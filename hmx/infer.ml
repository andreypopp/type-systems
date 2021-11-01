open! Base
open Syntax

let refresh_ty ty =
  let vs = Hashtbl.create (module Var) in
  let rec aux ty =
    match ty with
    | Ty_name _ -> ty
    | Ty_abstract _ -> ty
    | Ty_var v -> Ty.var (Hashtbl.find_or_add vs v ~default:Var.fresh)
    | Ty_app (name, args) -> Ty_app (name, List.map args ~f:aux)
    | Ty_arr (args, r) -> Ty_arr (List.map args ~f:aux, aux r)
  in
  let ty = aux ty in
  let vs = Hashtbl.to_alist vs |> List.map ~f:snd in
  (vs, ty)

(** Constraints generation. *)
let rec generate : expr -> ty -> expr Constraint.t =
 fun e ty ->
  match e with
  | E_lit (Lit_int _) ->
    Constraint.(ty =~ Ty_abstract (Path.make "int") >>| fun () -> e)
  | E_lit (Lit_string _) ->
    Constraint.(ty =~ Ty_abstract (Path.make "string") >>| fun () -> e)
  | E_var p -> Constraint.inst p ty
  | E_app (f, args) ->
    let vs, arg_tys, args =
      List.fold args ~init:([], [], []) ~f:(fun (vs, arg_tys, args) arg ->
          let v = Var.fresh () in
          let arg_ty = Ty.var v in
          let arg = generate arg arg_ty in
          (v :: vs, arg_ty :: arg_tys, arg :: args))
    in
    let f_ty = Ty.(arr (List.rev arg_tys) ty) in
    let f = generate f f_ty in
    let args = Constraint.list (List.rev args) in
    Constraint.(exists vs (f &~ args) >>| fun (f, args) -> E_app (f, args))
  | E_abs (args, b) ->
    let vs, bindings, atys =
      List.fold args ~init:([], [], []) ~f:(fun (vs, bindings, atys) param ->
          let v = Var.fresh () in
          let ty = Ty.var v in
          ( v :: vs,
            (param, [], Constraint.return (E_var (Path.make param)), ty)
            :: bindings,
            Ty.var v :: atys ))
    in
    let v = Var.fresh () in
    let b = generate b (Ty.var v) in
    let ty' = Ty.arr (List.rev atys) (Ty.var v) in
    Constraint.(
      exists (v :: vs) (let_in (List.rev bindings) b &~ (ty' =~ ty))
      >>| fun ((_tys, b), ()) -> E_abs (args, b))
  | E_let ((name, e, a_ty), b) -> (
    let v = Var.fresh () in
    let e_ty = Ty.var v in
    let e = generate e e_ty in
    let e =
      match a_ty with
      | None -> e
      | Some ([], a_ty) ->
        let vs, a_ty = refresh_ty a_ty in
        Constraint.(e &~ exists vs (e_ty =~ a_ty) >>| fst)
      | Some (_vs, _) -> failwith "TODO: handle ascribed polymorphic types"
    in
    let b = generate b ty in
    Constraint.(
      let_in [ (name, [ v ], e, e_ty) ] b >>| fun (tys, b) ->
      match tys with
      | [ (e, ty_sch) ] -> E_let ((name, e, Some ty_sch), b)
      | _ -> failwith "impossible as we are supplying a single binding"))

module Env = struct
  type t = {
    values : (name, ty_sch def, String.comparator_witness) Map.t;
    types : (name, ty_sch def, String.comparator_witness) Map.t;
    modules : (name, mod_env def, String.comparator_witness) Map.t;
    module_types : (name, mod_env def, String.comparator_witness) Map.t;
  }

  and 'v def = { name : name; value : 'v }

  and mod_env = { mod_sign : t; mod_subst : Ident_subst.t }

  let empty =
    {
      types = Map.empty (module String);
      values = Map.empty (module String);
      modules = Map.empty (module String);
      module_types = Map.empty (module String);
    }

  let resolve_module_and ~lookup ~subst env p =
    let module_env p env name =
      match Map.find env.modules name with
      | None -> Type_error.raise (Error_unknown_module p)
      | Some def -> def.value.mod_sign
    in
    let rec module_path_env env p =
      match p with
      | Path.Path_ident name -> module_env p env name
      | Path.Path_project (p, name) ->
        let env' = module_path_env env p in
        module_env (Path.project p name) env' name
    in
    match p with
    | Path.Path_ident name -> lookup env name
    | Path.Path_project (p, name) ->
      let env' = module_path_env env p in
      let v = lookup env' name in
      let v = subst p v in
      v

  let resolve_module env p =
    let lookup env name =
      match Map.find env.modules name with
      | None -> Type_error.raise (Error_unknown_module p)
      | Some def -> def
    in
    let subst _p v = v in
    resolve_module_and ~lookup ~subst env p

  let resolve_module_type env p =
    let lookup env name =
      match Map.find env.module_types name with
      | None -> Type_error.raise (Error_unknown_module_type p)
      | Some def -> def.value
    in
    let subst _p v = v in
    resolve_module_and ~lookup ~subst env p

  let resolve_value env p =
    let lookup env name =
      match Map.find env.values name with
      | None -> Type_error.raise (Error_unknown_value p)
      | Some def -> def
    in
    let subst _p v = v in
    resolve_module_and ~lookup ~subst env p

  let resolve_type env p =
    let lookup env name =
      match Map.find env.types name with
      | None -> Type_error.raise (Error_unknown_type p)
      | Some def -> def
    in
    let subst _p v = v in
    resolve_module_and ~lookup ~subst env p

  let add_val env name ty_sch =
    if Debug.log_define then
      Caml.Format.printf "val %s : %s@." name (Ty_sch.show ty_sch);
    {
      env with
      values = Map.set env.values ~key:name ~data:{ name; value = ty_sch };
    }

  let add_type env name ty =
    { env with types = Map.set env.types ~key:name ~data:{ name; value = ty } }

  let add_module env name mod_env =
    {
      env with
      modules = Map.set env.modules ~key:name ~data:{ name; value = mod_env };
    }

  let add_module_type env name mty =
    {
      env with
      module_types =
        Map.set env.module_types ~key:name ~data:{ name; value = mty };
    }
end

(** A substitution over [ty] terms. *)
module Subst : sig
  type t

  val empty : t

  val make : (var * ty) list -> t

  val apply_ty : t -> ty -> ty
end = struct
  type t = (var * ty) list

  let empty = []

  let make pairs = pairs

  let find subst var =
    match List.Assoc.find ~equal:Var.equal subst var with
    | Some ty -> Some ty
    | None -> None

  let rec apply_ty subst ty =
    if List.is_empty subst then ty
    else
      match ty with
      | Ty_name _ -> ty
      | Ty_abstract _ -> ty
      | Ty_app (name, args) -> Ty_app (name, List.map args ~f:(apply_ty subst))
      | Ty_arr (args, b) ->
        Ty_arr (List.map args ~f:(apply_ty subst), apply_ty subst b)
      | Ty_var v -> (
        match Var.ty v with
        | Some ty -> apply_ty subst ty
        | None -> (
          match find subst v with
          | Some ty -> ty
          | None -> ty))
end

(* [unify ty1 ty2] unifies two types [ty1] and [ty2]. *)
let rec unify ~env ty1 ty2 =
  if Debug.log_unify then
    Caml.Format.printf "UNIFY %s ~ %s@." (Ty.show ty1) (Ty.show ty2);
  if phys_equal ty1 ty2 then ()
  else
    match (ty1, ty2) with
    | Ty_name name, ty
    | ty, Ty_name name ->
      let ty' = (Env.resolve_type env name).Env.value in
      let ty' =
        match ty' with
        | [], ty' -> ty'
        | _, _ ->
          Type_error.raise (Error_invalid_type_constructor_application name)
      in
      unify ~env ty ty'
    | Ty_abstract a, Ty_abstract b ->
      if not (Path.equal a b) then
        Type_error.raise (Error_unification (ty1, ty2))
    | Ty_app (Ty_abstract name1, args1), Ty_app (Ty_abstract name2, args2) -> (
      if not (Path.equal name1 name2) then
        Type_error.raise (Error_unification (ty1, ty2));
      match List.iter2 args1 args2 ~f:(unify ~env) with
      | Unequal_lengths -> Type_error.raise (Error_unification (ty1, ty2))
      | Ok () -> ())
    | Ty_app (Ty_name name, args), ty
    | ty, Ty_app (Ty_name name, args) ->
      let ty' = expand_ty_app ~env name args in
      unify ~env ty ty'
    | Ty_arr (a1, b1), Ty_arr (a2, b2) -> (
      match List.iter2 a1 a2 ~f:(unify ~env) with
      | Unequal_lengths -> Type_error.raise (Error_unification (ty1, ty2))
      | Ok () -> unify ~env b1 b2)
    | Ty_var var1, Ty_var var2 -> (
      match Var.unify var1 var2 with
      | Some (ty1, ty2) -> unify ~env ty1 ty2
      | None -> ())
    | Ty_var var, ty
    | ty, Ty_var var -> (
      match Var.ty var with
      | None ->
        Var.occurs_check_adjust_lvl var ty;
        Var.set_ty ty var
      | Some ty' -> unify ~env ty' ty)
    | _, _ -> Type_error.raise (Error_unification (ty1, ty2))

and expand_ty_app ~env name args =
  let vs, ty = (Env.resolve_type env name).value in
  let subst =
    match List.zip vs args with
    | Unequal_lengths ->
      Type_error.raise (Error_invalid_type_constructor_application name)
    | Ok s -> Subst.make s
  in
  match Subst.apply_ty subst ty with
  | Ty_abstract _ -> Ty_app (ty, args)
  | ty -> ty

(** An applicative structure which is used to build a computation which
    elaborates terms. *)
module Elab : sig
  type 'a t

  val run : 'a t -> 'a
  (** Compute a value.

      This should be run at the very end, when all holes are elaborated. *)

  val return : 'a -> 'a t

  val map : 'a t -> ('a -> 'b) -> 'b t

  val both : 'a t -> 'b t -> ('a * 'b) t

  val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t

  val ( and+ ) : 'a t -> 'b t -> ('a * 'b) t

  val list : 'a t list -> 'a list t
end = struct
  type 'a t = unit -> 'a

  let run elab = elab ()

  let return v () = v

  let map v f () = f (v ())

  let both a b () = (a (), b ())

  let ( let+ ) = map

  let ( and+ ) = both

  let list es () = List.map es ~f:run
end

(** Instantiate type scheme into a constrained type. *)
let instantiate ~lvl (ty_sch : ty_sch) : ty =
  match ty_sch with
  | [], ty ->
    (* No ∀-quantified variables, return the type as-is *)
    ty
  | vars, cty ->
    let subst =
      Subst.make (List.map vars ~f:(fun v -> (v, Ty.var (Var.fresh ~lvl ()))))
    in
    Subst.apply_ty subst cty

let instantiate ~lvl ty_sch =
  if Debug.log_instantiate then Ty_sch.print ~label:"I<" ty_sch;
  let cty = instantiate ~lvl ty_sch in
  if Debug.log_instantiate then Ty.print ~label:"I>" cty;
  cty

let simple_vs vs =
  let rec simple_vs vs' = function
    | [] -> vs'
    | v :: vs ->
      if Option.is_some (Var.ty v) then
        (* Skipping as the var is already bound. *)
        simple_vs vs' vs
      else if List.mem ~equal:Var.equal vs v then
        (* Skipping as the var is duplicated within [vs]. *)
        simple_vs vs' vs
      else simple_vs (v :: vs') vs
  in
  simple_vs [] vs

let ty_vs ~lvl ty =
  let rec aux vs = function
    | Ty_name _ -> vs
    | Ty_abstract _ -> vs
    | Ty_app (_name, args) -> List.fold args ~init:vs ~f:aux
    | Ty_arr (args, b) ->
      let vs = aux vs b in
      List.fold args ~init:vs ~f:aux
    | Ty_var v -> (
      match Var.ty v with
      | Some ty -> aux vs ty
      | None -> if Var.lvl v > lvl then v :: vs else vs)
  in
  aux [] ty

let generalize ~lvl ty =
  let gvs = simple_vs (ty_vs ~lvl ty) in
  (simple_vs gvs, ty)

let generalize ~lvl ty =
  let ty_sch = generalize ~lvl ty in
  if Debug.log_generalize then Ty_sch.print ~label:"G>" ty_sch;
  ty_sch

let rec solve : type a. lvl:lvl -> env:Env.t -> a Constraint.t -> a Elab.t =
 fun ~lvl ~env c ->
  match c with
  | C_trivial -> Elab.return ()
  | C_eq (a, b) ->
    unify ~env a b;
    Elab.return ()
  | C_map (c, f) ->
    let v = solve ~lvl ~env c in
    Elab.map v f
  | C_and (a, b) ->
    let a = solve ~lvl ~env a in
    let b = solve ~lvl ~env b in
    Elab.both a b
  | C_and_list cs ->
    let vs =
      List.fold cs ~init:[] ~f:(fun vs c ->
          let v = solve ~lvl ~env c in
          v :: vs)
    in
    Elab.(
      let+ vs = list vs in
      List.rev vs)
  | C_exists (vs, c) ->
    List.iter vs ~f:(Var.set_lvl lvl);
    solve ~lvl ~env c
  | C_let (bindings, c) ->
    let env, values =
      let env0 = env in
      List.fold bindings ~init:(env, [])
        ~f:(fun (env, values) (name, vs, c, ty) ->
          (* Need to set levels here as [C_let] works as [C_exists] as well. *)
          List.iter vs ~f:(Var.set_lvl (lvl + 1));
          let e, ty_sch = solve_and_generalize ~lvl:(lvl + 1) ~env:env0 c ty in
          let env = Env.add_val env name ty_sch in
          (env, e :: values))
    in
    let v = solve ~lvl ~env c in
    let values = Elab.list (List.rev values) in
    Elab.(both values v)
  | C_inst (name, ty) ->
    let ty_sch = (Env.resolve_value env name).value in
    let ty' = instantiate ~lvl ty_sch in
    unify ~env ty ty';
    Elab.return (E_var name)

and solve_and_generalize ~lvl ~env c ty =
  let e = solve ~lvl ~env c in
  let ty_sch = generalize ~lvl:(lvl - 1) ty in
  let e =
    Elab.(
      let+ e = e in
      (e, ty_sch))
  in
  (e, ty_sch)

let infer_expr ~env e =
  let e, _ty_sch =
    (* To infer an expression type we first generate constraints *)
    let v = Var.fresh () in
    let ty = Ty.var v in
    let c = generate e ty in
    let c = Constraint.exists [ v ] c in
    (* and then solve them and generaralize!. *)
    solve_and_generalize ~lvl:1 ~env c ty
  in
  Elab.run e

let rec subst_mod_env name { Env.mod_sign; mod_subst } =
  let subst_mod_env_def def =
    { def with Env.value = subst_mod_env name def.Env.value }
  in
  let subst_def =
    let mod_subst' = Ident_subst.prefix_image name mod_subst in
    fun subst def -> { def with Env.value = subst mod_subst' def.Env.value }
  in
  let mod_subst = Ident_subst.prefix name mod_subst in
  let mod_sign =
    {
      Env.values =
        Map.map mod_sign.Env.values ~f:(subst_def Ident_subst.subst_ty_sch);
      types = Map.map mod_sign.types ~f:(subst_def Ident_subst.subst_ty_sch);
      modules = Map.map mod_sign.Env.modules ~f:subst_mod_env_def;
      module_types = Map.map mod_sign.module_types ~f:subst_mod_env_def;
    }
  in
  { Env.mod_sign; mod_subst }

let rec infer_mstr ~env str =
  let str, sign, subst, _env =
    List.fold str ~init:([], Env.empty, Ident_subst.empty, env)
      ~f:(fun (str, sign, subst, env) item ->
        match item with
        | Mstr_val (name, ty_sch, e) ->
          let e, ty_sch =
            let e = E_let ((name, e, ty_sch), E_var (Path.make name)) in
            let e, ty_sch = infer_expr ~env e in
            match e with
            | E_let ((_, e, _), _) -> (e, ty_sch)
            | _ -> assert false
          in
          ( Mstr_val (name, Some ty_sch, e) :: str,
            Env.add_val sign name ty_sch,
            subst,
            Env.add_val env name ty_sch )
        | Mstr_ty (name, (Ty_decl_alias ty_sch as ty_decl)) ->
          ( Mstr_ty (name, ty_decl) :: str,
            Env.add_type sign name ty_sch,
            subst,
            Env.add_type env name ty_sch )
        | Mstr_ty (name, (Ty_decl_abstract arity as ty_decl)) ->
          let ty_sch =
            let vs = List.init arity ~f:(fun _ -> Var.fresh ()) in
            (vs, Ty_abstract (Path.make name))
          in
          ( Mstr_ty (name, ty_decl) :: str,
            Env.add_type sign name ty_sch,
            Ident_subst.add subst name (Path.make name),
            Env.add_type env name ty_sch )
        | Mstr_mexpr (name, me) ->
          let me, mod_env = infer_mexpr ~env me in
          let mod_env = subst_mod_env (Path.make name) mod_env in
          ( Mstr_mexpr (name, me) :: str,
            Env.add_module sign name mod_env,
            Ident_subst.merge subst mod_env.mod_subst,
            Env.add_module env name mod_env )
        | Mstr_mty (name, mty) ->
          let msign = infer_mty ~env mty in
          ( Mstr_mty (name, mty) :: str,
            Env.add_module_type sign name msign,
            subst,
            Env.add_module_type env name msign ))
  in
  (List.rev str, { Env.mod_sign = sign; mod_subst = subst })

and infer_mexpr ~env me =
  match me with
  | M_path mpath ->
    let mod_env = (Env.resolve_module env mpath).value in
    (M_path mpath, mod_env)
  | M_str mstr ->
    let mstr', mod_env' = infer_mstr ~env mstr in
    (M_str mstr', mod_env')
  | M_constr (me, mty) ->
    let me', mod_env' = infer_mexpr ~env me in
    let mod_env'' = infer_mty ~env mty in
    check_subtype mod_env''.Env.mod_sign mod_env'.Env.mod_sign;
    (M_constr (me', mty), mod_env'')

and infer_mty ~env mty =
  match mty with
  | Mty_sig msig -> infer_msig ~env msig
  | Mty_path mpath -> Env.resolve_module_type env mpath

and infer_msig ~env items =
  let _env, mod_sign, mod_subst =
    List.fold items ~init:(env, Env.empty, Ident_subst.empty)
      ~f:(fun (env, sign, subst) item ->
        match item with
        | Msig_val (name, ty_sch) ->
          (Env.add_val env name ty_sch, Env.add_val sign name ty_sch, subst)
        | Msig_ty (name, Ty_decl_alias ty_sch) ->
          (Env.add_type env name ty_sch, Env.add_type sign name ty_sch, subst)
        | Msig_ty (name, Ty_decl_abstract arity) ->
          let ty_sch =
            let vs = List.init arity ~f:(fun _ -> Var.fresh ()) in
            (vs, Ty_abstract (Path.make name))
          in
          ( Env.add_type env name ty_sch,
            Env.add_type sign name ty_sch,
            Ident_subst.add subst name (Path.make name) )
        | Msig_mexpr (name, mty) ->
          let mod_env = infer_mty ~env mty in
          ( Env.add_module env name mod_env,
            Env.add_module sign name mod_env,
            subst )
        | Msig_mty (name, mty) ->
          let mod_env = infer_mty ~env mty in
          ( Env.add_module_type env name mod_env,
            Env.add_module_type sign name mod_env,
            subst ))
  in
  { Env.mod_sign; mod_subst }

and check_subtype _supertype _subtype = (* TODO *) ()
