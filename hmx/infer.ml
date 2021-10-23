open! Base
open Syntax

(** Constraints generation. *)
let rec generate : expr -> ty -> expr Constraint.t =
 fun e ty ->
  match e with
  | E_lit (Lit_int _) -> Constraint.(ty =~ Ty_const "int" >>| fun () -> e)
  | E_lit (Lit_string _) -> Constraint.(ty =~ Ty_const "string" >>| fun () -> e)
  | E_var name -> Constraint.inst name ty
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
            (param, [], Constraint.return (E_var param), ty) :: bindings,
            Ty.var v :: atys ))
    in
    let v = Var.fresh () in
    let b = generate b (Ty.var v) in
    let ty' = Ty.arr (List.rev atys) (Ty.var v) in
    Constraint.(
      exists (v :: vs) (let_in (List.rev bindings) b &~ (ty' =~ ty))
      >>| fun ((_tys, b), ()) -> E_abs (args, b))
  | E_let ((name, e, _), b) -> (
    let v = Var.fresh () in
    let e_ty = Ty.var v in
    let e = generate e e_ty in
    let b = generate b ty in
    Constraint.(
      let_in [ (name, [ v ], e, e_ty) ] b >>| fun (tys, b) ->
      match tys with
      | [ (e, ty_sch) ] -> E_let ((name, e, Some ty_sch), b)
      | _ -> failwith "impossible as we are supplying a single binding"))

(* [unify ty1 ty2] unifies two types [ty1] and [ty2]. *)
let rec unify ty1 ty2 =
  if Debug.log_unify then
    Caml.Format.printf "UNIFY %s ~ %s@." (Ty.show ty1) (Ty.show ty2);
  if phys_equal ty1 ty2 then ()
  else
    match (ty1, ty2) with
    | Ty_const a, Ty_const b ->
      if not String.(a = b) then Type_error.raise (Error_unification (ty1, ty2))
    | Ty_app (a1, b1), Ty_app (a2, b2) -> (
      unify a1 a2;
      match List.iter2 b1 b2 ~f:unify with
      | Unequal_lengths -> Type_error.raise (Error_unification (ty1, ty2))
      | Ok () -> ())
    | Ty_arr (a1, b1), Ty_arr (a2, b2) -> (
      match List.iter2 a1 a2 ~f:unify with
      | Unequal_lengths -> Type_error.raise (Error_unification (ty1, ty2))
      | Ok () -> unify b1 b2)
    | Ty_var var1, Ty_var var2 -> (
      match Var.unify var1 var2 with
      | Some (ty1, ty2) -> unify ty1 ty2
      | None -> ())
    | Ty_var var, ty
    | ty, Ty_var var -> (
      match Var.ty var with
      | None ->
        Var.occurs_check_adjust_lvl var ty;
        Var.set_ty ty var
      | Some ty' -> unify ty' ty)
    | _, _ -> Type_error.raise (Error_unification (ty1, ty2))

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
    match ty with
    | Ty_const _ -> ty
    | Ty_app (a, args) ->
      Ty_app (apply_ty subst a, List.map args ~f:(apply_ty subst))
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

module Env = struct
  type t = {
    values : (name, def, String.comparator_witness) Map.t;
    tclasses : (name, tclass, String.comparator_witness) Map.t;
  }

  and def = { name : name; ty_sch : ty_sch }

  and tclass = { def : def; method_def : def; instances : def list }

  let empty =
    { values = Map.empty (module String); tclasses = Map.empty (module String) }

  let find_val env name = Map.find env.values name

  let find_tclass env name = Map.find env.tclasses name

  let add_val env name ty_sch =
    if Debug.log_define then
      Caml.Format.printf "val %s : %s@." name (Ty_sch.show ty_sch);
    { env with values = Map.set env.values ~key:name ~data:{ name; ty_sch } }
end

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
    | Ty_const _ -> vs
    | Ty_app (a, args) ->
      let vs = aux vs a in
      List.fold args ~init:vs ~f:aux
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
    unify a b;
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
    let ty_sch =
      match Env.find_val env name with
      | Some def -> def.ty_sch
      | None -> Type_error.raise (Error_unknown_name name)
    in
    let ty' = instantiate ~lvl ty_sch in
    unify ty ty';
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

(** [infer ~env e] infers the type scheme for expression [e].

    It returns either an [Ok (ty_sch, elaborated)] where [ty_sch] is the type
    scheme inferred and [elaborated] is an elaborated expression corresponding
    to [e].

    ... or in case of an error it returns [Error err].
    *)
let infer ~env e : (expr, Type_error.t) Result.t =
  (* To infer an expression type we first generate constraints *)
  let v = Var.fresh () in
  let ty = Ty.var v in
  let c = generate e ty in
  let c = Constraint.exists [ v ] c in
  try
    (* and then solve them and generaralize!. *)
    let e, _ty_sch = solve_and_generalize ~lvl:1 ~env c ty in
    Ok
      Elab.(
        run
          (let+ e, ty_sch = e in
           E_let (("_", e, Some ty_sch), E_var "_")))
  with
  | Type_error.Type_error error -> Error error
