open! Base
open Syntax

(** Constraints generation. *)
let rec generate : expr -> ty -> expr C.t =
 fun e ty ->
  match e with
  | E_lit (Lit_int _) -> C.(ty =~ Ty_const "int" >>| fun () -> e)
  | E_lit (Lit_string _) -> C.(ty =~ Ty_const "string" >>| fun () -> e)
  | E_var name -> C.(inst name ty >>| fun _ty -> e)
  | E_app (f, args) ->
    let vs, arg_tys, args =
      List.fold args ~init:([], [], []) ~f:(fun (vs, arg_tys, args) arg ->
          let v = C.fresh_var () in
          let arg_ty = Ty.var v in
          let arg = generate arg arg_ty in
          (v :: vs, arg_ty :: arg_tys, arg :: args))
    in
    let f_ty = Ty.(arr (List.rev arg_tys) ty) in
    let f = generate f f_ty in
    let args = C.list (List.rev args) in
    C.(exists vs (f &~ args) >>| fun (f, args) -> E_app (f, args))
  | E_abs (args, b) ->
    let vs, bindings, atys =
      List.fold args ~init:([], [], []) ~f:(fun (vs, bindings, atys) arg ->
          let v = C.fresh_var () in
          let ty = Ty.var v in
          (v :: vs, (arg, [], C.trivial, ty) :: bindings, Ty.var v :: atys))
    in
    let v = C.fresh_var () in
    let b = generate b (Ty.var v) in
    let ty' = Ty.arr (List.rev atys) (Ty.var v) in
    C.(
      exists (v :: vs) (let_in (List.rev bindings) b &~ (ty' =~ ty))
      >>| fun ((_tys, b), ()) -> E_abs (args, b))
  | E_let ((name, e, _), b) -> (
    let v = C.fresh_var () in
    let e_ty = Ty.var v in
    let e = generate e e_ty in
    let b = generate b ty in
    C.(
      let_in [ (name, [ v ], e, e_ty) ] b >>| fun (tys, b) ->
      match tys with
      | [ (e, ty_sch) ] -> E_let ((name, e, Some ty_sch), b)
      | _ -> failwith "impossible as we are supplying a single binding"))

module Error = struct
  type t =
    | Error_unification of ty * ty
    | Error_recursive_type
    | Error_unknown_name of string

  include (
    Showable (struct
      type nonrec t = t

      let layout =
        let open PPrint in
        function
        | Error_unification (ty1, ty2) ->
          string "incompatible types:"
          ^^ nest 2 (break 1 ^^ Ty.layout ty1)
          ^^ break 1
          ^^ string "and"
          ^^ nest 2 (break 1 ^^ Ty.layout ty2)
        | Error_recursive_type -> string "recursive type"
        | Error_unknown_name name -> string "unknown name: " ^^ string name
    end) :
      SHOWABLE with type t := t)
end

exception Type_error of Error.t

let type_error error = raise (Type_error error)

let merge_lvl lvl1 lvl2 =
  match (lvl1, lvl2) with
  | None, None
  | Some _, None
  | None, Some _ ->
    failwith "lvl is not assigned"
  | Some lvl1, Some lvl2 -> Some (min lvl1 lvl2)

module Var = struct
  type t = var

  let set_level lvl v = (Union_find.value v).lvl <- Some lvl

  let merge_level v ov =
    let data = Union_find.value v
    and odata = Union_find.value ov in
    data.lvl <- merge_lvl data.lvl odata.lvl

  let bound v = (Union_find.value v).ty

  let lvl var =
    let v = Union_find.value var in
    match v.lvl with
    | Some lvl -> lvl
    | None -> failwith (Printf.sprintf "%i has no lvl assigned" v.id)

  let equal = Union_find.equal

  (** [occurs_check_adjust_lvl var ty] checks that variable [var] is not
      contained within type [ty] and adjust levels of all unbound vars within
      the [ty]. *)
  let occurs_check_adjust_lvl var ty =
    let rec occurs_check_ty (ty : ty) : unit =
      match ty with
      | Ty_const _ -> ()
      | Ty_arr (args, ret) ->
        List.iter args ~f:occurs_check_ty;
        occurs_check_ty ret
      | Ty_app (f, args) ->
        occurs_check_ty f;
        List.iter args ~f:occurs_check_ty
      | Ty_var other_var -> (
        match bound other_var with
        | Some ty -> occurs_check_ty ty
        | None ->
          if equal other_var var then type_error Error_recursive_type
          else merge_level other_var var)
    in
    occurs_check_ty ty

  let unify unify_ty var1 var2 =
    match (bound var1, bound var2) with
    | Some ty1, Some ty2 ->
      Union_find.union var1 var2 ~f:(fun data1 data2 ->
          data1.lvl <- merge_lvl data1.lvl data2.lvl;
          data1);
      unify_ty ty1 ty2
    | Some ty1, None ->
      occurs_check_adjust_lvl var2 ty1;
      Union_find.union var1 var2 ~f:(fun data1 data2 ->
          data1.lvl <- merge_lvl data1.lvl data2.lvl;
          data1)
    | None, Some ty2 ->
      occurs_check_adjust_lvl var1 ty2;
      Union_find.union var1 var2 ~f:(fun data1 data2 ->
          data2.lvl <- merge_lvl data1.lvl data2.lvl;
          data2)
    | None, None ->
      Union_find.union var1 var2 ~f:(fun data1 data2 ->
          data1.lvl <- merge_lvl data1.lvl data2.lvl;
          data1)

  let bind unify_ty var ty =
    let data = Union_find.value var in
    match data.ty with
    | None ->
      occurs_check_adjust_lvl var ty;
      data.ty <- Some ty
    | Some ty' -> unify_ty ty' ty
end

let rec unify ty1 ty2 =
  if Debug.log_unify then
    Caml.Format.printf "UNIFY %s ~ %s@." (Ty.show ty1) (Ty.show ty2);
  if phys_equal ty1 ty2 then ()
  else
    match (ty1, ty2) with
    | Ty_const a, Ty_const b ->
      if not String.(a = b) then type_error (Error_unification (ty1, ty2))
    | Ty_app (a1, b1), Ty_app (a2, b2) -> (
      unify a1 a2;
      match List.iter2 b1 b2 ~f:unify with
      | Unequal_lengths -> type_error (Error_unification (ty1, ty2))
      | Ok () -> ())
    | Ty_arr (a1, b1), Ty_arr (a2, b2) -> (
      match List.iter2 a1 a2 ~f:unify with
      | Unequal_lengths -> type_error (Error_unification (ty1, ty2))
      | Ok () -> unify b1 b2)
    | Ty_var var1, Ty_var var2 -> Var.unify unify var1 var2
    | Ty_var var, ty
    | ty, Ty_var var ->
      Var.bind unify var ty
    | _, _ -> type_error (Error_unification (ty1, ty2))

(** Instantiate type scheme into a constrained type. *)
let instantiate lvl ty_sch =
  match ty_sch with
  | [], ty ->
    (* No ∀-quantified variables, return the type as-is *)
    ty
  | vars, ty ->
    let vars =
      (* Allocate a fresh var for each ∀-quantified var. *)
      (* NOTE: That this now depends on ty_sch be simplified with [simpl] before
         generalization. *)
      List.map vars ~f:(fun v -> (v, C.fresh_var ~lvl ()))
    in
    let rec instantiate_ty ty =
      match ty with
      | Ty_const _ -> ty
      | Ty_app (a, args) ->
        Ty_app (instantiate_ty a, List.map args ~f:instantiate_ty)
      | Ty_arr (args, b) ->
        Ty_arr (List.map args ~f:instantiate_ty, instantiate_ty b)
      | Ty_var v -> (
        match Var.bound v with
        | Some ty -> instantiate_ty ty
        | None -> (
          match List.Assoc.find ~equal:Var.equal vars v with
          | Some v -> Ty.var v
          | None -> ty))
    in
    instantiate_ty ty

let simpl (vs, ty) =
  let simpl_vars vs =
    let rec simpl_vars vs' = function
      | [] -> vs'
      | v :: vs ->
        if Option.is_some (Var.bound v) then
          (* Skipping as the var is already bound. *)
          simpl_vars vs' vs
        else if List.mem ~equal:Var.equal vs v then
          (* Skipping as the var is duplicated within [vs]. *)
          simpl_vars vs' vs
        else simpl_vars (v :: vs') vs
    in
    simpl_vars [] vs
  in
  (simpl_vars vs, ty)

let generalize lvl ty =
  let rec vars vs = function
    | Ty_const _ -> vs
    | Ty_app (a, args) ->
      let vs = vars vs a in
      List.fold args ~init:vs ~f:vars
    | Ty_arr (args, b) ->
      let vs = vars vs b in
      List.fold args ~init:vs ~f:vars
    | Ty_var v -> (
      match Var.bound v with
      | Some ty -> vars vs ty
      | None -> if Var.lvl v > lvl then v :: vs else vs)
  in
  let vs' = vars [] ty in
  simpl (vs', ty)

module Env : sig
  type t

  val empty : t

  val find : t -> name -> ty_sch option

  val add : t -> name -> ty_sch -> t
end = struct
  type t = (name, ty_sch, String.comparator_witness) Map.t

  let empty = Map.empty (module String)

  let find env name = Map.find env name

  let add env name ty_sch = Map.set env ~key:name ~data:ty_sch
end

let rec solve : type a. lvl -> Env.t -> a C.t -> a =
 fun lvl env c ->
  match c with
  | C_trivial -> ()
  | C_eq (a, b) -> unify a b
  | C_map (c, f) -> f (solve lvl env c)
  | C_and (a, b) ->
    let a = solve lvl env a in
    let b = solve lvl env b in
    (a, b)
  | C_and_list cs -> List.map cs ~f:(solve lvl env)
  | C_exists (vs, c) ->
    List.iter vs ~f:(Var.set_level lvl);
    solve lvl env c
  | C_let (bindings, c) ->
    let env, values =
      List.fold bindings ~init:(env, [])
        ~f:(fun (env, values) (name, vs, c, ty) ->
          List.iter vs ~f:(Var.set_level (lvl + 1));
          let e = solve (lvl + 1) env c in
          let ty_sch = generalize lvl ty in
          let env = Env.add env name ty_sch in
          (env, (e, ty_sch) :: values))
    in
    (List.rev values, solve lvl env c)
  | C_inst (name, ty) ->
    let ty_sch =
      match Env.find env name with
      | Some ty_sch -> ty_sch
      | None -> type_error (Error_unknown_name name)
    in
    let ty' = instantiate lvl ty_sch in
    unify ty ty';
    ty'

(** [infer ~env e] infers the type scheme for expression [e].

    It returns either an [Ok (ty_sch, elaborated)] where [ty_sch] is the type
    scheme inferred and [elaborated] is an elaborated expression corresponding
    to [e].

    ... or in case of an error it returns [Error err].
    *)
let infer ~env e : (expr, Error.t) Result.t =
  (* To infer an expression type we first generate constraints *)
  let v = C.fresh_var () in
  let c = generate e (Ty.var v) in
  let c = C.exists [ v ] c in
  try
    (* and then solve them and generaralize!. *)
    let e = solve 0 env c in
    let ty_sch = generalize (-1) (Ty.var v) in
    Ok (E_let (("_", e, Some ty_sch), E_var "_"))
  with
  | Type_error error -> Error error
