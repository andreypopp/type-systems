open! Base
open Syntax

(** Constraints generation. *)
let rec generate e ty : con =
  match e with
  | E_lit (Lit_int _) -> C.(ty =~ Ty_const "int")
  | E_lit (Lit_string _) -> C.(ty =~ Ty_const "string")
  | E_var name -> C.inst name ty
  | E_app (f, args) ->
    let vs, atys, cs =
      List.fold args ~init:([], [], C.trivial) ~f:(fun (vs, atys, cs) arg ->
          let v = C.fresh_var () in
          (v :: vs, Ty.var v :: atys, C.(cs &~ generate arg (Ty.var v))))
    in
    C.(exists vs (generate f Ty.(arr (List.rev atys) ty) &~ cs))
  | E_abs (args, b) ->
    let vs, bindings, atys =
      List.fold args ~init:([], [], []) ~f:(fun (vs, bindings, atys) arg ->
          let v = C.fresh_var () in
          let ty_sch = ([], (C.trivial, Ty.var v)) in
          (v :: vs, (arg, ty_sch) :: bindings, Ty.var v :: atys))
    in
    let v = C.fresh_var () in
    C.(
      exists (v :: vs)
        (let_in (List.rev bindings) (generate b (Ty.var v))
        &~ (Ty.arr (List.rev atys) (Ty.var v) =~ ty)))
  | E_let (name, e, b) ->
    let v = C.fresh_var () in
    C.(
      let_in
        [ (name, ([ v ], (generate e (Ty.var v), Ty.var v))) ]
        (generate b ty))

module Error = struct
  type t =
    | Error_unification of ty * ty
    | Error_recursive_type
    | Error_unknown_name of string
  [@@deriving sexp_of]

  include Showable (struct
    type nonrec t = t

    let sexp_of_t = sexp_of_t

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
  end)
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
let instantiate lvl (ty_sch : ty_sch) =
  match ty_sch with
  | [], cty ->
    (* No ∀-quantified variables, return constrained type as-is *)
    cty
  | vars, cty ->
    let vars =
      (* Allocate a fresh var for each ∀-quantified var. *)
      (* NOTE: That this now depends on ty_sch be simplified with [simpl]. *)
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
    and instantiate_con c =
      match c with
      | C_trivial -> c
      | C_eq (a, b) -> C_eq (instantiate_ty a, instantiate_ty b)
      | C_and cs -> C_and (List.map cs ~f:instantiate_con)
      | C_exists (vs, c) ->
        let vs =
          List.map vs ~f:(fun v ->
              match List.Assoc.find ~equal:Var.equal vars v with
              | Some v -> v
              | None -> v)
        in
        C_exists (vs, instantiate_con c)
      | C_let (bindings, c) ->
        let bindings =
          List.map bindings ~f:(fun (name, (vs, cty)) ->
              (name, (vs, instantiate_cty cty)))
        in
        C_let (bindings, instantiate_con c)
      | C_inst (name, ty) -> C_inst (name, instantiate_ty ty)
    and instantiate_cty (c, ty) = (instantiate_con c, instantiate_ty ty) in
    instantiate_cty cty

let instantiate lvl ty_sch =
  if Debug.log_instantiate then
    Caml.Format.printf "INST< %i %s@." lvl (Ty_sch.show ty_sch);
  let cty = instantiate lvl ty_sch in
  if Debug.log_instantiate then
    Caml.Format.printf "INST> %i %s@." lvl (Cty.show cty);
  cty

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

let simpl ty_sch =
  let vs, cty = ty_sch in
  (simpl_vars vs, cty)

let generalize lvl (cty : cty) : ty_sch =
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
  let c, ty = cty in
  let vs' = vars [] ty in
  simpl (vs', (c, ty))

let generalize lvl cty =
  if Debug.log_generalize then
    Caml.Format.printf "GEN<  %i %s@." lvl (Cty.show cty);
  let ty_sch = generalize lvl cty in
  if Debug.log_generalize then
    Caml.Format.printf "GEN>  %i %s@." lvl (Ty_sch.show ty_sch);
  ty_sch

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

let rec solve lvl env c =
  if Debug.log_solve then Caml.Format.printf "SOLVE %s@." (C.show c);
  match c with
  | C_trivial -> C_trivial
  | C_eq (a, b) ->
    unify a b;
    C_trivial
  | C_and cs -> (
    let cs =
      List.fold cs ~init:[] ~f:(fun cs c ->
          match solve lvl env c with
          | C_trivial -> cs
          | c -> c :: cs)
    in
    match cs with
    | [] -> C_trivial
    | cs -> C_and cs)
  | C_exists (vs, c) -> (
    List.iter vs ~f:(Var.set_level lvl);
    match solve lvl env c with
    | C_trivial -> C_trivial
    | C_exists (vs', c) -> C_exists (simpl_vars (vs @ vs'), c)
    | c -> C_exists (simpl_vars vs, c))
  | C_let (bindings, c) ->
    let env =
      List.fold bindings ~init:env ~f:(fun env (name, ty_sch) ->
          let vs, (c', ty) = ty_sch in
          List.iter vs ~f:(Var.set_level (lvl + 1));
          let c' = solve (lvl + 1) env c' in
          let ty_sch = generalize lvl (c', ty) in
          Env.add env name ty_sch)
    in
    solve lvl env c
  | C_inst (name, ty) ->
    let ty_sch =
      match Env.find env name with
      | Some ty_sch -> ty_sch
      | None -> type_error (Error_unknown_name name)
    in
    let c', ty' = instantiate lvl ty_sch in
    unify ty ty';
    solve lvl env c'

let infer ~env e =
  (* To infer an expression type we first generate constraints *)
  let v = C.fresh_var () in
  let c = C.exists [ v ] (generate e (Ty.var v)) in
  try
    (* and then solve them and generaralize!. *)
    let c = solve 0 env c in
    Ok (generalize (-1) (c, Ty.var v))
  with
  | Type_error error -> Error error
