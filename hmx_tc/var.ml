open Base
open Syntax

type t = var

module Id = MakeId ()

let fresh ?(bound_lvl = 0) ?lvl () : var =
  let id = Id.fresh () in
  Union_find.make { ty = None; lvl; bound_lvl; id }

let reset = Id.reset

let bound_lvl v = (Union_find.value v).bound_lvl

let ty v = (Union_find.value v).ty

let set_ty ty v = (Union_find.value v).ty <- Some ty

let lvl var =
  let v = Union_find.value var in
  match v.lvl with
  | Some lvl -> lvl
  | None -> failwith (Printf.sprintf "%i has no lvl assigned" v.id)

let set_lvl lvl v = (Union_find.value v).lvl <- Some lvl

let equal = Union_find.equal

let show v =
  let data = Union_find.value v in
  match data.ty with
  | None -> Printf.sprintf "_%i" data.id
  | Some ty -> Ty.show ty

let merge_lvl lvl1 lvl2 =
  match (lvl1, lvl2) with
  | None, None
  | Some _, None
  | None, Some _ ->
    failwith "lvl is not assigned"
  | Some lvl1, Some lvl2 -> Some (min lvl1 lvl2)

(** [occurs_check_adjust_lvl var ty] checks that variable [var] is not
      contained within type [ty] and adjust levels of all unbound vars within
      the [ty]. *)
let occurs_check_adjust_lvl var =
  let rec occurs_check_ty ty' : unit =
    match ty' with
    | Ty_const _ -> ()
    | Ty_arr (args, ret) ->
      List.iter args ~f:occurs_check_ty;
      occurs_check_ty ret
    | Ty_app (f, args) ->
      occurs_check_ty f;
      List.iter args ~f:occurs_check_ty
    | Ty_var other_var -> (
      match ty other_var with
      | Some ty' -> occurs_check_ty ty'
      | None ->
        if equal other_var var then Type_error.raise Error_recursive_type
        else
          let data = Union_find.value var
          and odata = Union_find.value other_var in
          odata.lvl <- merge_lvl data.lvl odata.lvl)
  in
  occurs_check_ty

let unify var1 var2 =
  let merge v1 v2 =
    let v =
      match (v1.ty, v2.ty) with
      | Some _, Some _
      | Some _, None
      | None, None ->
        v1
      | None, Some _ -> v2
    in
    v.lvl <- merge_lvl v1.lvl v2.lvl;
    v
  in
  match (ty var1, ty var2) with
  | Some ty1, Some ty2 ->
    Union_find.union var1 var2 ~f:merge;
    Some (ty1, ty2)
  | Some ty1, None ->
    occurs_check_adjust_lvl var2 ty1;
    Union_find.union var1 var2 ~f:merge;
    None
  | None, Some ty2 ->
    occurs_check_adjust_lvl var1 ty2;
    Union_find.union var1 var2 ~f:merge;
    None
  | None, None ->
    Union_find.union var1 var2 ~f:merge;
    None
