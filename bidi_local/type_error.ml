open Import
open Syntax

type t =
  | Error_not_a_subtype of {
      sub_loc : Location.t;
      sub_ty : ty;
      super_loc : Location.t;
      super_ty : ty;
    }
  | Error_not_equal of ty * ty
  | Error_recursive_type
  | Error_recursive_record_type
  | Error_unknown_name of { name : Location.t * name }
  | Error_missing_type_annotation of { expr : expr }
  | Error_expected_a_function of { loc : Location.t; ty : ty }
  | Error_arity_mismatch of { loc : Location.t }

(* let layout = *)
(*   let open Layout in *)
(*   function *)
(*   | Error_not_a_subtype (ty1, ty2) -> *)
(*     let* ty1 = Ty.layout ty1 in *)
(*     let* ty2 = Ty.layout ty2 in *)
(*     return *)
(*       (group *)
(*          (string "type" *)
(*          ^^ nest 2 (break 1 ^^ ty1) *)
(*          ^^ break 1 *)
(*          ^^ string "is not a subtype of" *)
(*          ^^ nest 2 (break 1 ^^ ty2))) *)
(*   | Error_not_equal (ty1, ty2) -> *)
(*     let* ty1 = Ty.layout ty1 in *)
(*     let* ty2 = Ty.layout ty2 in *)
(*     return *)
(*       (group *)
(*          (string "type" *)
(*          ^^ nest 2 (break 1 ^^ ty1) *)
(*          ^^ break 1 *)
(*          ^^ string "is not equal to" *)
(*          ^^ nest 2 (break 1 ^^ ty2))) *)
(*   | Error_recursive_type -> return (string "recursive type") *)
(*   | Error_recursive_record_type -> return (string "recursive record type") *)
(*   | Error_unknown_name name -> return (string "unknown name: " ^^ string name) *)
(*   | Error_missing_type_annotation expr -> *)
(*     let loc, _ = expr in *)
(*     let err = Location.error ~loc "missing type annotation" in *)
(*     let* expr = Expr.layout expr in *)
(*     Caml.Format.printf "ERROR: %a@." Location.print_report err; *)
(*     return (string "missing type annotation: " ^^ expr) *)
(*   | Error_expected_a_function ty -> *)
(*     let* ty = Ty.layout ty in *)
(*     return (string "expected a function but got: " ^^ ty) *)
(*   | Error_expected_a_record ty -> *)
(*     let* ty = Ty.layout ty in *)
(*     return (string "expected a record but got: " ^^ ty) *)
(*   | Error_arity_mismatch -> return (string "arity mismatch") *)

let to_report = function
  | Error_not_a_subtype info ->
    let doc =
      let open Layout in
      let* sub_ty = Ty.layout info.sub_ty in
      let* super_ty = Ty.layout info.super_ty in
      return
        (group
           (string "type"
           ^^ nest 2 (break 1 ^^ bold sub_ty)
           ^^ break 1
           ^^ string "is not a subtype of"
           ^^ nest 2 (break 1 ^^ bold super_ty)))
    in
    Location.error ~loc:info.sub_loc (Layout.to_string doc)
  | Error_not_equal _ -> Location.error "types are not equal"
  | Error_recursive_type -> Location.error "recursive type"
  | Error_recursive_record_type -> Location.error "recursive record type"
  | Error_unknown_name { name = loc, name } ->
    Location.errorf ~loc "'%s' is not defined" name
  | Error_missing_type_annotation { expr = loc, _ } ->
    Location.error ~loc "missing type annotation"
  | Error_expected_a_function { loc; ty = _ty } ->
    Location.error ~loc "expected a function"
  | Error_arity_mismatch { loc } -> Location.error ~loc "arity mismatch"

(* include ( *)
(*   Showable (struct *)
(*     type nonrec t = t *)

(*     let layout v = Layout.render (layout v) *)
(*   end) : *)
(*     SHOWABLE with type t := t) *)

exception Type_error of t

let raise error = raise (Type_error error)

let raise_not_a_subtype
    ?(sub_loc = Location.none) ?(super_loc = Location.none) ~sub_ty ~super_ty ()
    =
  raise (Error_not_a_subtype { sub_loc; sub_ty; super_loc; super_ty })
