open Import
open Syntax

type t =
  | Error_not_a_subtype of ty * ty
  | Error_not_equal of ty * ty
  | Error_recursive_type
  | Error_unknown_name of string
  | Error_missing_type_annotation of expr
  | Error_expected_a_function of ty
  | Error_arity_mismatch

let layout =
  let open Layout in
  function
  | Error_not_a_subtype (ty1, ty2) ->
    let* ty1 = Ty.layout ty1 in
    let* ty2 = Ty.layout ty2 in
    return
      (group
         (string "type"
         ^^ nest 2 (break 1 ^^ ty1)
         ^^ break 1
         ^^ string "is not a subtype of"
         ^^ nest 2 (break 1 ^^ ty2)))
  | Error_not_equal (ty1, ty2) ->
    let* ty1 = Ty.layout ty1 in
    let* ty2 = Ty.layout ty2 in
    return
      (group
         (string "type"
         ^^ nest 2 (break 1 ^^ ty1)
         ^^ break 1
         ^^ string "is not equal to"
         ^^ nest 2 (break 1 ^^ ty2)))
  | Error_recursive_type -> return (string "recursive type")
  | Error_unknown_name name -> return (string "unknown name: " ^^ string name)
  | Error_missing_type_annotation expr ->
    let* expr = Expr.layout expr in
    return (string "missing type annotation: " ^^ expr)
  | Error_expected_a_function ty ->
    let* ty = Ty.layout ty in
    return (string "expected a function but got: " ^^ ty)
  | Error_arity_mismatch -> return (string "arity mismatch")

include (
  Showable (struct
    type nonrec t = t

    let layout v = Layout.render (layout v)
  end) :
    SHOWABLE with type t := t)

exception Type_error of t

let raise error = raise (Type_error error)

let raise_not_a_subtype ~sub_ty ~super_ty =
  raise (Error_not_a_subtype (sub_ty, super_ty))
