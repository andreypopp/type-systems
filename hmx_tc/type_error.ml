open Base
open Syntax

type t =
  | Error_unification of ty * ty
  | Error_recursive_type
  | Error_unknown_name of string
  | Error_ambigious_tclass_application of bound
  | Error_no_tclass_instance of ty
  | Error_unknown_tclass of name

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
      | Error_ambigious_tclass_application (B_class (name, tys)) ->
        string "ambigious typeclass application: "
        ^^ Ty.layout (Ty_app (Ty_const name, tys))
      | Error_unknown_tclass name -> string "unknown typeclass: " ^^ string name
      | Error_no_tclass_instance ty ->
        string "no typeclass instance found: " ^^ Ty.layout ty
  end) :
    SHOWABLE with type t := t)

exception Type_error of t

let raise error = raise (Type_error error)
