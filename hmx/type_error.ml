open Base
open Syntax

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

exception Type_error of t

let raise error = raise (Type_error error)
