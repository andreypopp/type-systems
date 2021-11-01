open Import
open Syntax

type t =
  | Error_unification of ty * ty
  | Error_recursive_type
  | Error_invalid_type_constructor_application of Path.t
  | Error_unknown_value of Path.t
  | Error_unknown_type of Path.t
  | Error_unknown_module of Path.t
  | Error_unknown_module_type of Path.t

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
      | Error_invalid_type_constructor_application p ->
        string "invalid application of type constructor: " ^^ Path.layout p
      | Error_unknown_value p -> string "unknown value: " ^^ Path.layout p
      | Error_unknown_type p -> string "unknown type: " ^^ Path.layout p
      | Error_unknown_module p -> string "unknown module: " ^^ Path.layout p
      | Error_unknown_module_type p ->
        string "unknown module type: " ^^ Path.layout p
  end) :
    SHOWABLE with type t := t)

exception Type_error of t

let raise error = raise (Type_error error)
