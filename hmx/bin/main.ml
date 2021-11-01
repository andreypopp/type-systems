open! Base
open Hmx

let () =
  let env =
    Env.empty
    |> Env.assume_type "int" 0
    |> Env.assume_type "bool" 0
    |> Env.assume_type "string" 0
    |> Env.assume_type "list" 1
    |> Env.assume_type "pair" 2
    |> Env.assume_val "one" "int"
    |> Env.assume_val "hello" "string"
    |> Env.assume_val "pair" "a, b . (a, b) -> pair[a, b]"
    |> Env.assume_val "plus" "(int, int) -> int"
    |> Env.assume_val "true" "bool"
    |> Env.assume_val "eq" "a . (a, a) -> bool"
  in
  let s = Mstr.parse_chan Stdio.stdin in
  match infer_mstr ~env s with
  | Ok (s, _env) -> Caml.Format.printf "%s@." (Mstr.show s)
  | Error err -> Caml.Format.printf "ERROR: %s@." (Type_error.show err)
