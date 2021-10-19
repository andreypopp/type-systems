open Base
open Hmx

let () =
  let env =
    Env.empty
    |> Env.assume_val "one" "int"
    |> Env.assume_val "hello" "string"
    |> Env.assume_val "pair" "a, b . (a, b) -> pair[a, b]"
    |> Env.assume_val "plus" "int -> int -> int"
    |> Env.assume_val "true" "bool"
    |> Env.assume_val "eq" "a . (a, a) -> bool"
  in
  let e = Expr.parse_chan Stdio.stdin in
  match infer ~env e with
  | Ok e -> Caml.Format.printf "%s@." (Expr.show e)
  | Error err -> Caml.Format.printf "ERROR: %s@." (Error.show err)
