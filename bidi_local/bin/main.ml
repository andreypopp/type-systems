open Base
open Bidi_local

let () =
  let () = if Unix.isatty Unix.stdout then enable_colors true in
  let env =
    Env.empty
    |> Env.assume_val "id" "a . a -> a"
    |> Env.assume_val "null" "a . a?"
    |> Env.assume_val "one" "int"
    |> Env.assume_val "succ" "int -> int"
    |> Env.assume_val "nil" "a . list[a]"
    |> Env.assume_val "cons" "a . (a, list[a]) -> list[a]"
    |> Env.assume_val "map" "a, b . (a -> b, list[a]) -> list[b]"
    |> Env.assume_val "choose" "a . (a, a) -> a"
    |> Env.assume_val "choose3" "a . (a, a, a) -> a"
    |> Env.assume_val "choose4" "a . (a, a, a, a) -> a"
    |> Env.assume_val "hello" "string"
    |> Env.assume_val "pair" "a, b . (a, b) -> pair[a, b]"
    |> Env.assume_val "plus" "(int, int) -> int"
    |> Env.assume_val "true" "bool"
    |> Env.assume_val "ifnull" "a . (a?, a) -> a"
    |> Env.assume_val "eq" "a . (a, a) -> bool"
  in
  let s = Stdio.In_channel.input_all Stdio.stdin in
  let e = Expr.parse_string (String.strip s) in
  match infer ~env e with
  | Ok e -> Caml.Format.printf "%s@." (Expr.show e)
  | Error err ->
    let report = Type_error.to_report err in
    Caml.Format.printf "%a@." Location.print_report report
