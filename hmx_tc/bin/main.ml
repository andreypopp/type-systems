open Base
open Hmx_tc

let () =
  let env =
    Env.empty
    |> Env.assume_val "one" "int"
    |> Env.assume_val "hello" "string"
    |> Env.assume_val "world" "string"
    |> Env.assume_val "pair" "a, b . (a, b) -> pair[a, b]"
    |> Env.assume_val "triple" "a, b, c . (a, b, c) -> triple[a, b, c]"
    |> Env.assume_val "quadruple"
         "a, b, c, e . (a, b, c, e) -> quadruple[a, b, c, e]"
    |> Env.assume_val "plus" "(int, int) -> int"
    |> Env.assume_val "true" "bool"
    |> Env.assume_val "nil" "a . list[a]"
    |> Env.assume_val "cons" "a . (a, list[a]) -> list[a]"
    (* eq *)
    |> Env.assume_tclass "eq" "a . (a, a) -> bool"
    |> Env.assume_tclass_instance "eq_int" "eq[int]"
    |> Env.assume_tclass_instance "eq_bool" "eq[bool]"
    |> Env.assume_tclass_instance "eq_list" "a . eq[a] => eq[list[a]]"
    |> Env.assume_tclass_instance "eq_pair"
         "a, b . eq[a], eq[b] => eq[pair[a, b]]"
    (* compare[a] *)
    |> Env.assume_tclass "compare" "a . eq[a] => (a, a) -> bool"
    |> Env.assume_tclass_instance "compare_list"
         "a . compare[a] => compare[list[a]]"
    |> Env.assume_tclass_instance "compare_int" "compare[int]"
    |> Env.assume_tclass_instance "compare_bool" "compare[bool]"
    (* coerce[a, b] *)
    |> Env.assume_tclass "coerce" "a, b . a -> b"
    |> Env.assume_tclass_instance "coerce_id" "a . coerce[a, a]"
    |> Env.assume_tclass_instance "coerce_list"
         "a, b . coerce[a, b] => coerce[list[a], list[b]]"
    |> Env.assume_tclass_instance "coerce_bool_int" "coerce[bool, int]"
    (* show *)
    |> Env.assume_tclass "show" "a . a -> string"
    |> Env.assume_tclass_instance "show_int" "show[int]"
    |> Env.assume_tclass_instance "show_float" "show[float]"
    (* (1* read *1) *)
    |> Env.assume_tclass "read" "a . string -> a"
    |> Env.assume_tclass_instance "read_int" "read[int]"
    |> Env.assume_tclass_instance "read_float" "read[float]"
    (* |> Env.assume_tclass "eq2" "a . (a, a) -> bool" *)
    (* |> Env.assume_tclass_instance "eq2_int" "eq2[int]" *)
    (* |> Env.assume_tclass_instance "eq2_list" "a . eq2[a] => eq2[list[a]]" *)
    (* |> Env.assume_val "ch" "a . compare[a], eq2[a] => (a, a) -> bool" *)
  in
  let e = Expr.parse_chan Stdio.stdin in
  match infer ~env e with
  | Ok e -> Caml.Format.printf "%s@." (Expr.show e)
  | Error err -> Caml.Format.printf "ERROR: %s@." (Type_error.show err)
