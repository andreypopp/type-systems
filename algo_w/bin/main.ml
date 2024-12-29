open Base

let () =
  let env =
    let assume name ty env =
      Algo_w.Infer.Env.add env name (Algo_w.parse_ty ty)
    in
    let assume_typeclass qp env =
      let qp = Algo_w.parse_qual_pred qp in
      Algo_w.Infer.Env.add_typeclass env qp
    in
    let assume_instance qp witness env =
      let qp = Algo_w.parse_qual_pred qp in
      Algo_w.Infer.Env.add_instance env qp witness
    in
    Algo_w.Infer.Env.empty
    (* Show *)
    |> assume_typeclass "a . Show(a)"
    |> assume "show" "a . Show(a) => a -> string"
    |> assume "show_int" "int -> string"
    |> assume_instance "Show(int)" "show_int"
    |> assume "show_float" "float -> string"
    |> assume_instance "Show(float)" "show_float"
    (* Read *)
    |> assume_typeclass "a . Read(a)"
    |> assume "read" "a . Read(a) => string -> a"
    |> assume "read_int" "string -> int"
    |> assume_instance "Read(int)" "read_int"
    |> assume "read_float" "string -> float"
    |> assume_instance "Read(float)" "read_float"
    (* Eq *)
    |> assume_typeclass "a . Eq(a)"
    |> assume "eq" "a . Eq(a) => (a, a) -> bool"
    |> assume "eq_bool" "(bool, bool) -> bool"
    |> assume_instance "Eq(bool)" "eq_bool"
    |> assume "eq_int" "(int, int) -> bool"
    |> assume_instance "Eq(int)" "eq_int"
    |> assume "eq_list" "a . Eq(a) => (list[a], list[a]) -> bool"
    |> assume_instance "a . Eq(a) => Eq(list[a])" "eq_list"
    |> assume "eq_pair" "a, b . Eq(a), Eq(b) => (pair[a, b], list[a, b]) -> bool"
    |> assume_instance "a, b . Eq(a), Eq(b) => Eq(pair[a, b])" "eq_pair"
    (* Ord *)
    |> assume_typeclass "a . Eq(a) => Ord(a)"
    |> assume "compare" "a . Ord(a) => (a, a) -> int"
    |> assume "compare_bool" "(bool, bool) -> int"
    |> assume_instance "Ord(bool)" "compare_bool"
    |> assume "compare_int" "(int, int) -> int"
    |> assume_instance "Ord(int)" "compare_int"
    |> assume "compare_list" "a . Ord(a) => (list[a], list[a]) -> int"
    |> assume_instance "a . Ord(a) => Ord(list[a])" "compare_list"
    |> assume "compare_pair"
         "a, b . Ord(a), Ord(b) => (pair[a, b], list[a, b]) -> int"
    |> assume_instance "a, b . Ord(a), Ord(b) => Ord(pair[a, b])" "compare_pair"
    (* Lists *)
    |> assume "head" "a . list[a] -> a"
    |> assume "tail" "a . list[a] -> list[a]"
    |> assume "nil" "a . list[a]"
    |> assume "cons" "a . (a, list[a]) -> list[a]"
    |> assume "cons_curry" "a . a -> list[a] -> list[a]"
    |> assume "map" "a, b . (a -> b, list[a]) -> list[b]"
    |> assume "map_curry" "a, b . (a -> b) -> list[a] -> list[b]"
    |> assume "fix" "a . (a -> a) -> a"
    |> assume "one" "int"
    |> assume "zero" "int"
    |> assume "succ" "int -> int"
    |> assume "plus" "(int, int) -> int"
    |> assume "eq_curry" "a . a -> a -> bool"
    |> assume "not" "bool -> bool"
    |> assume "true" "bool"
    |> assume "false" "bool"
    |> assume "pair" "a, b . (a, b) -> pair[a, b]"
    |> assume "pair_curry" "a, b . a -> b -> pair[a, b]"
    |> assume "first" "a, b . pair[a, b] -> a"
    |> assume "second" "a, b . pair[a, b] -> b"
    |> assume "id" "a . a -> a"
    |> assume "const" "a, b . a -> b -> a"
    |> assume "apply" "a, b . (a -> b, a) -> b"
    |> assume "apply_curry" "a, b . (a -> b) -> a -> b"
    |> assume "choose" "a . (a, a) -> a"
    |> assume "choose_curry" "a . a -> a -> a"
    |> assume "age" "int"
    |> assume "world" "string"
    |> assume "print" "string -> string"
    |> assume "print_user" "(string,age) -> string"
  in
  let prog = Algo_w.Expr_parser.parse_chan Stdio.stdin in
  match Algo_w.infer_ty ~env prog with
  | Ok qty -> Stdlib.Format.printf ": %s@." (Algo_w.Expr.show_qual_ty qty)
  | Error err ->
    Stdlib.Format.printf "ERROR: %s@." (Algo_w.Infer.show_error err);
    Stdlib.exit 1
