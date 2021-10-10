open Base

let () =
  let env =
    let assume name ty env = Mu.Infer.Env.add env name (Mu.parse_ty ty) in
    let assume_typeclass qp env =
      let qp = Mu.parse_qual_pred qp in
      Mu.Infer.Env.add_typeclass env qp
    in
    let assume_instance qp witness env =
      let qp = Mu.parse_qual_pred qp in
      Mu.Infer.Env.add_instance env qp witness
    in
    Mu.Infer.Env.empty
    (* Show *)
    |> assume_typeclass "forall[a] Show(a)"
    |> assume "show" "forall[a] Show(a) => a -> string"
    |> assume "show_int" "int -> string"
    |> assume_instance "Show(int)" "show_int"
    |> assume "show_float" "float -> string"
    |> assume_instance "Show(float)" "show_float"
    (* Read *)
    |> assume_typeclass "forall[a] Read(a)"
    |> assume "read" "forall[a] Read(a) => string -> a"
    |> assume "read_int" "string -> int"
    |> assume_instance "Read(int)" "read_int"
    |> assume "read_float" "string -> float"
    |> assume_instance "Read(float)" "read_float"
    (* Eq *)
    |> assume_typeclass "forall[a] Eq(a)"
    |> assume "eq" "forall[a] Eq(a) => (a, a) -> bool"
    |> assume "eq_bool" "(bool, bool) -> bool"
    |> assume_instance "Eq(bool)" "eq_bool"
    |> assume "eq_int" "(int, int) -> bool"
    |> assume_instance "Eq(int)" "eq_int"
    |> assume "eq_list" "forall[a] Eq(a) => (list[a], list[a]) -> bool"
    |> assume_instance "forall[a] Eq(a) => Eq(list[a])" "eq_list"
    |> assume "eq_pair"
         "forall[a, b] Eq(a), Eq(b) => (pair[a, b], list[a, b]) -> bool"
    |> assume_instance "forall[a, b] Eq(a), Eq(b) => Eq(pair[a, b])" "eq_pair"
    (* Ord *)
    |> assume_typeclass "forall[a] Eq(a) => Ord(a)"
    |> assume "compare" "forall[a] Ord(a) => (a, a) -> int"
    |> assume "compare_bool" "(bool, bool) -> int"
    |> assume_instance "Ord(bool)" "compare_bool"
    |> assume "compare_int" "(int, int) -> int"
    |> assume_instance "Ord(int)" "compare_int"
    |> assume "compare_list" "forall[a] Ord(a) => (list[a], list[a]) -> int"
    |> assume_instance "forall[a] Ord(a) => Ord(list[a])" "compare_list"
    |> assume "compare_pair"
         "forall[a, b] Ord(a), Ord(b) => (pair[a, b], list[a, b]) -> int"
    |> assume_instance "forall[a, b] Ord(a), Ord(b) => Ord(pair[a, b])"
         "compare_pair"
    (* Lists *)
    |> assume "head" "forall[a] list[a] -> a"
    |> assume "tail" "forall[a] list[a] -> list[a]"
    |> assume "nil" "forall[a] list[a]"
    |> assume "cons" "forall[a] (a, list[a]) -> list[a]"
    |> assume "cons_curry" "forall[a] a -> list[a] -> list[a]"
    |> assume "map" "forall[a, b] (a -> b, list[a]) -> list[b]"
    |> assume "map_curry" "forall[a, b] (a -> b) -> list[a] -> list[b]"
    |> assume "fix" "forall [a] (a -> a) -> a"
    |> assume "one" "int"
    |> assume "zero" "int"
    |> assume "succ" "int -> int"
    |> assume "plus" "(int, int) -> int"
    |> assume "eq_curry" "forall[a] a -> a -> bool"
    |> assume "not" "bool -> bool"
    |> assume "true" "bool"
    |> assume "false" "bool"
    |> assume "pair" "forall[a, b] (a, b) -> pair[a, b]"
    |> assume "pair_curry" "forall[a, b] a -> b -> pair[a, b]"
    |> assume "first" "forall[a, b] pair[a, b] -> a"
    |> assume "second" "forall[a, b] pair[a, b] -> b"
    |> assume "id" "forall[a] a -> a"
    |> assume "const" "forall[a, b] a -> b -> a"
    |> assume "apply" "forall[a, b] (a -> b, a) -> b"
    |> assume "apply_curry" "forall[a, b] (a -> b) -> a -> b"
    |> assume "choose" "forall[a] (a, a) -> a"
    |> assume "choose_curry" "forall[a] a -> a -> a"
    |> assume "age" "int"
    |> assume "world" "string"
    |> assume "print" "string -> string"
    |> assume "print_user" "(string,age) -> string"
  in
  let prog = Mu.Expr_parser.parse_chan Stdio.stdin in
  match Mu.infer_ty ~env prog with
  | Ok qty -> Caml.Format.printf ": %s@." (Mu.Expr.show_qual_ty qty)
  | Error err ->
    Caml.Format.printf "ERROR: %s@." (Mu.Infer.show_error err);
    Caml.exit 1
