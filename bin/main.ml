open Base

let () =
  let env =
    let assume name ty env = Map.set env ~key:name ~data:(Mu.parse_ty ty) in
    Map.empty (module String)
    |> assume "choose" "forall[a] (a, a) -> a"
    |> assume "zero" "int"
    |> assume "one" "int"
    |> assume "age" "int"
    |> assume "world" "string"
    |> assume "print" "string -> string"
    |> assume "print_user" "(string,age) -> string"
    |> assume "nil" "forall[a] list[a]"
    |> assume "cons" "forall[a] (a, list[a]) -> list[a]"
    |> assume "head" "forall[a] list[a] -> a"
    |> assume "tail" "forall[a] list[a] -> list[a]"
    |> assume "pair" "forall[a b] (a, b) -> pair[a, b]"
    |> assume "fst" "forall[a b] pair[a, b] -> a"
    |> assume "snd" "forall[a b] pair[a, b] -> b"
  in
  let prog = Mu.Expr_parser.parse_chan Stdio.stdin in
  match Mu.infer_ty ~env prog with
  | Ok ty -> Caml.Format.printf ": %s@." (Mu.Expr.show_ty ty)
  | Error err ->
    Caml.Format.printf "ERROR: %s@." (Mu.Infer.show_error err);
    Caml.exit 1
