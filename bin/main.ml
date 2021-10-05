open Base

let expect_type code ty =
  Mu.Infer.resetid ();
  let prog = Mu.parse_expr code in
  Caml.Format.printf "=== CODE ===@.%s@." (Mu.Expr.show_expr prog);
  let () =
    let assume name ty env = Map.set env ~key:name ~data:(Mu.parse_ty ty) in
    let env =
      Map.empty (module String)
      |> assume "world" "string"
      |> assume "print" "string -> string"
      |> assume "nil" "forall[a] list[a]"
      |> assume "cons" "forall[a] (a, list[a]) -> list[a]"
      |> assume "head" "forall[a] list[a] -> a"
      |> assume "tail" "forall[a] list[a] -> list[a]"
    in
    try
      let inferred_ty = Mu.Infer.infer env prog in
      Caml.Format.printf ": %s@." (Mu.Expr.show_ty inferred_ty);
      if not String.(Mu.Expr.show_ty inferred_ty = ty) then (
        Caml.print_endline ("ERROR: " ^ Mu.Expr.show_ty inferred_ty);
        Caml.exit 1)
    with
    | Mu.Infer.Type_error msg -> Caml.print_endline msg
  in
  ()

let () =
  expect_type "world" "string";
  expect_type "print" "string -> string";
  expect_type "let x = world in x" "string";
  expect_type "fun () -> world" "() -> string";
  expect_type "let x = fun () -> world in world" "string";
  expect_type "let x = fun () -> world in x" "() -> string";
  expect_type "print(world)" "string";
  expect_type "let hello = fun msg -> print(msg) in hello(world)" "string";
  expect_type "fun x -> let y = fun z -> z in y" "b -> a -> a";
  expect_type "fun x -> let y = x in y" "a -> a";
  expect_type "fun x -> let y = fun z -> x in y" "a -> b -> a";
  expect_type "let rec fact = fun n -> fact(print(n)) in fact(world)" "a";
  expect_type
    "let rec map = fun (f, xs) -> cons(f(head(xs)), map(f, tail(xs))) in map"
    "(b -> a,list(b)) -> list(a)";
  ()
