open Base

let test_run code =
  Mu.Infer.resetid ();
  let prog = Mu.parse_expr code in
  Caml.Format.printf "=== CODE ===@.%s@." (Mu.Expr.show_expr prog);
  let () =
    let assume name ty env = Map.set env ~key:name ~data:(Mu.parse_ty ty) in
    let env =
      Map.empty (module String)
      |> assume "world" "string"
      |> assume "print" "string -> string"
    in
    try
      let ty = Mu.Infer.infer env prog in
      Caml.Format.printf ": %s@." (Mu.Expr.show_ty ty)
    with
    | Mu.Infer.Type_error msg -> Caml.print_endline msg
  in
  ()

let () =
  test_run "world";
  test_run "print";
  test_run "let x = world in x";
  test_run "fun () -> world";
  test_run "let x = fun () -> world in world";
  test_run "let x = fun () -> world in x";
  test_run "print(world)";
  test_run "let hello = fun msg -> print(msg) in hello(world)";
  test_run "fun x -> let y = fun z -> z in y";

  (* XXX: UNSOUND NOW DUE TO GENERALIZATION *)
  test_run "fun x -> let y = x in y";

  (* XXX: UNSOUND NOW DUE TO GENERALIZATION *)
  test_run "fun x -> let y = fun z -> x in y"
