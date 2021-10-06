open Base

let expect_type code ty =
  Mu.Infer.resetid ();
  let prog = Mu.parse_expr code in
  Caml.Format.printf "=== CODE ===@.%s@." (Mu.Expr.show_expr prog);
  let () =
    let assume name ty env = Map.set env ~key:name ~data:(Mu.parse_ty ty) in
    let env =
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
    "(b -> a, list[b]) -> list[a]";
  expect_type "fun x -> x.username" "{ username: a; b } -> a";
  expect_type "{ name = world }" "{ name: string;  }";
  expect_type "({ name = world }).name" "string";
  expect_type "({ name = world; age = age }).name" "string";
  expect_type "({ age = age; name = world }).name" "string";
  expect_type "fun user -> pair(user.name, user.age)"
    "{ name: a; age: b; c } -> pair[a, b]";
  expect_type "{ {name = world} with age = age }" "{ age: int; name: string;  }";
  expect_type "fun info -> { info with age = age }" "{ a } -> { age: int; a }";
  expect_type "fun info -> { info with age = age; age = world }"
    "{ a } -> { age: string; age: int; a }";
  expect_type
    {|
    let add_age = fun x -> { x with age = age } in
    add_age({ age = world })
    |}
    "{ age: int; age: string;  }";
  expect_type
    {|
    let add_age = fun x -> { x with age = age } in
    add_age({ age = age })
    |}
    "{ age: int; age: int;  }";
  expect_type "{ { num = age } with num := age }" "{ num: int;  }";
  expect_type "{ { num = world } with num := age }" "{ num: int;  }";
  expect_type
    {|
    let upd_age = fun x -> { x with age := age } in
    upd_age({ age = age })
    |}
    "{ age: int;  }";
  expect_type
    {|
    let upd_age = fun x -> { x with age := age } in
    upd_age({ age = world })
    |}
    "{ age: int;  }";
  (* test for recursive rowtype *)
  expect_type
    {|
	  fun r -> choose({r with x = zero}, {r with y = one})
    |}
    "";
  ()
