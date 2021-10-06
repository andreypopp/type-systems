open Base

let env =
  let assume name ty env = Map.set env ~key:name ~data:(Mu.parse_ty ty) in
  Mu.empty_env
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

let infer code =
  Mu.Infer.resetid ();
  let prog = Mu.parse_expr code in
  Caml.Format.printf "%s@." (Mu.Expr.show_expr prog);
  match Mu.infer_ty ~env prog with
  | Ok ty -> Caml.Format.printf ": %s@.|" (Mu.Expr.show_ty ty)
  | Error err -> Caml.Format.printf "ERROR: %s@.|" (Mu.Infer.show_error err)

let%expect_test "" =
  infer "world";
  [%expect {|
    world
    : string
    | |}]

let%expect_test "" =
  infer "print";
  [%expect {|
    print
    : string -> string
    | |}]

let%expect_test "" =
  infer "let x = world in x";
  [%expect {|
    let x = world in x
    : string
    | |}]

let%expect_test "" =
  infer "fun () -> world";
  [%expect {|
    fun () -> world
    : () -> string
    | |}]

let%expect_test "" =
  infer "let x = fun () -> world in world";
  [%expect {|
    let x = fun () -> world in world
    : string
    | |}]

let%expect_test "" =
  infer "let x = fun () -> world in x";
  [%expect {|
    let x = fun () -> world in x
    : () -> string
    | |}]

let%expect_test "" =
  infer "print(world)";
  [%expect {|
    print(world)
    : string
    | |}]

let%expect_test "" =
  infer "let hello = fun msg -> print(msg) in hello(world)";
  [%expect
    {|
    let hello = fun msg -> print(msg) in hello(world)
    : string
    | |}]

let%expect_test "" =
  infer "fun x -> let y = fun z -> z in y";
  [%expect {|
    fun x -> let y = fun z -> z in y
    : b -> a -> a
    | |}]

let%expect_test "" =
  infer "fun x -> let y = x in y";
  [%expect {|
    fun x -> let y = x in y
    : a -> a
    | |}]

let%expect_test "" =
  infer "fun x -> let y = fun z -> x in y";
  [%expect {|
    fun x -> let y = fun z -> x in y
    : a -> b -> a
    | |}]

let%expect_test "" =
  infer "let rec fact = fun n -> fact(print(n)) in fact(world)";
  [%expect
    {|
    let rec fact = fun n -> fact(print(n)) in fact(world)
    : a
    | |}]

let%expect_test "" =
  infer
    "let rec map = fun (f, xs) -> cons(f(head(xs)), map(f, tail(xs))) in map";
  [%expect
    {|
    let rec map = fun (f, xs) -> cons(f(head(xs)), map(f, tail(xs))) in map
    : (b -> a, list[b]) -> list[a]
    | |}]

let%expect_test "" =
  infer "fun x -> x.username";
  [%expect {|
    fun x -> x.username
    : { username: a; b } -> a
    | |}]

let%expect_test "" =
  infer "{ name = world }";
  [%expect {|
    { name = world }
    : { name: string;  }
    | |}]

let%expect_test "" =
  infer "({ name = world }).name";
  [%expect {|
    ({ name = world }).name
    : string
    | |}]

let%expect_test "" =
  infer "({ name = world; age = age }).name";
  [%expect {|
    ({ name = world; age = age }).name
    : string
    | |}]

let%expect_test "" =
  infer "({ age = age; name = world }).name";
  [%expect {|
    ({ age = age; name = world }).name
    : string
    | |}]

let%expect_test "" =
  infer "fun user -> pair(user.name, user.age)";
  [%expect
    {|
    fun user -> pair(user.name, user.age)
    : { name: a; age: b; c } -> pair[a, b]
    | |}]

let%expect_test "" =
  infer "fun user -> {name = user.name; age = user.age}";
  [%expect
    {|
    fun user -> { name = user.name; age = user.age }
    : { name: a; age: b; c } -> { age: b; name: a;  }
    | |}]

let%expect_test "" =
  infer "{ {name = world} with age = age }";
  [%expect
    {|
    { { name = world } with age = age }
    : { age: int; name: string;  }
    | |}]

let%expect_test "" =
  infer "fun info -> { info with age = age }";
  [%expect
    {|
    fun info -> { info with age = age }
    : { a } -> { age: int; a }
    | |}]

let%expect_test "" =
  infer "fun info -> { info with age = age; age = world }";
  [%expect
    {|
    fun info -> { info with age = age; age = world }
    : { a } -> { age: string; age: int; a }
    | |}]

let%expect_test "" =
  infer
    {|
  let add_age = fun x -> { x with age = age } in
  add_age
  |};
  [%expect
    {|
    let add_age = fun x -> { x with age = age } in add_age
    : { a } -> { age: int; a }
    | |}]

let%expect_test "" =
  infer
    {|
  let add_age = fun x -> { x with age = age } in
  add_age({ age = world })
  |};
  [%expect
    {|
    let add_age = fun x -> { x with age = age } in add_age({ age = world })
    : { age: int; age: string;  }
    | |}]

let%expect_test "" =
  infer
    {|
  let add_age = fun x -> { x with age = age } in
  add_age({ age = age })
  |};
  [%expect
    {|
    let add_age = fun x -> { x with age = age } in add_age({ age = age })
    : { age: int; age: int;  }
    | |}]

let%expect_test "" =
  infer "{ { } with num := age }";
  [%expect
    {|
    { {  } with num := age }
    ERROR: unification error of
      { num: _2; _1 }
    with
      {  }
    | |}]

let%expect_test "" =
  infer "{ { num = age } with num := age }";
  [%expect
    {|
    { { num = age } with num := age }
    : { num: int;  }
    | |}]

let%expect_test "" =
  infer "{ { num = world } with num := age }";
  [%expect
    {|
    { { num = world } with num := age }
    ERROR: unification error of
      string
    with
      int
    | |}]

let%expect_test "" =
  infer
    {|
  let upd_age = fun x -> { x with age := age } in
  upd_age
  |};
  [%expect
    {|
    let upd_age = fun x -> { x with age := age } in upd_age
    : { age: int; a } -> { age: int; a }
    | |}]

let%expect_test "" =
  infer
    {|
  let upd_age = fun x -> { x with age := age } in
  upd_age({ age = age })
  |};
  [%expect
    {|
    let upd_age = fun x -> { x with age := age } in upd_age({ age = age })
    : { age: int;  }
    | |}]

let%expect_test "" =
  infer
    {|
  let upd_age = fun x -> { x with age := age } in
  upd_age({ age = world })
  |};
  [%expect
    {|
    let upd_age = fun x -> { x with age := age } in upd_age({ age = world })
    ERROR: unification error of
      string
    with
      int
    | |}]

(* test for recursive rowtype *)
let%expect_test "" =
  infer {|
  fun r -> choose({r with x = zero}, {r with y = one})
  |};
  [%expect
    {|
    fun r -> choose({ r with x = zero }, { r with y = one })
    ERROR: recursive row types
    | |}]
