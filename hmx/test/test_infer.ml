open Base
open Hmx

let env =
  Env.empty
  |> Env.assume_val "fix" "a . (a -> a) -> a"
  |> Env.assume_val "head" "a . list[a] -> a"
  |> Env.assume_val "tail" "a . list[a] -> list[a]"
  |> Env.assume_val "nil" "a . list[a]"
  |> Env.assume_val "cons" "a . (a, list[a]) -> list[a]"
  |> Env.assume_val "cons_curry" "a . a -> list[a] -> list[a]"
  |> Env.assume_val "map" "a, b . (a -> b, list[a]) -> list[b]"
  |> Env.assume_val "map_curry" "a, b . (a -> b) -> list[a] -> list[b]"
  |> Env.assume_val "one" "int"
  |> Env.assume_val "zero" "int"
  |> Env.assume_val "succ" "int -> int"
  |> Env.assume_val "plus" "(int, int) -> int"
  |> Env.assume_val "eq" "a . (a, a) -> bool"
  |> Env.assume_val "eq_curry" "a . a -> a -> bool"
  |> Env.assume_val "not" "bool -> bool"
  |> Env.assume_val "true" "bool"
  |> Env.assume_val "false" "bool"
  |> Env.assume_val "pair" "a, b . (a, b) -> pair[a, b]"
  |> Env.assume_val "pair_curry" "a, b . a -> b -> pair[a, b]"
  |> Env.assume_val "first" "a, b . pair[a, b] -> a"
  |> Env.assume_val "second" "a, b . pair[a, b] -> b"
  |> Env.assume_val "id" "a . a -> a"
  |> Env.assume_val "const" "a, b . a -> b -> a"
  |> Env.assume_val "apply" "a, b . (a -> b, a) -> b"
  |> Env.assume_val "apply_curry" "a, b . (a -> b) -> a -> b"
  |> Env.assume_val "choose" "a . (a, a) -> a"
  |> Env.assume_val "choose_curry" "a . a -> a -> a"
  |> Env.assume_val "age" "int"
  |> Env.assume_val "world" "string"
  |> Env.assume_val "print" "string -> string"

let infer ?(env = env) code =
  Id.reset ();
  let prog = Expr.parse_string code in
  Caml.Format.printf "%s@." (Expr.show prog);
  match infer ~env prog with
  | Ok ty_sch -> Caml.Format.printf ": %s@.|" (Ty_sch.show ty_sch)
  | Error err -> Caml.Format.printf "ERROR: %s@.|" (Error.show err)

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
  [%expect
    {|
    fun x -> let y = fun z -> z in y
    : a, b . b -> a -> a
    | |}]

let%expect_test "" =
  infer "fun x -> let y = x in y";
  [%expect {|
    fun x -> let y = x in y
    : a . a -> a
    | |}]

let%expect_test "" =
  infer "fun x -> let y = fun z -> x in y";
  [%expect
    {|
    fun x -> let y = fun z -> x in y
    : a, b . a -> b -> a
    | |}]

let%expect_test "" =
  infer "id";
  [%expect {|
    id
    : a . a -> a
    | |}]

let%expect_test "" =
  infer "one";
  [%expect {|
    one
    : int
    | |}]

let%expect_test "" =
  infer "x";
  [%expect {|
    x
    ERROR: unknown name: x
    | |}]

let%expect_test "" =
  infer "let x = x in x";
  [%expect {|
    let x = x in x
    ERROR: unknown name: x
    | |}]

let%expect_test "" =
  infer "let x = id in x";
  [%expect {|
    let x = id in x
    : a . a -> a
    | |}]

let%expect_test "" =
  infer "let x = fun y -> y in x";
  [%expect {|
    let x = fun y -> y in x
    : a . a -> a
    | |}]

let%expect_test "" =
  infer "fun x -> x";
  [%expect {|
    fun x -> x
    : a . a -> a
    | |}]

let%expect_test "" =
  infer "pair";
  [%expect {|
    pair
    : a, b . (a, b) -> pair[a, b]
    | |}]

let%expect_test "" =
  infer "fun x -> let y = fun z -> z in y";
  [%expect
    {|
    fun x -> let y = fun z -> z in y
    : a, b . b -> a -> a
    | |}]

let%expect_test "" =
  infer "let f = fun x -> x in let id = fun y -> y in eq(f, id)";
  [%expect
    {|
    let f = fun x -> x in let id = fun y -> y in eq(f, id)
    : bool
    | |}]

let%expect_test "" =
  infer "let f = fun x -> x in let id = fun y -> y in eq_curry(f)(id)";
  [%expect
    {|
    let f = fun x -> x in let id = fun y -> y in eq_curry(f)(id)
    : bool
    | |}]

let%expect_test "" =
  infer "let f = fun x -> x in eq(f, succ)";
  [%expect {|
    let f = fun x -> x in eq(f, succ)
    : bool
    | |}]

let%expect_test "" =
  infer "let f = fun x -> x in eq_curry(f)(succ)";
  [%expect {|
    let f = fun x -> x in eq_curry(f)(succ)
    : bool
    | |}]

let%expect_test "" =
  infer "let f = fun x -> x in pair(f(one), f(true))";
  [%expect
    {|
    let f = fun x -> x in pair(f(one), f(true))
    : pair[int, bool]
    | |}]

let%expect_test "" =
  infer "fun f -> pair(f(one), f(true))";
  [%expect
    {|
    fun f -> pair(f(one), f(true))
    ERROR: incompatible types:
      int
    and
      bool
    | |}]

let%expect_test "" =
  infer "let f = fun (x, y) -> let a = eq(x, y) in eq(x, y) in f";
  [%expect
    {|
    let f = fun (x, y) -> let a = eq(x, y) in eq(x, y) in f
    : a . (a, a) -> bool
    | |}]

let%expect_test "" =
  infer "let f = fun (x, y) -> let a = eq_curry(x)(y) in eq_curry(x)(y) in f";
  [%expect
    {|
    let f = fun (x, y) -> let a = eq_curry(x)(y) in eq_curry(x)(y) in f
    : a . (a, a) -> bool
    | |}]

let%expect_test "" =
  infer "id(id)";
  [%expect {|
    id(id)
    : a . a -> a
    | |}]

let%expect_test "" =
  infer "choose(fun (x, y) -> x, fun (x, y) -> y)";
  [%expect
    {|
    choose(fun (x, y) -> x, fun (x, y) -> y)
    : a . (a, a) -> a
    | |}]

let%expect_test "" =
  infer "choose_curry(fun (x, y) -> x)(fun (x, y) -> y)";
  [%expect
    {|
    choose_curry(fun (x, y) -> x)(fun (x, y) -> y)
    : a . (a, a) -> a
    | |}]

let%expect_test "" =
  infer "let x = id in let y = let z = x(id) in z in y";
  [%expect
    {|
    let x = id in let y = let z = x(id) in z in y
    : a . a -> a
    | |}]

let%expect_test "" =
  infer "cons(id, nil)";
  [%expect {|
    cons(id, nil)
    : a . list[a -> a]
    | |}]

let%expect_test "" =
  infer "cons_curry(id)(nil)";
  [%expect {|
    cons_curry(id)(nil)
    : a . list[a -> a]
    | |}]

let%expect_test "" =
  infer "let lst1 = cons(id, nil) in let lst2 = cons(succ, lst1) in lst2";
  [%expect
    {|
    let lst1 = cons(id, nil) in let lst2 = cons(succ, lst1) in lst2
    : list[int -> int]
    | |}]

let%expect_test "" =
  infer "cons_curry(id)(cons_curry(succ)(cons_curry(id)(nil)))";
  [%expect
    {|
    cons_curry(id)(cons_curry(succ)(cons_curry(id)(nil)))
    : list[int -> int]
    | |}]

let%expect_test "" =
  infer "plus(one, true)";
  [%expect
    {|
    plus(one, true)
    ERROR: incompatible types:
      int
    and
      bool
    | |}]

let%expect_test "" =
  infer "plus(one)";
  [%expect
    {|
    plus(one)
    ERROR: incompatible types:
      _2 -> _1
    and
      (int, int) -> int
    | |}]

let%expect_test "" =
  infer "fun x -> let y = x in y";
  [%expect {|
    fun x -> let y = x in y
    : a . a -> a
    | |}]

let%expect_test "" =
  infer "fun x -> let y = let z = x(fun x -> x) in z in y";
  [%expect
    {|
    fun x -> let y = let z = x(fun x -> x) in z in y
    : a, b . ((b -> b) -> a) -> a
    | |}]

let%expect_test "" =
  infer "fun x -> fun y -> let x = x(y) in x(y)";
  [%expect
    {|
    fun x -> fun y -> let x = x(y) in x(y)
    : a, b . (b -> b -> a) -> b -> a
    | |}]

let%expect_test "" =
  infer "fun x -> let y = fun z -> x(z) in y";
  [%expect
    {|
    fun x -> let y = fun z -> x(z) in y
    : a, b . (b -> a) -> b -> a
    | |}]

let%expect_test "" =
  infer "fun x -> let y = fun z -> x in y";
  [%expect
    {|
    fun x -> let y = fun z -> x in y
    : a, b . a -> b -> a
    | |}]

let%expect_test "" =
  infer "fun x -> fun y -> let x = x(y) in fun x -> y(x)";
  [%expect
    {|
    fun x -> fun y -> let x = x(y) in fun x -> y(x)
    : a, b, c . ((b -> a) -> c) -> (b -> a) -> b -> a
    | |}]

let%expect_test "" =
  infer "fun x -> let y = x in y(y)";
  [%expect {|
    fun x -> let y = x in y(y)
    ERROR: recursive type
    | |}]

let%expect_test "" =
  infer "fun x -> let y = fun z -> z in y(y)";
  [%expect
    {|
    fun x -> let y = fun z -> z in y(y)
    : a, b . b -> a -> a
    | |}]

let%expect_test "" =
  infer "fun x -> x(x)";
  [%expect {|
    fun x -> x(x)
    ERROR: recursive type
    | |}]

let%expect_test "" =
  infer "one(id)";
  [%expect
    {|
    one(id)
    ERROR: incompatible types:
      _2 -> _1
    and
      int
    | |}]

let%expect_test "" =
  infer "fun f -> let x = fun (g, y) -> let _ = g(y) in eq(f, g) in x";
  [%expect
    {|
    fun f -> let x = fun (g, y) -> let _ = g(y) in eq(f, g) in x
    : a, b . (b -> a) -> (b -> a, b) -> bool
    | |}]

let%expect_test "" =
  infer "let const = fun x -> fun y -> x in const";
  [%expect
    {|
    let const = fun x -> fun y -> x in const
    : a, b . a -> b -> a
    | |}]

let%expect_test "" =
  infer "let apply = fun (f, x) -> f(x) in apply";
  [%expect
    {|
    let apply = fun (f, x) -> f(x) in apply
    : a, b . (b -> a, b) -> a
    | |}]

let%expect_test "" =
  infer "let apply_curry = fun f -> fun x -> f(x) in apply_curry";
  [%expect
    {|
    let apply_curry = fun f -> fun x -> f(x) in apply_curry
    : a, b . (b -> a) -> b -> a
    | |}]
