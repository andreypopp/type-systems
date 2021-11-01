open Base
open Hmx

let env =
  Env.empty
  |> Env.assume_type "int" 0
  |> Env.assume_type "bool" 0
  |> Env.assume_type "string" 0
  |> Env.assume_type "list" 1
  |> Env.assume_type "pair" 2
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
  Var.reset ();
  let prog = Expr.parse_string code in
  match infer ~env prog with
  | Ok (e, ty_sch) ->
    (* Wrap into [let _ : ty = e in _] so that we print the inferred type. *)
    let e =
      Syntax.E_let (("_", e, Some ty_sch), E_var (Syntax.Path.make "_"))
    in
    Caml.Format.printf "%s@.|" (Expr.show e)
  | Error err -> Caml.Format.printf "ERROR: %s@.|" (Type_error.show err)

let%expect_test "" =
  infer "world";
  [%expect {|
    let _ : string = world in
    _
    | |}]

let%expect_test "" =
  infer "print";
  [%expect {|
    let _ : string -> string = print in
    _
    | |}]

let%expect_test "" =
  infer "let x = world in x";
  [%expect
    {|
    let _ : string =
      let x : string = world in
      x
    in
    _
    | |}]

let%expect_test "" =
  infer "fun () -> world";
  [%expect {|
    let _ : () -> string = fun () -> world in
    _
    | |}]

let%expect_test "" =
  infer "let x = fun () -> world in world";
  [%expect
    {|
    let _ : string =
      let x : () -> string = fun () -> world in
      world
    in
    _
    | |}]

let%expect_test "" =
  infer "let x = fun () -> world in x";
  [%expect
    {|
    let _ : () -> string =
      let x : () -> string = fun () -> world in
      x
    in
    _
    | |}]

let%expect_test "" =
  infer "print(world)";
  [%expect {|
    let _ : string = print(world) in
    _
    | |}]

let%expect_test "" =
  infer "let hello = fun msg -> print(msg) in hello(world)";
  [%expect
    {|
    let _ : string =
      let hello : string -> string = fun msg -> print(msg) in
      hello(world)
    in
    _
    | |}]

let%expect_test "" =
  infer "fun x -> let y = fun z -> z in y";
  [%expect
    {|
    let _ : a, b . a -> b -> b =
      fun x ->
        let y : c . c -> c = fun z -> z in y
    in
    _
    | |}]

let%expect_test "" =
  infer "fun x -> let y = x in y";
  [%expect
    {|
    let _ : a . a -> a =
      fun x ->
        let y : a = x in y
    in
    _
    | |}]

let%expect_test "" =
  infer "fun x -> let y = fun z -> x in y";
  [%expect
    {|
    let _ : a, b . b -> a -> b =
      fun x ->
        let y : c . c -> b = fun z -> x in y
    in
    _
    | |}]

let%expect_test "" =
  infer "id";
  [%expect {|
    let _ : a . a -> a = id in
    _
    | |}]

let%expect_test "" =
  infer "one";
  [%expect {|
    let _ : int = one in
    _
    | |}]

let%expect_test "" =
  infer "x";
  [%expect {|
    ERROR: unknown value: x
    | |}]

let%expect_test "" =
  infer "let x = x in x";
  [%expect {|
    ERROR: unknown value: x
    | |}]

let%expect_test "" =
  infer "let x = id in x";
  [%expect
    {|
    let _ : a . a -> a =
      let x : b . b -> b = id in
      x
    in
    _
    | |}]

let%expect_test "" =
  infer "let x = fun y -> y in x";
  [%expect
    {|
    let _ : a . a -> a =
      let x : b . b -> b = fun y -> y in
      x
    in
    _
    | |}]

let%expect_test "" =
  infer "fun x -> x";
  [%expect {|
    let _ : a . a -> a = fun x -> x in
    _
    | |}]

let%expect_test "" =
  infer "pair";
  [%expect {|
    let _ : a, b . (b, a) -> pair[b, a] = pair in
    _
    | |}]

let%expect_test "" =
  infer "fun x -> let y = fun z -> z in y";
  [%expect
    {|
    let _ : a, b . a -> b -> b =
      fun x ->
        let y : c . c -> c = fun z -> z in y
    in
    _
    | |}]

let%expect_test "" =
  infer "let f = fun x -> x in let id = fun y -> y in eq(f, id)";
  [%expect
    {|
    let _ : bool =
      let f : a . a -> a = fun x -> x in
      let id : b . b -> b = fun y -> y in
      eq(f, id)
    in
    _
    | |}]

let%expect_test "" =
  infer "let f = fun x -> x in let id = fun y -> y in eq_curry(f)(id)";
  [%expect
    {|
    let _ : bool =
      let f : a . a -> a = fun x -> x in
      let id : b . b -> b = fun y -> y in
      eq_curry(f)(id)
    in
    _
    | |}]

let%expect_test "" =
  infer "let f = fun x -> x in eq(f, succ)";
  [%expect
    {|
    let _ : bool =
      let f : a . a -> a = fun x -> x in
      eq(f, succ)
    in
    _
    | |}]

let%expect_test "" =
  infer "let f = fun x -> x in eq_curry(f)(succ)";
  [%expect
    {|
    let _ : bool =
      let f : a . a -> a = fun x -> x in
      eq_curry(f)(succ)
    in
    _
    | |}]

let%expect_test "" =
  infer "let f = fun x -> x in pair(f(one), f(true))";
  [%expect
    {|
    let _ : pair[int, bool] =
      let f : a . a -> a = fun x -> x in
      pair(f(one), f(true))
    in
    _
    | |}]

let%expect_test "" =
  infer "fun f -> pair(f(one), f(true))";
  [%expect
    {|
    ERROR: incompatible types:
      int
    and
      bool
    | |}]

let%expect_test "" =
  infer "let f = fun (x, y) -> let a = eq(x, y) in eq(x, y) in f";
  [%expect
    {|
    let _ : a . (a, a) -> bool =
      let f : b . (b, b) -> bool =
        fun (x, y) ->
          let a : bool = eq(x, y) in eq(x, y)
      in
      f
    in
    _
    | |}]

let%expect_test "" =
  infer "let f = fun (x, y) -> let a = eq_curry(x)(y) in eq_curry(x)(y) in f";
  [%expect
    {|
    let _ : a . (a, a) -> bool =
      let f : b . (b, b) -> bool =
        fun (x, y) ->
          let a : bool = eq_curry(x)(y) in eq_curry(x)(y)
      in
      f
    in
    _
    | |}]

let%expect_test "" =
  infer "id(id)";
  [%expect {|
    let _ : a . a -> a = id(id) in
    _
    | |}]

let%expect_test "" =
  infer "choose(fun (x, y) -> x, fun (x, y) -> y)";
  [%expect
    {|
    let _ : a . (a, a) -> a =
      choose(fun (x, y) -> x, fun (x, y) -> y)
    in
    _
    | |}]

let%expect_test "" =
  infer "choose_curry(fun (x, y) -> x)(fun (x, y) -> y)";
  [%expect
    {|
    let _ : a . (a, a) -> a =
      choose_curry(fun (x, y) -> x)(fun (x, y) -> y)
    in
    _
    | |}]

let%expect_test "" =
  infer "let x = id in let y = let z = x(id) in z in y";
  [%expect
    {|
    let _ : a . a -> a =
      let x : b . b -> b = id in
      let y : c . c -> c =
        let z : d . d -> d = x(id) in
        z
      in
      y
    in
    _
    | |}]

let%expect_test "" =
  infer "cons(id, nil)";
  [%expect {|
    let _ : a . list[a -> a] = cons(id, nil) in
    _
    | |}]

let%expect_test "" =
  infer "cons_curry(id)(nil)";
  [%expect
    {|
    let _ : a . list[a -> a] = cons_curry(id)(nil) in
    _
    | |}]

let%expect_test "" =
  infer "let lst1 = cons(id, nil) in let lst2 = cons(succ, lst1) in lst2";
  [%expect
    {|
    let _ : list[int -> int] =
      let lst1 : a . list[a -> a] = cons(id, nil) in
      let lst2 : list[int -> int] = cons(succ, lst1) in
      lst2
    in
    _
    | |}]

let%expect_test "" =
  infer "cons_curry(id)(cons_curry(succ)(cons_curry(id)(nil)))";
  [%expect
    {|
    let _ : list[int -> int] =
      cons_curry(id)(cons_curry(succ)(cons_curry(id)(nil)))
    in
    _
    | |}]

let%expect_test "" =
  infer "plus(one, true)";
  [%expect
    {|
    ERROR: incompatible types:
      int
    and
      bool
    | |}]

let%expect_test "" =
  infer "plus(one)";
  [%expect
    {|
    ERROR: incompatible types:
      _2 -> _1
    and
      (int, int) -> int
    | |}]

let%expect_test "" =
  infer "fun x -> let y = x in y";
  [%expect
    {|
    let _ : a . a -> a =
      fun x ->
        let y : a = x in y
    in
    _
    | |}]

let%expect_test "" =
  infer "fun x -> let y = let z = x(fun x -> x) in z in y";
  [%expect
    {|
    let _ : a, b . ((a -> a) -> b) -> b =
      fun x ->
        let y : b =
          let z : b = x(fun x -> x) in
          z
        in
        y
    in
    _
    | |}]

let%expect_test "" =
  infer "fun x -> fun y -> let x = x(y) in x(y)";
  [%expect
    {|
    let _ : a, b . (a -> a -> b) -> a -> b =
      fun x ->
        fun y ->
          let x : a -> b = x(y) in x(y)
    in
    _
    | |}]

let%expect_test "" =
  infer "fun x -> let y = fun z -> x(z) in y";
  [%expect
    {|
    let _ : a, b . (a -> b) -> a -> b =
      fun x ->
        let y : a -> b = fun z -> x(z) in y
    in
    _
    | |}]

let%expect_test "" =
  infer "fun x -> let y = fun z -> x in y";
  [%expect
    {|
    let _ : a, b . b -> a -> b =
      fun x ->
        let y : c . c -> b = fun z -> x in y
    in
    _
    | |}]

let%expect_test "" =
  infer "fun x -> fun y -> let x = x(y) in fun x -> y(x)";
  [%expect
    {|
    let _ : a, b, c . ((b -> c) -> a) -> (b -> c) -> b -> c =
      fun x ->
        fun y ->
          let x : a = x(y) in fun x -> y(x)
    in
    _
    | |}]

let%expect_test "" =
  infer "fun x -> let y = x in y(y)";
  [%expect {|
    ERROR: recursive type
    | |}]

let%expect_test "" =
  infer "fun x -> let y = fun z -> z in y(y)";
  [%expect
    {|
    let _ : a, b . a -> b -> b =
      fun x ->
        let y : c . c -> c = fun z -> z in y(y)
    in
    _
    | |}]

let%expect_test "" =
  infer "fun x -> x(x)";
  [%expect {|
    ERROR: recursive type
    | |}]

let%expect_test "" =
  infer "one(id)";
  [%expect
    {|
    ERROR: incompatible types:
      _2 -> _1
    and
      int
    | |}]

let%expect_test "" =
  infer "fun f -> let x = fun (g, y) -> let _ = g(y) in eq(f, g) in x";
  [%expect
    {|
    let _ : a, b . (a -> b) -> (a -> b, a) -> bool =
      fun f ->
        let x : (a -> b, a) -> bool =
          fun (g, y) ->
            let _ : b = g(y) in eq(f, g)
        in
        x
    in
    _
    | |}]

let%expect_test "" =
  infer "let const = fun x -> fun y -> x in const";
  [%expect
    {|
    let _ : a, b . b -> a -> b =
      let const : c, d . d -> c -> d = fun x -> fun y -> x in
      const
    in
    _
    | |}]

let%expect_test "" =
  infer "let apply = fun (f, x) -> f(x) in apply";
  [%expect
    {|
    let _ : a, b . (a -> b, a) -> b =
      let apply : c, d . (c -> d, c) -> d =
        fun (f, x) -> f(x)
      in
      apply
    in
    _
    | |}]

let%expect_test "" =
  infer "let apply_curry = fun f -> fun x -> f(x) in apply_curry";
  [%expect
    {|
    let _ : a, b . (a -> b) -> a -> b =
      let apply_curry : c, d . (c -> d) -> c -> d =
        fun f -> fun x -> f(x)
      in
      apply_curry
    in
    _
    | |}]
