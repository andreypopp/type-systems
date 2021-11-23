open Base
open Bidi_local

let env =
  Env.empty
  |> Env.assume_val "null" "a . a?"
  |> Env.assume_val "one" "int"
  |> Env.assume_val "nil" "a . list[a]"
  |> Env.assume_val "cons" "a . (a, list[a]) -> list[a]"
  |> Env.assume_val "map" "a, b . (a -> b, list[a]) -> list[b]"
  |> Env.assume_val "choose" "a . (a, a) -> a"
  |> Env.assume_val "choose3" "a . (a, a, a) -> a"
  |> Env.assume_val "choose4" "a . (a, a, a, a) -> a"
  |> Env.assume_val "hello" "string"
  |> Env.assume_val "pair" "a, b . (a, b) -> pair[a, b]"
  |> Env.assume_val "plus" "(int, int) -> int"
  |> Env.assume_val "true" "bool"
  |> Env.assume_val "ifnull" "a . (a?, a) -> a"
  |> Env.assume_val "eq" "a . (a, a) -> bool"

let infer ~env code =
  Var.reset ();
  let prog = Expr.parse_string code in
  match infer ~env prog with
  | Ok e -> Caml.Format.printf "%s@.|" (Expr.show e)
  | Error err -> Caml.Format.printf "ERROR: %s@.|" (Type_error.show err)

let%expect_test "" =
  infer ~env "choose(one, one)";
  [%expect {|
    (choose(one, one) : int)
    | |}]

let%expect_test "" =
  infer ~env "choose(null, one)";
  [%expect {|
    (choose(null, one) : int?)
    | |}]

let%expect_test "" =
  infer ~env "choose(one, null)";
  [%expect {|
    (choose(one, null) : int?)
    | |}]

let%expect_test "" =
  infer ~env "choose(null, null)";
  [%expect {|
    (choose(null, null) : b . b?)
    | |}]

let%expect_test "" =
  infer ~env
    {|
     let f = fun (cb: int? -> int) -> cb(one) in
     f(fun z -> ifnull(z, one))
    |};
  [%expect
    {|
    (let f : (int? -> int) -> int =
       fun (cb: int? -> int) -> cb(one)
     in
     f(fun (z: int?) -> ifnull(z, one))
     : int)
    | |}]

let%expect_test "" =
  infer ~env "map(fun x -> plus(x, x), cons(one, nil))";
  [%expect
    {|
    (map(fun (x: int) -> plus(x, x), cons(one, nil))
     : list[int])
    | |}]

let%expect_test "" =
  infer ~env "(null : int?)";
  [%expect {|
    (null : int?)
    | |}]

let env =
  env
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

let%expect_test "" =
  infer ~env "world";
  [%expect {|
    (world : string)
    | |}]

let%expect_test "" =
  infer ~env "print";
  [%expect {|
       (print : string -> string)
       | |}]

let%expect_test "" =
  infer ~env "let x = world in x";
  [%expect {|
       let x : string = world in
       x
       | |}]

let%expect_test "" =
  infer ~env "fun () -> world";
  [%expect {|
       (fun () -> world : () -> string)
       | |}]

let%expect_test "" =
  infer ~env "let x = fun () -> world in world";
  [%expect
    {|
       (let x : () -> string = fun () -> world in world : string)
       | |}]

let%expect_test "" =
  infer ~env "let x = fun () -> world in x";
  [%expect
    {|
       let x : () -> string = fun () -> world in
       x
       | |}]

let%expect_test "" =
  infer ~env "print(world)";
  [%expect {|
       (print(world) : string)
       | |}]

let%expect_test "" =
  infer ~env "let hello = fun (msg: string) -> print(msg) in hello(world)";
  [%expect
    {|
       (let hello : string -> string =
          fun (msg: string) -> print(msg)
        in
        hello(world)
        : string)
       | |}]

let%expect_test "" =
  infer ~env
    "(fun x -> let y : a . a -> a = fun z -> z in y : a, b . a -> b -> b)";
  [%expect
    {|
    (fun (x: a) ->
       let y : a/1 . a/1 -> a/1 = fun (z: a/1) -> z in y
     : a, b . a -> b -> b)
    | |}]

let%expect_test "" =
  infer ~env "(fun x -> let y = x in y : a . a -> a)";
  [%expect
    {|
    (fun (x: a) ->
       let y : a = x in y
     : a . a -> a)
    | |}]

let%expect_test "" =
  infer ~env "fun [a] (x: a) -> let y = fun [b] (z: b) -> x in y";
  [%expect
    {|
       (fun[a] (x: a) ->
          let y : b/1 . b/1 -> a = fun[b/1] (z: b/1) -> x in y
        : a, b . a -> b -> a)
       | |}]

let%expect_test "" =
  infer ~env "id";
  [%expect {|
       (id : b . b -> b)
       | |}]

let%expect_test "" =
  infer ~env "one";
  [%expect {|
       (one : int)
       | |}]

let%expect_test "" =
  infer ~env "x";
  [%expect {|
       ERROR: unknown name: x
       | |}]

let%expect_test "" =
  infer ~env "let x = x in x";
  [%expect {|
       ERROR: unknown name: x
       | |}]

let%expect_test "" =
  infer ~env "let x = id in x";
  [%expect {|
       let x : b . b -> b = id in
       x
       | |}]

let%expect_test "" =
  infer ~env "let x : a . a -> a = fun y -> y in x";
  [%expect
    {|
       let x : a . a -> a = fun (y: a) -> y in
       x
       | |}]

let%expect_test "" =
  infer ~env "(fun x -> x : a . a -> a)";
  [%expect {|
       (fun (x: a) -> x : a . a -> a)
       | |}]

let%expect_test "" =
  infer ~env "pair";
  [%expect {|
       (pair : b, b . (b, b) -> pair[b, b])
       | |}]

let%expect_test "" =
  infer ~env "(fun x -> let y = fun (z : b) -> z in y : a, b . a -> b -> b)";
  [%expect
    {|
       (fun (x: a) ->
          let y : b -> b = fun (z: b) -> z in y
        : a . a -> b -> b)
       | |}]

let%expect_test "" =
  infer ~env
    {|
    let f : a . a -> a = fun x -> x in
    let id : a . a -> a = fun y -> y in
    eq(f, id)
  |};
  [%expect
    {|
    (let f : a . a -> a = fun (x: a) -> x in
     let id : a/1 . a/1 -> a/1 = fun (y: a/1) -> y in
     eq(f, id)
     : bool)
    | |}]

let%expect_test "" =
  infer ~env
    {|
    let f : a . a -> a = fun x -> one in
    let id : a . a -> a = fun y -> true in
    choose(f, id)
  |};
  [%expect
    {|
    (let f : int -> int = fun (x: int) -> one in
     let id : bool -> bool = fun (y: bool) -> true in
     choose(f, id)
     : ⊥ -> ⊤)
    | |}]

let%expect_test "" =
  infer ~env
    "let f : a . a -> a = fun x -> x in let id : b . b -> b = fun y -> y in \
     eq_curry(f)(id)";
  [%expect
    {|
       (let f : a . a -> a = fun (x: a) -> x in
        let id : b . b -> b = fun (y: b) -> y in
        eq_curry(f)(id)
        : bool)
       | |}]

let%expect_test "" =
  infer ~env
    {|
    let f : a . a -> a = fun x -> one in
    let id : b . b -> b = fun y -> true in
    choose_curry(f)(id)
    |};
  [%expect {|
       ERROR: type int is not a subtype of bool
       | |}]

let%expect_test "" =
  infer ~env "let f : a . a -> a = fun x -> x in eq(f, succ)";
  [%expect
    {|
       (let f : a . a -> a = fun (x: a) -> x in eq(f, succ) : bool)
       | |}]

let%expect_test "" =
  infer ~env "let f : a . a -> a = fun x -> x in eq_curry(f)(succ)";
  [%expect
    {|
       (let f : a . a -> a = fun (x: a) -> x in
        eq_curry(f)(succ)
        : bool)
       | |}]

let%expect_test "" =
  infer ~env "let f : a . a -> a = fun x -> x in pair(f(one), f(true))";
  [%expect
    {|
       (let f : a . a -> a = fun (x: a) -> x in
        pair(f(one), f(true))
        : pair[int, bool])
       | |}]

let%expect_test "" =
  infer ~env
    {|
    let f : a . (a, a) -> bool =
      fun (x, y) -> let a = eq(x, y) in eq(x, y)
    in f
    |};
  [%expect
    {|
    let f : a . (a, a) -> bool =
      fun (x: a, y: a) ->
        let a : bool = eq(x, y) in eq(x, y)
    in
    f
    | |}]

let%expect_test "" =
  infer ~env
    {|
    let f : a . (a, a) -> bool =
      fun (x, y) -> let a = eq_curry(x)(y) in eq_curry(x)(y)
    in f
    |};
  [%expect
    {|
       let f : a . (a, a) -> bool =
         fun (x: a, y: a) ->
           let a : bool = eq_curry(x)(y) in eq_curry(x)(y)
       in
       f
       | |}]

let%expect_test "" =
  infer ~env "id(id)";
  [%expect {|
       (id(id) : b . b -> b)
       | |}]

let%expect_test "" =
  infer ~env "choose(fun (x, y) -> x, fun (x, y) -> y)";
  [%expect
    {|
       (choose(fun (x: b, y: b) -> x, fun (x: b, y: b) -> y)
        : b . (b, b) -> b)
       | |}]

let%expect_test "" =
  infer ~env "choose_curry(fun (x, y) -> x)(fun (x, y) -> y)";
  [%expect
    {|
       (choose_curry(fun (x: b, y: b) -> x)(fun (x: b, y: b) -> y)
        : b . (b, b) -> b)
       | |}]

let%expect_test "" =
  infer ~env "let x = id in let y = let z = x(id) in z in y";
  [%expect
    {|
       (let x : b . b -> b = id in
        let y : b . b -> b =
          let z : b . b -> b = x(id) in
          z
        in
        y
        : b . b -> b)
       | |}]

let%expect_test "" =
  infer ~env "cons(id, nil)";
  [%expect {|
       (cons(id, nil) : b . list[b -> b])
       | |}]

let%expect_test "" =
  infer ~env "cons_curry(id)(nil)";
  [%expect {|
       (cons_curry(id)(nil) : b . list[b -> b])
       | |}]

let%expect_test "" =
  infer ~env "let lst1 = cons(id, nil) in let lst2 = cons(succ, lst1) in lst2";
  [%expect
    {|
       (let lst1 : b . list[b -> b] = cons(id, nil) in
        let lst2 : list[int -> int] = cons(succ, lst1) in
        lst2
        : list[int -> int])
       | |}]

let%expect_test "" =
  infer ~env "cons_curry(id)(cons_curry(succ)(cons_curry(id)(nil)))";
  [%expect
    {|
       (cons_curry(id)(cons_curry(succ)(cons_curry(id)(nil)))
        : list[int -> int])
       | |}]

let%expect_test "" =
  infer ~env "plus(one, true)";
  [%expect {|
       ERROR: type bool is not a subtype of int
       | |}]

let%expect_test "" =
  infer ~env "plus(one)";
  [%expect {|
       ERROR: arity mismatch
       | |}]

let%expect_test "" =
  infer ~env "(fun x -> let y = x in y : a . a -> a)";
  [%expect
    {|
       (fun (x: a) ->
          let y : a = x in y
        : a . a -> a)
       | |}]

let%expect_test "" =
  infer ~env
    {|
     (fun x -> let y = let z = x(fun x -> x) in z in y
      : a, b . ((a -> a) -> b) -> b)
  |};
  [%expect
    {|
       (fun (x: (a -> a) -> b) ->
          let y : b =
            let z : b = x(fun (x: a) -> x) in
            z
          in
          y
        : a, b . ((a -> a) -> b) -> b)
       | |}]

let%expect_test "" =
  infer ~env
    {|
     (fun x -> fun y -> let x = x(y) in x(y)
     : a, b . (a -> a -> b) -> a -> b)
    |};
  [%expect
    {|
       (fun (x: a -> a -> b) ->
          fun (y: a) ->
            let x : a -> b = x(y) in x(y)
        : a, b . (a -> a -> b) -> a -> b)
       | |}]

let%expect_test "" =
  infer ~env
    {|
    fun[a, b] (x: a -> b) -> let y = fun [c] (z: c) -> x(z) in y
    |};
  [%expect
    {|
    (fun[a, b] (x: a -> b) ->
       let y : a -> b = fun[a] (z: a) -> x(z) in y
     : b, a . (a -> b) -> a -> b)
    | |}]

let%expect_test "" =
  infer ~env {|
    fun[a] (x: a) -> let y = fun [b] (z: b) -> x in y
    |};
  [%expect
    {|
    (fun[a] (x: a) ->
       let y : b/1 . b/1 -> a = fun[b/1] (z: b/1) -> x in y
     : a, b . a -> b -> a)
    | |}]

let%expect_test "" =
  infer ~env
    {|
    fun[a, b](x: a -> b) ->
      fun [c, d](y: c -> d) ->
        let x = x(y) in fun [e](x: e) -> y(x)
    |};
  [%expect
    {|
    (fun[a, b] (x: (e -> d) -> b) ->
       fun[e, d] (y: e -> d) ->
         let x : b = x(y) in fun[e] (x: e) -> y(x)
     : b, d, e . ((e -> d) -> b) -> (e -> d) -> e -> d)
    | |}]

let%expect_test "" =
  infer ~env {|
    fun[a](x: a) -> let y = fun[a](z: a) -> z in y(y)
    |};
  [%expect
    {|
    (fun[a] (x: a) ->
       let y : a/2 . a/2 -> a/2 = fun[a/2] (z: a/2) -> z in y(y)
     : a, a/1 . a -> a/1 -> a/1)
    | |}]

let%expect_test "" =
  infer ~env "one(id)";
  [%expect {|
       ERROR: expected a function but got: int
       | |}]

let%expect_test "" =
  infer ~env
    {|
    fun[a, b](f: a -> b) ->
      let x =
        fun (g: a -> b, y: a) ->
          let _ = g(y) in eq(f, g)
      in x
    |};
  [%expect
    {|
    (fun[a, b] (f: a -> b) ->
       let x : (a -> b, a) -> bool =
         fun (g: a -> b, y: a) ->
           let _ : b = g(y) in eq(f, g)
       in
       x
     : a, b . (a -> b) -> (a -> b, a) -> bool)
    | |}]

let%expect_test "" =
  infer ~env
    {|
    let const : a, b . b -> a -> b = fun x -> fun y -> x in const
    |};
  [%expect
    {|
       let const : a, b . b -> a -> b =
         fun (x: b) -> fun (y: a) -> x
       in
       const
       | |}]

let%expect_test "" =
  infer ~env
    {|
    let apply : a, b . (a -> b, a) -> b =
      fun (f, x) -> f(x)
    in apply
    |};
  [%expect
    {|
       let apply : a, b . (a -> b, a) -> b =
         fun (f: a -> b, x: a) -> f(x)
       in
       apply
       | |}]

let%expect_test "" =
  infer ~env
    {|
    let apply_curry : a, b . (a -> b) -> a -> b =
      fun f -> fun x -> f(x)
    in apply_curry
    |};
  [%expect
    {|
       let apply_curry : a, b . (a -> b) -> a -> b =
         fun (f: a -> b) -> fun (x: a) -> f(x)
       in
       apply_curry
       | |}]

(*
let%expect_test "" =
  infer ~env
    {|
    {a = one, b = one}
    |}

let%expect_test "" =
  infer ~env
    {|
    {a = one, b = one}.a
    |}

let%expect_test "" =
  infer ~env
    {|
    {a = one, b = one}.b
    |}

let%expect_test "" =
  infer ~env
    {|
    let update_a[r, a](data : {a : a, ...r}, v : a) =
      {data with a := v}
    in
    update_a({a = one, b = true}, null)
    |}

let%expect_test "" =
  infer ~env
    {|
    let update_a[r, a](data : {a : a, ...r}, v : int) =
      {data with a := plus(data.a, v)}
    in
    let data = {a = one, b = true} in
    update_a(data, null)
    |}

*)
