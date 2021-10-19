open Base
open Hmx_tc

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
  |> Env.assume_val "triple" "a, b, c . (a, b, c) -> triple[a, b, c]"
  |> Env.assume_val "quadruple"
       "a, b, c, e . (a, b, c, e) -> quadruple[a, b, c, e]"
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

let infer ~env code =
  Var.reset ();
  let prog = Expr.parse_string code in
  match infer ~env prog with
  | Ok e -> Caml.Format.printf "%s@.|" (Expr.show e)
  | Error err -> Caml.Format.printf "ERROR: %s@.|" (Type_error.show err)

let%expect_test "" =
  infer ~env "world";
  [%expect {|
    let _ : string = world in
    _
    | |}]

let%expect_test "" =
  infer ~env "print";
  [%expect {|
    let _ : string -> string = print in
    _
    | |}]

let%expect_test "" =
  infer ~env "let x = world in x";
  [%expect
    {|
    let _ : string =
      let x : string = world in
      x
    in
    _
    | |}]

let%expect_test "" =
  infer ~env "fun () -> world";
  [%expect {|
    let _ : () -> string = fun () -> world in
    _
    | |}]

let%expect_test "" =
  infer ~env "let x = fun () -> world in world";
  [%expect
    {|
    let _ : string =
      let x : () -> string = fun () -> world in
      world
    in
    _
    | |}]

let%expect_test "" =
  infer ~env "let x = fun () -> world in x";
  [%expect
    {|
    let _ : () -> string =
      let x : () -> string = fun () -> world in
      x
    in
    _
    | |}]

let%expect_test "" =
  infer ~env "print(world)";
  [%expect {|
    let _ : string = print(world) in
    _
    | |}]

let%expect_test "" =
  infer ~env "let hello = fun msg -> print(msg) in hello(world)";
  [%expect
    {|
    let _ : string =
      let hello : string -> string = fun msg -> print(msg) in
      hello(world)
    in
    _
    | |}]

let%expect_test "" =
  infer ~env "fun x -> let y = fun z -> z in y";
  [%expect
    {|
    let _ : a, b . a -> b -> b =
      fun x ->
        let y : c . c -> c = fun z -> z in y
    in
    _
    | |}]

let%expect_test "" =
  infer ~env "fun x -> let y = x in y";
  [%expect
    {|
    let _ : a . a -> a =
      fun x ->
        let y : a = x in y
    in
    _
    | |}]

let%expect_test "" =
  infer ~env "fun x -> let y = fun z -> x in y";
  [%expect
    {|
    let _ : a, b . b -> a -> b =
      fun x ->
        let y : c . c -> b = fun z -> x in y
    in
    _
    | |}]

let%expect_test "" =
  infer ~env "id";
  [%expect {|
    let _ : a . a -> a = id in
    _
    | |}]

let%expect_test "" =
  infer ~env "one";
  [%expect {|
    let _ : int = one in
    _
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
  [%expect
    {|
    let _ : a . a -> a =
      let x : b . b -> b = id in
      x
    in
    _
    | |}]

let%expect_test "" =
  infer ~env "let x = fun y -> y in x";
  [%expect
    {|
    let _ : a . a -> a =
      let x : b . b -> b = fun y -> y in
      x
    in
    _
    | |}]

let%expect_test "" =
  infer ~env "fun x -> x";
  [%expect {|
    let _ : a . a -> a = fun x -> x in
    _
    | |}]

let%expect_test "" =
  infer ~env "pair";
  [%expect {|
    let _ : a, b . (b, a) -> pair[b, a] = pair in
    _
    | |}]

let%expect_test "" =
  infer ~env "fun x -> let y = fun z -> z in y";
  [%expect
    {|
    let _ : a, b . a -> b -> b =
      fun x ->
        let y : c . c -> c = fun z -> z in y
    in
    _
    | |}]

let%expect_test "" =
  infer ~env "let f = fun x -> x in let id = fun y -> y in eq(f, id)";
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
  infer ~env "let f = fun x -> x in let id = fun y -> y in eq_curry(f)(id)";
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
  infer ~env "let f = fun x -> x in eq(f, succ)";
  [%expect
    {|
    let _ : bool =
      let f : a . a -> a = fun x -> x in
      eq(f, succ)
    in
    _
    | |}]

let%expect_test "" =
  infer ~env "let f = fun x -> x in eq_curry(f)(succ)";
  [%expect
    {|
    let _ : bool =
      let f : a . a -> a = fun x -> x in
      eq_curry(f)(succ)
    in
    _
    | |}]

let%expect_test "" =
  infer ~env "let f = fun x -> x in pair(f(one), f(true))";
  [%expect
    {|
    let _ : pair[int, bool] =
      let f : a . a -> a = fun x -> x in
      pair(f(one), f(true))
    in
    _
    | |}]

let%expect_test "" =
  infer ~env "fun f -> pair(f(one), f(true))";
  [%expect
    {|
    ERROR: incompatible types:
      int
    and
      bool
    | |}]

let%expect_test "" =
  infer ~env "let f = fun (x, y) -> let a = eq(x, y) in eq(x, y) in f";
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
  infer ~env
    "let f = fun (x, y) -> let a = eq_curry(x)(y) in eq_curry(x)(y) in f";
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
  infer ~env "id(id)";
  [%expect {|
    let _ : a . a -> a = id(id) in
    _
    | |}]

let%expect_test "" =
  infer ~env "choose(fun (x, y) -> x, fun (x, y) -> y)";
  [%expect
    {|
    let _ : a . (a, a) -> a =
      choose(fun (x, y) -> x, fun (x, y) -> y)
    in
    _
    | |}]

let%expect_test "" =
  infer ~env "choose_curry(fun (x, y) -> x)(fun (x, y) -> y)";
  [%expect
    {|
    let _ : a . (a, a) -> a =
      choose_curry(fun (x, y) -> x)(fun (x, y) -> y)
    in
    _
    | |}]

let%expect_test "" =
  infer ~env "let x = id in let y = let z = x(id) in z in y";
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
  infer ~env "cons(id, nil)";
  [%expect {|
    let _ : a . list[a -> a] = cons(id, nil) in
    _
    | |}]

let%expect_test "" =
  infer ~env "cons_curry(id)(nil)";
  [%expect
    {|
    let _ : a . list[a -> a] = cons_curry(id)(nil) in
    _
    | |}]

let%expect_test "" =
  infer ~env "let lst1 = cons(id, nil) in let lst2 = cons(succ, lst1) in lst2";
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
  infer ~env "cons_curry(id)(cons_curry(succ)(cons_curry(id)(nil)))";
  [%expect
    {|
    let _ : list[int -> int] =
      cons_curry(id)(cons_curry(succ)(cons_curry(id)(nil)))
    in
    _
    | |}]

let%expect_test "" =
  infer ~env "plus(one, true)";
  [%expect
    {|
    ERROR: incompatible types:
      int
    and
      bool
    | |}]

let%expect_test "" =
  infer ~env "plus(one)";
  [%expect
    {|
    ERROR: incompatible types:
      _2 -> _1
    and
      (int, int) -> int
    | |}]

let%expect_test "" =
  infer ~env "fun x -> let y = x in y";
  [%expect
    {|
    let _ : a . a -> a =
      fun x ->
        let y : a = x in y
    in
    _
    | |}]

let%expect_test "" =
  infer ~env "fun x -> let y = let z = x(fun x -> x) in z in y";
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
  infer ~env "fun x -> fun y -> let x = x(y) in x(y)";
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
  infer ~env "fun x -> let y = fun z -> x(z) in y";
  [%expect
    {|
    let _ : a, b . (a -> b) -> a -> b =
      fun x ->
        let y : a -> b = fun z -> x(z) in y
    in
    _
    | |}]

let%expect_test "" =
  infer ~env "fun x -> let y = fun z -> x in y";
  [%expect
    {|
    let _ : a, b . b -> a -> b =
      fun x ->
        let y : c . c -> b = fun z -> x in y
    in
    _
    | |}]

let%expect_test "" =
  infer ~env "fun x -> fun y -> let x = x(y) in fun x -> y(x)";
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
  infer ~env "fun x -> let y = x in y(y)";
  [%expect {|
    ERROR: recursive type
    | |}]

let%expect_test "" =
  infer ~env "fun x -> let y = fun z -> z in y(y)";
  [%expect
    {|
    let _ : a, b . a -> b -> b =
      fun x ->
        let y : c . c -> c = fun z -> z in y(y)
    in
    _
    | |}]

let%expect_test "" =
  infer ~env "fun x -> x(x)";
  [%expect {|
    ERROR: recursive type
    | |}]

let%expect_test "" =
  infer ~env "one(id)";
  [%expect
    {|
    ERROR: incompatible types:
      _2 -> _1
    and
      int
    | |}]

let%expect_test "" =
  infer ~env "fun f -> let x = fun (g, y) -> let _ = g(y) in eq(f, g) in x";
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
  infer ~env "let const = fun x -> fun y -> x in const";
  [%expect
    {|
    let _ : a, b . b -> a -> b =
      let const : c, d . d -> c -> d = fun x -> fun y -> x in
      const
    in
    _
    | |}]

let%expect_test "" =
  infer ~env "let apply = fun (f, x) -> f(x) in apply";
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
  infer ~env "let apply_curry = fun f -> fun x -> f(x) in apply_curry";
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

(* typeclasses *)

let env =
  env
  (* eq *)
  |> Env.assume_tclass "eq" "a . (a, a) -> bool"
  |> Env.assume_tclass_instance "eq_int" "eq[int]"
  |> Env.assume_tclass_instance "eq_bool" "eq[bool]"
  |> Env.assume_tclass_instance "eq_list" "a . eq[a] => eq[list[a]]"
  (* compare[a] *)
  |> Env.assume_tclass "compare" "a . eq[a] => (a, a) -> bool"
  |> Env.assume_tclass_instance "compare_int" "compare[int]"
  |> Env.assume_tclass_instance "compare_list"
       "a . compare[a] => compare[list[a]]"
  (* show *)
  |> Env.assume_tclass "show" "a . a -> string"
  |> Env.assume_tclass_instance "show_int" "show[int]"
  |> Env.assume_tclass_instance "show_float" "show[float]"
  (* read *)
  |> Env.assume_tclass "read" "a . string -> a"
  |> Env.assume_tclass_instance "read_int" "read[int]"
  |> Env.assume_tclass_instance "read_float" "read[float]"
  (* coerce *)
  |> Env.assume_tclass "coerce" "a, b . a -> b"
  |> Env.assume_tclass_instance "coerce_id" "a . coerce[a, a]"
  |> Env.assume_tclass_instance "coerce_list"
       "a, b . coerce[a, b] => coerce[list[a], list[b]]"
  |> Env.assume_tclass_instance "coerce_bool_int" "coerce[bool, int]"

let%expect_test "just a sanity check" =
  infer ~env "eq";
  [%expect
    {|
    let _ : a . eq[a] => (a, a) -> bool =
      fun _eq_0_1 -> _eq_0_1.eq
    in
    _
    | |}]

let%expect_test "just a sanity check" =
  infer ~env "let f = eq in f";
  [%expect
    {|
    let _ : a . eq[a] => (a, a) -> bool =
      fun _eq_0_1 ->
        let f : b . eq[b] => (b, b) -> bool =
          fun _eq_1_1 -> _eq_1_1.eq
        in
        f(_eq_0_1)
    in
    _
    | |}]

let%expect_test "just a sanity check" =
  infer ~env "fun (x, y) -> eq(x, y)";
  [%expect
    {|
    let _ : a . eq[a] => (a, a) -> bool =
      fun _eq_0_1 -> fun (x, y) -> _eq_0_1.eq(x, y)
    in
    _
    | |}]

let%expect_test "eq[int] should be completely resolved" =
  infer ~env "fun (x) -> eq(x, one)";
  [%expect
    {|
    let _ : int -> bool = fun x -> eq_int.eq(x, one) in
    _
    | |}]

let%expect_test "eq[list[a]] should be resolved to eq[a]" =
  infer ~env "fun (x) -> eq(cons(x, nil), cons(x, nil))";
  [%expect
    {|
    let _ : a . eq[a] => a -> bool =
      fun _eq_0_1 ->
        fun x -> eq_list(_eq_0_1).eq(cons(x, nil), cons(x, nil))
    in
    _
    | |}]

let%expect_test "eq[list[int]] should be completely resolved" =
  infer ~env "fun (x) -> eq(cons(x, nil), cons(one, nil))";
  [%expect
    {|
    let _ : int -> bool =
      fun x -> eq_list(eq_int).eq(cons(x, nil), cons(one, nil))
    in
    _
    | |}]

let%expect_test "eq[list[int]] should be completely resolved" =
  infer ~env "fun (x) -> eq(x, cons(one, nil))";
  [%expect
    {|
    let _ : list[int] -> bool =
      fun x -> eq_list(eq_int).eq(x, cons(one, nil))
    in
    _
    | |}]

let%expect_test "eq[c] constraint is retained at f while eq[list[a]] is \
                 deferred till the top" =
  infer ~env
    {|
    fun y ->
      let f x = pair(eq(cons(x, nil), nil), eq(y, nil)) in
      f
    |};
  [%expect
    {|
    let _ :
        a, b . eq[a], eq[b] => list[a] -> b -> pair[bool, bool] =
      fun (_eq_1_1, _eq_0_1) ->
        fun y ->
          let f : c . eq[c] => c -> pair[bool, bool] =
            fun _eq_1_2 ->
              fun x ->
                pair(
                  eq_list(_eq_1_2).eq(cons(x, nil), nil),
                  eq_list(_eq_1_1).eq(y, nil))
          in
          f(_eq_0_1)
    in
    _
    | |}]

let%expect_test "should be ambigious" =
  infer ~env "show(read(world))";
  [%expect {|
    ERROR: ambigious typeclass application: read[_2]
    | |}]

let%expect_test "should be ambigious" =
  infer ~env "fun x -> show(read(x))";
  [%expect {|
    ERROR: ambigious typeclass application: read[_4]
    | |}]

let%expect_test "usage of plus resolves ambiguity" =
  infer ~env "show(plus(read(world), one))";
  [%expect
    {|
    let _ : string =
      show_int.show(plus(read_int.read(world), one))
    in
    _
    | |}]

let%expect_test "usage of plus resolves ambiguity" =
  infer ~env "fun x -> show(plus(read(x), one))";
  [%expect
    {|
    let _ : string -> string =
      fun x -> show_int.show(plus(read_int.read(x), one))
    in
    _
    | |}]

let%expect_test "just a sanity check" =
  infer ~env "fun (x, y) -> pair(eq(x, x), eq(y, y))";
  [%expect
    {|
    let _ : a, b . eq[b], eq[a] => (b, a) -> pair[bool, bool] =
      fun (_eq_0_2, _eq_0_1) ->
        fun (x, y) -> pair(_eq_0_2.eq(x, x), _eq_0_1.eq(y, y))
    in
    _
    | |}]

let%expect_test "just a sanity check" =
  infer ~env "fun (x, y) -> pair(eq(cons(x, nil), nil), eq(y, nil))";
  [%expect
    {|
    let _ :
        a, b . eq[b], eq[a] => (b, list[a]) -> pair[bool, bool] =
      fun (_eq_0_2, _eq_0_1) ->
        fun (x, y) ->
          pair(
            eq_list(_eq_0_2).eq(cons(x, nil), nil),
            eq_list(_eq_0_1).eq(y, nil))
    in
    _
    | |}]

let%expect_test "just a sanity check" =
  infer ~env "fun (x, y) -> pair(eq(cons(x, nil), nil), eq(cons(y, nil), nil))";
  [%expect
    {|
    let _ : a, b . eq[b], eq[a] => (b, a) -> pair[bool, bool] =
      fun (_eq_0_2, _eq_0_1) ->
        fun (x, y) ->
          pair(
            eq_list(_eq_0_2).eq(cons(x, nil), nil),
            eq_list(_eq_0_1).eq(cons(y, nil), nil))
    in
    _
    | |}]

let%expect_test "just a sanity check" =
  infer ~env "fun (x, y) -> compare(x, y)";
  [%expect
    {|
    let _ : a . compare[a] => (a, a) -> bool =
      fun _compare_0_1 ->
        fun (x, y) -> _compare_0_1.compare(x, y)
    in
    _
    | |}]

let%expect_test "compare[a] subsumes eq[a]" =
  infer ~env "fun (x, y) -> pair(compare(x, y), eq(x, y))";
  [%expect
    {|
    let _ : a . compare[a] => (a, a) -> pair[bool, bool] =
      fun _compare_0_2 ->
        fun (x, y) ->
          pair(_compare_0_2.compare(x, y), _compare_0_2.eq(x, y))
    in
    _
    | |}]

let%expect_test "no compare[bool] defined" =
  infer ~env "fun (x, y) -> compare(x, true)";
  [%expect {|
    ERROR: no typeclass instance found: compare[bool]
    | |}]

let%expect_test "just a sanity check" =
  infer ~env "fun (x, y) -> compare(x, nil)";
  [%expect
    {|
    let _ : a, b . compare[b] => (list[b], a) -> bool =
      fun _compare_0_1 ->
        fun (x, y) -> compare_list(_compare_0_1).compare(x, nil)
    in
    _
    | |}]

let%expect_test "just a sanity check" =
  infer ~env
    {|
    let f (x, y) =
      quadruple(
        eq(x, x),
        compare(x, x),
        eq(nil, y),
        compare(nil, y)
      )
    in
    f(cons(one, nil), cons(one, nil))
    |};
  [%expect
    {|
    let _ : quadruple[bool, bool, bool, bool] =
      let f :
          a, b . compare[b], compare[a] =>
          (b, list[a]) -> quadruple[bool, bool, bool, bool] =
        fun (_compare_1_3, _compare_1_1) ->
          fun (x, y) ->
            quadruple(
              _compare_1_3.eq(x, x),
              _compare_1_3.compare(x, x),
              eq_list(_compare_1_1).eq(nil, y),
              compare_list(_compare_1_1).compare(nil, y))
      in
      f(compare_list(compare_int), compare_int)(
        cons(one, nil),
        cons(one, nil))
    in
    _
    | |}]

let%expect_test "check deferred constraints" =
  infer ~env
    {|
    let g y =
      let f x = pair(eq(cons(x, nil), nil), eq(y, nil)) in
      one
    in
    g(cons(one, nil))
    |};
  [%expect
    {|
    let _ : int =
      let g : a . eq[a] => list[a] -> int =
        fun _eq_2_1 ->
          fun y ->
            let f : b . eq[b] => b -> pair[bool, bool] =
              fun _eq_2_2 ->
                fun x ->
                  pair(
                    eq_list(_eq_2_2).eq(cons(x, nil), nil),
                    eq_list(_eq_2_1).eq(y, nil))
            in
            one
      in
      g(eq_int)(cons(one, nil))
    in
    _
    | |}]

let%expect_test "check deferred constraints" =
  infer ~env
    {|
    let g y =
      let f x = pair(eq(cons(x, nil), nil), eq(y, nil)) in
      pair(one, eq(one, one))
    in
    g(cons(one, nil))
    |};
  [%expect
    {|
    let _ : pair[int, bool] =
      let g : a . eq[a] => list[a] -> pair[int, bool] =
        fun _eq_2_1 ->
          fun y ->
            let f : b . eq[b] => b -> pair[bool, bool] =
              fun _eq_2_2 ->
                fun x ->
                  pair(
                    eq_list(_eq_2_2).eq(cons(x, nil), nil),
                    eq_list(_eq_2_1).eq(y, nil))
            in
            pair(one, eq_int.eq(one, one))
      in
      g(eq_int)(cons(one, nil))
    in
    _
    | |}]

let%expect_test "check deferred constraints" =
  infer ~env
    {|
    let g y =
      let f x = pair(eq(cons(x, nil), nil), eq(y, nil)) in
      pair(one, eq(y, nil))
    in
    g(cons(one, nil))
    |};
  [%expect
    {|
    let _ : pair[int, bool] =
      let g : a . eq[a] => list[a] -> pair[int, bool] =
        fun _eq_2_1 ->
          fun y ->
            let f : b . eq[b] => b -> pair[bool, bool] =
              fun _eq_2_2 ->
                fun x ->
                  pair(
                    eq_list(_eq_2_2).eq(cons(x, nil), nil),
                    eq_list(_eq_2_1).eq(y, nil))
            in
            pair(one, eq_list(_eq_2_1).eq(y, nil))
      in
      g(eq_int)(cons(one, nil))
    in
    _
    | |}]

let%expect_test "check deferred constraints" =
  infer ~env
    {|
    let g y =
      let f x = pair(eq(cons(x, nil), nil), eq(y, nil)) in
      pair(f(y), compare(y, nil))
    in
    g(cons(one, nil))
    |};
  [%expect
    {|
    let _ : pair[pair[bool, bool], bool] =
      let g :
          a . compare[a] =>
          list[a] -> pair[pair[bool, bool], bool] =
        fun _compare_1_1 ->
          fun y ->
            let f : b . eq[b] => b -> pair[bool, bool] =
              fun _eq_2_2 ->
                fun x ->
                  pair(
                    eq_list(_eq_2_2).eq(cons(x, nil), nil),
                    eq_list(_compare_1_1).eq(y, nil))
            in
            pair(
              f(eq_list(_compare_1_1))(y),
              compare_list(_compare_1_1).compare(y, nil))
      in
      g(compare_int)(cons(one, nil))
    in
    _
    | |}]

let%expect_test "multi parameter type classes" =
  infer ~env
    {|
    let g =
      fun x ->
        let f y = eq(coerce(x), y) in f
    in
    g
    |};
  [%expect
    {|
    let _ : a, b . coerce[a, b], eq[b] => a -> b -> bool =
      fun (_coerce_0_1, _eq_0_2) ->
        let g : c, d . coerce[c, d], eq[d] => c -> d -> bool =
          fun (_coerce_2_2, _eq_2_1) ->
            fun x ->
              let f : d -> bool =
                fun y -> _eq_2_1.eq(_coerce_2_2.coerce(x), y)
              in
              f
        in
        g(_coerce_0_1, _eq_0_2)
    in
    _
    | |}]

let%expect_test "multi parameter type classes" =
  infer ~env
    {|
    let g =
      fun x ->
        let f y = eq(coerce(x), y) in f
    in
    g(true)
    |};
  [%expect
    {|
    let _ : a . coerce[bool, a], eq[a] => a -> bool =
      fun (_coerce_0_1, _eq_0_2) ->
        let g : b, c . coerce[b, c], eq[c] => b -> c -> bool =
          fun (_coerce_2_2, _eq_2_1) ->
            fun x ->
              let f : c -> bool =
                fun y -> _eq_2_1.eq(_coerce_2_2.coerce(x), y)
              in
              f
        in
        g(_coerce_0_1, _eq_0_2)(true)
    in
    _
    | |}]

let%expect_test "multi parameter type classes" =
  infer ~env
    {|
    let g =
      fun x ->
        let f y = eq(coerce(x), y) in f
    in
    g(true)(one)
    |};
  [%expect
    {|
    let _ : bool =
      let g : a, b . coerce[a, b], eq[b] => a -> b -> bool =
        fun (_coerce_2_2, _eq_2_1) ->
          fun x ->
            let f : b -> bool =
              fun y -> _eq_2_1.eq(_coerce_2_2.coerce(x), y)
            in
            f
      in
      g(coerce_bool_int, eq_int)(true)(one)
    in
    _
    | |}]

let%expect_test "should eliminate eq[int]" =
  infer ~env {|
    fun x ->
      let f y = eq(x, y) in f(one)
    |};
  [%expect
    {|
    let _ : int -> bool =
      fun x ->
        let f : int -> bool = fun y -> eq_int.eq(x, y) in f(one)
    in
    _
    | |}]

let%expect_test "should eliminate eq[int]" =
  infer ~env
    {|
    let equal_to_one x = eq(one, coerce(x)) in
    equal_to_one
    |};
  [%expect
    {|
    let _ : a . coerce[a, int] => a -> bool =
      fun _coerce_0_1 ->
        let equal_to_one : b . coerce[b, int] => b -> bool =
          fun _coerce_1_1 ->
            fun x -> eq_int.eq(one, _coerce_1_1.coerce(x))
        in
        equal_to_one(_coerce_0_1)
    in
    _
    | |}]
