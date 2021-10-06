open Base

let env =
  let assume name ty env = Map.set env ~key:name ~data:(Mu.parse_ty ty) in
  Mu.empty_env
  |> assume "head" "forall[a] list[a] -> a"
  |> assume "tail" "forall[a] list[a] -> list[a]"
  |> assume "nil" "forall[a] list[a]"
  |> assume "cons" "forall[a] (a, list[a]) -> list[a]"
  |> assume "cons_curry" "forall[a] a -> list[a] -> list[a]"
  |> assume "map" "forall[a b] (a -> b, list[a]) -> list[b]"
  |> assume "map_curry" "forall[a b] (a -> b) -> list[a] -> list[b]"
  |> assume "one" "int"
  |> assume "zero" "int"
  |> assume "succ" "int -> int"
  |> assume "plus" "(int, int) -> inc"
  |> assume "eq" "forall[a] (a, a) -> bool"
  |> assume "eq_curry" "forall[a] a -> a -> bool"
  |> assume "not" "bool -> bool"
  |> assume "true" "bool"
  |> assume "false" "bool"
  |> assume "pair" "forall[a b] (a, b) -> pair[a, b]"
  |> assume "pair_curry" "forall[a b] a -> b -> pair[a, b]"
  |> assume "first" "forall[a b] pair[a, b] -> a"
  |> assume "second" "forall[a b] pair[a, b] -> b"
  |> assume "id" "forall[a] a -> a"
  |> assume "const" "forall[a b] a -> b -> a"
  |> assume "apply" "forall[a b] (a -> b, a) -> b"
  |> assume "apply_curry" "forall[a b] (a -> b) -> a -> b"
  |> assume "choose" "forall[a] (a, a) -> a"
  |> assume "choose_curry" "forall[a] a -> a -> a"
  |> assume "age" "int"
  |> assume "world" "string"
  |> assume "print" "string -> string"
  |> assume "print_user" "(string,age) -> string"

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
  infer {|
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
  infer {|
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

(* TESTS FROM type-systems repo *)

let%expect_test "" =
  infer "id";
  [%expect {|
    id
    : a -> a
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
    : a -> a
    | |}]

let%expect_test "" =
  infer "let x = fun y -> y in x";
  [%expect {|
    let x = fun y -> y in x
    : a -> a
    | |}]

let%expect_test "" =
  infer "fun x -> x";
  [%expect {|
    fun x -> x
    : a -> a
    | |}]

let%expect_test "" =
  infer "pair";
  [%expect {|
    pair
    : (a, b) -> pair[a, b]
    | |}]

let%expect_test "" =
  infer "fun x -> let y = fun z -> z in y";
  [%expect {|
    fun x -> let y = fun z -> z in y
    : b -> a -> a
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
    ERROR: unification error of
      bool
    with
      int
    | |}]

let%expect_test "" =
  infer "let f = fun (x, y) -> let a = eq(x, y) in eq(x, y) in f";
  [%expect
    {|
    let f = fun (x, y) -> let a = eq(x, y) in eq(x, y) in f
    : (a, a) -> bool
    | |}]

let%expect_test "" =
  infer "let f = fun (x, y) -> let a = eq_curry(x)(y) in eq_curry(x)(y) in f";
  [%expect
    {|
    let f = fun (x, y) -> let a = eq_curry(x)(y) in eq_curry(x)(y) in f
    : (a, a) -> bool
    | |}]

let%expect_test "" =
  infer "id(id)";
  [%expect {|
    id(id)
    : a -> a
    | |}]

let%expect_test "" =
  infer "choose(fun (x, y) -> x, fun (x, y) -> y)";
  [%expect
    {|
    choose(fun (x, y) -> x, fun (x, y) -> y)
    : (a, a) -> a
    | |}]

let%expect_test "" =
  infer "choose_curry(fun (x, y) -> x)(fun (x, y) -> y)";
  [%expect
    {|
    choose_curry(fun (x, y) -> x)(fun (x, y) -> y)
    : (a, a) -> a
    | |}]

let%expect_test "" =
  infer "let x = id in let y = let z = x(id) in z in y";
  [%expect
    {|
    let x = id in let y = let z = x(id) in z in y
    : a -> a
    | |}]

let%expect_test "" =
  infer "cons(id, nil)";
  [%expect {|
    cons(id, nil)
    : list[a -> a]
    | |}]

let%expect_test "" =
  infer "cons_curry(id)(nil)";
  [%expect {|
    cons_curry(id)(nil)
    : list[a -> a]
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
    ERROR: unification error of
      bool
    with
      int
    | |}]

let%expect_test "" =
  infer "plus(one)";
  [%expect
    {|
    plus(one)
    ERROR: arity mismatch: expected1 but got 2
    | |}]

let%expect_test "" =
  infer "fun x -> let y = x in y";
  [%expect {|
    fun x -> let y = x in y
    : a -> a
    | |}]

let%expect_test "" =
  infer "fun x -> let y = let z = x(fun x -> x) in z in y";
  [%expect
    {|
    fun x -> let y = let z = x(fun x -> x) in z in y
    : ((b -> b) -> a) -> a
    | |}]

let%expect_test "" =
  infer "fun x -> fun y -> let x = x(y) in x(y)";
  [%expect
    {|
    fun x -> fun y -> let x = x(y) in x(y)
    : (b -> b -> a) -> b -> a
    | |}]

let%expect_test "" =
  infer "fun x -> let y = fun z -> x(z) in y";
  [%expect
    {|
    fun x -> let y = fun z -> x(z) in y
    : (b -> a) -> b -> a
    | |}]

let%expect_test "" =
  infer "fun x -> let y = fun z -> x in y";
  [%expect {|
    fun x -> let y = fun z -> x in y
    : a -> b -> a
    | |}]

let%expect_test "" =
  infer "fun x -> fun y -> let x = x(y) in fun x -> y(x)";
  [%expect
    {|
    fun x -> fun y -> let x = x(y) in fun x -> y(x)
    : ((b -> a) -> c) -> (b -> a) -> b -> a
    | |}]

let%expect_test "" =
  infer "fun x -> let y = x in y(y)";
  [%expect
    {|
    fun x -> let y = x in y(y)
    ERROR: recursive types
    | |}]

let%expect_test "" =
  infer "fun x -> let y = fun z -> z in y(y)";
  [%expect
    {|
    fun x -> let y = fun z -> z in y(y)
    : b -> a -> a
    | |}]

let%expect_test "" =
  infer "fun x -> x(x)";
  [%expect {|
    fun x -> x(x)
    ERROR: recursive types
    | |}]

let%expect_test "" =
  infer "one(id)";
  [%expect {|
    one(id)
    ERROR: expected a function
    | |}]

let%expect_test "" =
  infer "fun f -> let x = fun (g, y) -> let _ = g(y) in eq(f, g) in x";
  [%expect
    {|
    fun f -> let x = fun (g, y) -> let _ = g(y) in eq(f, g) in x
    : (b -> a) -> (b -> a, b) -> bool
    | |}]

let%expect_test "" =
  infer "let const = fun x -> fun y -> x in const";
  [%expect
    {|
    let const = fun x -> fun y -> x in const
    : a -> b -> a
    | |}]

let%expect_test "" =
  infer "let apply = fun (f, x) -> f(x) in apply";
  [%expect
    {|
    let apply = fun (f, x) -> f(x) in apply
    : (b -> a, b) -> a
    | |}]

let%expect_test "" =
  infer "let apply_curry = fun f -> fun x -> f(x) in apply_curry";
  [%expect
    {|
    let apply_curry = fun f -> fun x -> f(x) in apply_curry
    : (b -> a) -> b -> a
    | |}]

(* TESTS FROM type-systems repo: records *)

let%expect_test "" = infer "{}";
  [%expect {|
    {  }
    : {  }
    | |}]

let%expect_test "" = infer "({}).x";
  [%expect {|
    ({  }).x
    ERROR: unification error of
      {  }
    with
      { x: _1; _2 }
    | |}]

let%expect_test "" = infer "{a = one}";
  [%expect {|
    { a = one }
    : { a: int;  }
    | |}]

let%expect_test "" = infer "{a = one; b = true}";
  [%expect {|
    { a = one; b = true }
    : { b: bool; a: int;  }
    | |}]

let%expect_test "" = infer "{b = true; a = one}";
  [%expect {|
    { b = true; a = one }
    : { a: int; b: bool;  }
    | |}]

let%expect_test "" = infer "({a = one; b = true}).a";
  [%expect {|
    ({ a = one; b = true }).a
    : int
    | |}]

let%expect_test "" = infer "({a = one; b = true}).b";
  [%expect {|
    ({ a = one; b = true }).b
    : bool
    | |}]

let%expect_test "" = infer "({a = one; b = true}).c";
  [%expect {|
    ({ a = one; b = true }).c
    ERROR: unification error of
      {  }
    with
      { c: _1; _4 }
    | |}]

let%expect_test "" = infer "{f = fun x -> x}";
  [%expect {|
    { f = fun x -> x }
    : { f: a -> a;  }
    | |}]

let%expect_test "" = infer "let r = {a = id; b = succ} in choose(r.a, r.b)";
  [%expect {|
    let r = { a = id; b = succ } in choose(r.a, r.b)
    : int -> int
    | |}]

let%expect_test "" =
  infer "let r = {a = id; b = fun x -> x} in choose(r.a, r.b)";
  [%expect {|
    let r = { a = id; b = fun x -> x } in choose(r.a, r.b)
    : a -> a
    | |}]

let%expect_test "" = infer "choose({a = one}, {})";
  [%expect {|
    choose({ a = one }, {  })
    ERROR: unification error of
      {  }
    with
      { a: int;  }
    | |}]

let%expect_test "" = infer "{ { {} with y = one } with x = zero }";
  [%expect {|
    { { {  } with y = one } with x = zero }
    : { x: int; y: int;  }
    | |}]

let%expect_test "" =
  infer "choose({ { {} with y = one } with x = zero }, {x = one; y = zero})";
  [%expect {|
    choose({ { {  } with y = one } with x = zero }, { x = one; y = zero })
    : { x: int; y: int;  }
    | |}]

let%expect_test "" = infer "{ {x = one } with x = true }";
  [%expect {|
    { { x = one } with x = true }
    : { x: bool; x: int;  }
    | |}]

let%expect_test "" = infer "{ {x = one } with x := true }";
  [%expect {|
    { { x = one } with x := true }
    ERROR: unification error of
      int
    with
      bool
    | |}]

let%expect_test "" = infer "let a = {} in {a with b := one}";
  [%expect {|
    let a = {  } in { a with b := one }
    ERROR: unification error of
      { b: _2; _1 }
    with
      {  }
    | |}]

let%expect_test "" = infer "let a = {x = one} in ({a with x = true}).x";
  [%expect {|
    let a = { x = one } in ({ a with x = true }).x
    : bool
    | |}]

let%expect_test "" = infer "let a = {x = one} in ({a with x := true}).x";
  [%expect {|
    let a = { x = one } in ({ a with x := true }).x
    ERROR: unification error of
      int
    with
      bool
    | |}]

let%expect_test "" = infer "let a = {x = one} in a.y";
  [%expect {|
    let a = { x = one } in a.y
    ERROR: unification error of
      {  }
    with
      { y: _1; _3 }
    | |}]

let%expect_test "" = infer "fun r -> {r with x = one}";
  [%expect {|
    fun r -> { r with x = one }
    : { a } -> { x: int; a }
    | |}]

let%expect_test "" = infer "fun r -> {r with x := one}";
  [%expect {|
    fun r -> { r with x := one }
    : { x: int; a } -> { x: int; a }
    | |}]

let%expect_test "" = infer "let addx = fun r -> {r with x = one} in addx({})";
  [%expect {|
    let addx = fun r -> { r with x = one } in addx({  })
    : { x: int;  }
    | |}]

let%expect_test "" = infer "let addx = fun r -> {r with x := one} in addx({})";
  [%expect {|
    let addx = fun r -> { r with x := one } in addx({  })
    ERROR: unification error of
      {  }
    with
      { x: int; _4 }
    | |}]

let%expect_test "" =
  infer "let addx = fun r -> {r with x = one} in addx({x = one})";
  [%expect {|
    let addx = fun r -> { r with x = one } in addx({ x = one })
    : { x: int; x: int;  }
    | |}]

let%expect_test "" =
  infer "let addx = fun r -> {r with x := one} in addx({x = one})";
  [%expect {|
    let addx = fun r -> { r with x := one } in addx({ x = one })
    : { x: int;  }
    | |}]

let%expect_test "" = infer "fun r -> r.x";
  [%expect {|
    fun r -> r.x
    : { x: a; b } -> a
    | |}]

let%expect_test "" =
  infer "let get_x = fun r -> r.x in get_x({y = one; x = zero})";
  [%expect {|
    let get_x = fun r -> r.x in get_x({ y = one; x = zero })
    : int
    | |}]

let%expect_test "" =
  infer "let get_x = fun r -> r.x in get_x({y = one; z = true})";
  [%expect {|
    let get_x = fun r -> r.x in get_x({ y = one; z = true })
    ERROR: unification error of
      {  }
    with
      { x: _4; _7 }
    | |}]

let%expect_test "" =
  infer "fun r -> choose({r with x = zero}, {{} with x = one})";
  [%expect {|
    fun r -> choose({ r with x = zero }, { {  } with x = one })
    : {  } -> { x: int;  }
    | |}]

let%expect_test "" =
  infer "fun r -> choose({r with x := zero}, {{} with x = one})";
  [%expect {|
    fun r -> choose({ r with x := zero }, { {  } with x = one })
    : { x: int;  } -> { x: int;  }
    | |}]

let%expect_test "" = infer "fun r -> choose({r with x = zero}, {x = one})";
  [%expect {|
    fun r -> choose({ r with x = zero }, { x = one })
    : {  } -> { x: int;  }
    | |}]

let%expect_test "" = infer "fun r -> choose({r with x := zero}, {x = one})";
  [%expect {|
    fun r -> choose({ r with x := zero }, { x = one })
    : { x: int;  } -> { x: int;  }
    | |}]

let%expect_test "" =
  infer "fun r -> choose({r with x = zero}, {r with x = one})";
  [%expect {|
    fun r -> choose({ r with x = zero }, { r with x = one })
    : { a } -> { x: int; a }
    | |}]

let%expect_test "" =
  infer "fun r -> choose({r with x := zero}, {r with x := one})";
  [%expect {|
    fun r -> choose({ r with x := zero }, { r with x := one })
    : { x: int; a } -> { x: int; a }
    | |}]

let%expect_test "" =
  infer "fun r -> choose({r with x = zero}, {r with y = one})";
  [%expect {|
    fun r -> choose({ r with x = zero }, { r with y = one })
    ERROR: recursive row types
    | |}]

let%expect_test "" =
  infer "fun r -> choose({r with x := zero}, {r with y := one})";
  [%expect {|
    fun r -> choose({ r with x := zero }, { r with y := one })
    : { x: int; y: int; a } -> { x: int; y: int; a }
    | |}]

let%expect_test "" = infer "let f = fun x -> x.t(one) in f({t = succ})";
  [%expect {|
    let f = fun x -> x.t(one) in f({ t = succ })
    : int
    | |}]

let%expect_test "" = infer "let f = fun x -> x.t(one) in f({t = id})";
  [%expect {|
    let f = fun x -> x.t(one) in f({ t = id })
    : int
    | |}]

let%expect_test "" = infer "{x = one; x = true}";
  [%expect {|
    { x = one; x = true }
    : { x: bool; x: int;  }
    | |}]

let%expect_test "" =
  infer "let f = fun r -> let y = r.y in choose(r, {x = one; x = true}) in f";
  [%expect {|
    let f = fun r -> let y = r.y in choose(r, { x = one; x = true }) in f
    ERROR: unification error of
      {  }
    with
      { y: _2; _6 }
    | |}]

let%expect_test "" =
  infer "fun r -> choose({r with x = zero}, {x = true; x = one})";
  [%expect {|
    fun r -> choose({ r with x = zero }, { x = true; x = one })
    : { x: bool;  } -> { x: int; x: bool;  }
    | |}]

let%expect_test "" =
  infer "fun r -> choose({r with x := zero}, {x = true; x = one})";
  [%expect {|
    fun r -> choose({ r with x := zero }, { x = true; x = one })
    : { x: int; x: bool;  } -> { x: int; x: bool;  }
    | |}]

let%expect_test "" = infer "fun r -> choose(r, {x = one; x = true})";
  [%expect {|
    fun r -> choose(r, { x = one; x = true })
    : { x: bool; x: int;  } -> { x: bool; x: int;  }
    | |}]

let%expect_test "" =
  infer "fun r -> choose({r with x = zero}, {r with x = true})";
  [%expect {|
    fun r -> choose({ r with x = zero }, { r with x = true })
    ERROR: unification error of
      bool
    with
      int
    | |}]

let%expect_test "" =
  infer "fun r -> choose({r with x := zero}, {r with x := true})";
  [%expect {|
    fun r -> choose({ r with x := zero }, { r with x := true })
    ERROR: unification error of
      int
    with
      bool
    | |}]
