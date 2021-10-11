# type-systems

This is an experiment in designing a type system for Rel/FunSQL.

The core is the [Hindley-Milner][] type system, this is the one used as a basis
for OCaml, StandardML and other ML-descendants. It features whole program type
inference (you don't need to specify any types, although you can), principality
(the most general type is inferred), parametric polymorphism (generics) and
let-polymorphism (terms defined with `let` syntax are inferred to have a
polymorphic types). Also there's support for `let rec` so it's possible to type
recursion.

On top of that extensible records are *implemented*, so that it is possible to
write functions which accept records of a known partial shapes leaving the
complete shapes unknown to the caller. The design follows [Extensible records
with scoped labels][] paper.

Extensible records are going to be used for several purposes:

1. Modelling scopes in Rel queries, the `DEFINE` Rel combinator will be typed as
   a record extension (it adds a new binding in scope with shadowing).

2. Modelling records as values in Expr, such records will be non-extensible (the
   shape will be fixed at the moment of creation, although it will still be
   possible to write functions which operate on a subset of a record's fields).

For dealing with overloading and type casting qualified types typeclasses are
used. We are going to support a closed set of typeclasses at the moment.

The code is heavily based on [tomprimozic/type-systems][].

[Simple-Sub]: https://lptk.github.io/simple-sub-paper
[Hindley-Milner]: https://en.wikipedia.org/wiki/Hindley–Milner_type_system
[Extensible records with scoped labels]: https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/scopedlabels.pdf
[tomprimozic/type-systems]: https://github.com/tomprimozic/type-systems
