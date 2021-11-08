# type-systems

- `algo_w` - Algorithm W extended with "Extensible Records with Scoped Labels"
  and Multi Parameter Typeclasses.

  This follows closely [tomprimozic/type-systems] and then [THIH][] (Typing
  Haskell in Haskell).

- `hmx` - [HM(X)][] style implementation of Hindley Minler type inference.

  The main idea is to introduce constraint language and split the algo into two
  phases — first generate constraints from expression terms, then solve those
  constraints.

  This implementation also does elaboration, the `infer` function has the
  following signature:
  ```
  val infer : env:Env.t -> expr -> (expr, Error.t) result
  ```
  That means that `infer` returns return not the type of the expression but an
  elaborated expression (an original expression annotated with types).

  The elaboration mechanism is shamelessly stolen from [inferno][].

- `hmx_tc` - [HM(X)][] extends with Multi-Parameter Typeclasses (MPTC).
  Type inference and elaborator are implemented but the environment construction
  doesn't check for overlapping instances yet.

- `bidi_local` attempts to implement ["Local Type Inference"][bidi_local] by
  Piece and Turner.

  This is a bidirectional type checking mechanism where we alternate between
  checking mode (where we have type annotations available) and synthesis mode.

  Thus this requires type annotations for let-functions declarations.

  The type system supports subtyping (with `null`). The way it works is it
  collects lower/upper bound constraints for type variables and then synthesises
  the most general type for type variables at polymorphic abstraction
  elimination.


# Development

```
make init
make build
make test
```

# References

- https://en.wikipedia.org/wiki/Hindley–Milner_type_system
- https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/scopedlabels.pdf
- https://www.cs.tufts.edu/~nr/cs257/archive/martin-odersky/hmx.pdf
- https://web.cecs.pdx.edu/~mpj/thih/thih.pdf
- https://github.com/tomprimozic/type-systems
- https://gitlab.inria.fr/fpottier/inferno/
- https://github.com/naominitel/hmx

[HM(X)]: https://www.cs.tufts.edu/~nr/cs257/archive/martin-odersky/hmx.pdf
[inferno]: https://gitlab.inria.fr/fpottier/inferno/
[THIH]: https://web.cecs.pdx.edu/~mpj/thih/thih.pdf
[tomprimozic/type-systems]: https://github.com/tomprimozic/type-systems
[bidi_local]: https://www.cis.upenn.edu/~bcpierce/papers/lti-toplas.pdf
