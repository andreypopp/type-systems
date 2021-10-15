(lang dune 2.9)
(name type-systems)
(using menhir 2.1)
(generate_opam_files true)

(package
 (name type-systems)
 (synopsis "Type Systems Toy Implementations")
 (depends
  (dune (>= 2.8))
  menhir
  pprint
  nice_parser
  ppx_sexp_conv
  ppx_expect
  base))
