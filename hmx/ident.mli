open! Import

type t

val name : t -> string

val make : string -> t

val equal : t -> t -> bool

val compare : t -> t -> int

val sexp_of_t : t -> Sexp.t

include Comparator.S with type t := t

include SHOWABLE with type t := t
