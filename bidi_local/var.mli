open! Import
open! Syntax

type t = var

val fresh : ?name:string -> ?lvl:lvl -> unit -> t

val refresh : ?lvl:lvl -> t -> t

val reset : unit -> unit

val layout : t -> Layout.layout

include SHOWABLE with type t := t

val sexp_of_t : t -> Sexp.t

val equal : t -> t -> bool

val compare : t -> t -> int

val is_empty : t -> bool

val union :
  merge_lower:(ty -> ty -> ty) -> merge_upper:(ty -> ty -> ty) -> t -> t -> unit

val name : t -> name

val lvl : t -> lvl

val ty : t -> ty option

val set_ty : t -> ty -> unit

val variance : t -> Variance.t

val set_variance : t -> Variance.t -> unit
