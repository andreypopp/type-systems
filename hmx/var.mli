open! Base
open Syntax

type t = var

val fresh : ?lvl:lvl -> unit -> t

val reset : unit -> unit

val equal : t -> t -> bool

val compare : t -> t -> int

val hash : t -> int

val sexp_of_t : t -> Sexp.t

val show : t -> string

val lvl : t -> lvl

val set_lvl : lvl -> t -> unit

val ty : t -> ty option

val set_ty : ty -> t -> unit

val unify : t -> t -> (ty * ty) option

val occurs_check_adjust_lvl : t -> ty -> unit
