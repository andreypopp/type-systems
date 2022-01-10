(** Layout data structures in a human readable way.

    This module is designed to be openned.
  *)

open! Import
open! Syntax0

include module type of PPrint
(** We include all pprint API. *)

type 'a t
(** Computation which can allocate and lookup names. *)

val alloc_var : var -> string t
(** Allocate name for a variable. *)

val lookup_var : var -> string option t
(** Lookup name for a variable. *)

type names

val names : names t
(** Get names at current position. *)

val closed : ?names:names -> 'a t -> 'a t
(** Closed term which doesn't leak names outside. *)

include Monad.S with type 'a t := 'a t
(** ['a t] is a monad. *)

include Monad.MONAD_SYNTAX with type 'a t := 'a t

val list_map : 'a list -> f:('a -> 'b t) -> 'b list t
(** Map with a monadic action over a list of items. *)

type layout = document t
(** A layout is a computation which produces a document. *)

val render : layout -> document
(** Render layout into a document. *)

val to_string : layout -> string

(** Colors *)

type color = Black | Red | Green | Yellow | Blue | Magenta | Cyan | White

val bold : document -> document

val fg : color -> document -> document

val enable_colors : bool -> unit
