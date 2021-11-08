(** Type variable substitutions. *)

open! Base
open! Syntax

type t

val empty : t

val add_var : t -> var -> ty -> t

val add_name : t -> name -> ty -> t

val apply_ty : t -> ty -> ty
