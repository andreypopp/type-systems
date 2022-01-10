(** Type variable substitutions. *)

open! Base
open! Syntax

type t

val empty : t

val add_var : t -> var -> var -> t

val add_name : t -> name -> var -> t

val apply_ty : variance:Variance.t -> t -> ty -> ty
