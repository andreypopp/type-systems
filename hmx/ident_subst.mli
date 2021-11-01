open! Import
open Syntax

type t

val empty : t

val add : t -> name -> Path.t -> t

val merge : t -> t -> t

val prefix : Path.t -> t -> t

val prefix_image : Path.t -> t -> t

val subst_path : t -> Path.t -> Path.t

val subst_ty : t -> ty -> ty

val subst_ty_sch : t -> ty_sch -> ty_sch

include SHOWABLE with type t := t
