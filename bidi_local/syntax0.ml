open! Import

type name = string [@@deriving sexp_of]

and id = int

and lvl = int

type variance = Covariant | Contravariant | Invariant [@@deriving sexp_of]

type ty =
  | Ty_const of name
  | Ty_var of var
  | Ty_app of ty * ty list
  | Ty_nullable of ty
  | Ty_arr of ty list * ty
  | Ty_bot
  | Ty_top

and var = var' Union_find.t

and var' = {
  id : int;
  mutable name : string option;
  mutable lvl : lvl option;
  mutable ty : ty option;
  mutable variance : variance option;
  mutable lower : ty;
  mutable upper : ty;
}
[@@deriving sexp_of]

type expr =
  | E_var of name
  | E_abs of var list * (name * ty option) list * expr
  | E_app of expr * expr list
  | E_let of (name * expr * ty_sch option) * expr
  | E_lit of lit
  | E_ann of expr * ty_sch
[@@deriving sexp_of]

and lit = Lit_string of string | Lit_int of int

and ty_sch = var list * ty
