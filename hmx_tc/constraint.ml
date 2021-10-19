(**

   This module defines constraint language.

   The constraint language has applicative structure (see [C_map] constructor)
   which is used for elaboration (the constraint solving algo computes a value).

 *)

open Base
open Syntax

type _ t =
  | C_trivial : unit t
      (** A trivial constraint, states nothing useful. Always can be solved. *)
  | C_eq : ty * ty -> unit t
      (** [C_eq (ty1, ty2)] states that the types [ty1] and [ty2] are equal. *)
  | C_inst : name * ty -> expr t
      (** [C_inst (name, ty)] states that [name] should be fetched from the
          environment, instantiated and equated to [ty]. *)
  | C_and : 'a t * 'b t -> ('a * 'b) t
      (** Conjuction of two constraints, possibly of different value type. *)
  | C_and_list : 'a t list -> 'a list t
      (** Conjuction of multiple constraints of the same value type. *)
  | C_exists : var list * 'a t -> 'a t
      (** [C_exists (vs, c)] existentially quantifies variables [vs] over [c]. *)
  | C_let :
      (name * var list * expr t * ty) list * 'b t
      -> ((expr * ty_sch) list * 'b) t
      (** [C_let (bindings, c)] works is a constraint abstraction fused with
          existential quantification. It adds [bindings] to the environment of
          the following constraint [c].

          It allows to define multiple names at once to support n-ary functions. *)
  | C_map : 'a t * ('a -> 'b) -> 'b t
      (** Map operation, this gives an applicative structure. *)

let trivial = C_trivial

let return v = C_map (C_trivial, fun () -> v)

let ( =~ ) x y = C_eq (x, y)

let inst name cty = C_inst (name, cty)

let exists tys c =
  match tys with
  | [] -> c
  | tys -> (
    match c with
    | C_exists (tys', c) -> C_exists (tys @ tys', c)
    | c -> C_exists (tys, c))

let let_in bindings c = C_let (bindings, c)

let ( &~ ) x y = C_and (x, y)

let ( >>| ) c f = C_map (c, f)

let list cs = C_and_list cs

let rec layout' : type a. names:Names.t -> a t -> PPrint.document =
 fun ~names c ->
  let open PPrint in
  match c with
  | C_trivial -> string "TRUE"
  | C_eq (ty1, ty2) ->
    layout_ty' ~names ty1 ^^ string " = " ^^ layout_ty' ~names ty2
  | C_and (a, b) -> layout' ~names a ^^ string " & " ^^ layout' ~names b
  | C_and_list cs ->
    let sep = string " & " in
    separate sep (List.map cs ~f:(layout' ~names))
  | C_exists (vs, c) ->
    string "∃"
    ^^ separate comma (List.map vs ~f:(layout_con_var' ~names))
    ^^ dot
    ^^ parens (layout' ~names c)
  | C_let (bindings, c) ->
    let layout_cty' : type a. a t * ty -> document = function
      | C_trivial, ty -> layout_ty' ~names ty
      | c, ty -> layout' ~names c ^^ string " => " ^^ layout_ty' ~names ty
    in
    let layout_binding : type a. string * var list * a t * ty -> document =
     fun (name, vs, c, ty) ->
      string name
      ^^ string " : "
      ^^
      match vs with
      | [] -> layout_cty' (c, ty)
      | vs ->
        let vs = layout_var_prenex' ~names vs in
        vs ^^ layout_cty' (c, ty)
    in
    let sep = comma ^^ blank 1 in
    string "let "
    ^^ separate sep (List.map bindings ~f:layout_binding)
    ^^ string " in "
    ^^ layout' ~names c
  | C_inst (name, ty) -> string name ^^ string " ≲ " ^^ layout_ty' ~names ty
  | C_map (c, _f) -> layout' ~names c

include (
  struct
    type pack = P : _ t -> pack

    include Showable (struct
      type t = pack

      let layout (P c) =
        let names = Names.make () in
        layout' ~names c
    end)

    let layout c = layout (P c)

    let show c = show (P c)

    let print ?label c = print ?label (P c)
  end :
    sig
      val layout : _ t -> PPrint.document

      val show : _ t -> string

      val print : ?label:string -> _ t -> unit
    end)
