open! Base

type name = string [@@deriving sexp_of]

type id = int [@@deriving sexp_of]

type lvl = int [@@deriving sexp_of]

type expr =
  | E_var of name
  | E_abs of name list * expr
  | E_app of expr * expr list
  | E_let of name * expr * expr
  | E_lit of lit

and lit = Lit_string of string | Lit_int of int [@@deriving sexp_of]

type ty =
  | Ty_const of name
  | Ty_var of var
  | Ty_app of ty * ty list
  | Ty_arr of ty list * ty
[@@deriving sexp_of]

and con =
  | C_trivial
  | C_eq of ty * ty
  | C_and of con list
  | C_exists of var list * con
  | C_let of (name * ty_sch) list * con
  | C_inst of name * ty

and var = var_data Union_find.t

and var_data = { id : int; mutable ty : ty option; mutable lvl : lvl option }

and cty = con * ty

and ty_sch = var list * cty

module Names : sig
  type t

  val make : unit -> t

  val alloc : t -> id -> string

  val lookup : t -> id -> string option
end = struct
  type t = (Int.t, string) Hashtbl.t

  let make () = Hashtbl.create (module Int)

  let alloc names id =
    let i = Hashtbl.length names in
    let name =
      String.make 1 (Char.of_int_exn (97 + Int.rem i 26))
      ^ if i >= 26 then Int.to_string (i / 26) else ""
    in
    Hashtbl.set names ~key:id ~data:name;
    name

  let lookup names id = Hashtbl.find names id
end

module Id = struct
  let c = ref 0

  let fresh () =
    Int.incr c;
    !c

  let reset () = c := 0
end

module Showable (S : sig
  type t

  val layout : t -> PPrint.document

  val sexp_of_t : t -> Sexp.t
end) =
struct
  let layout = S.layout

  let show v =
    let width = 80 in
    let buf = Buffer.create 100 in
    PPrint.ToBuffer.pretty 1. width buf (S.layout v);
    Buffer.contents buf

  let print ?label v =
    match label with
    | Some label -> Caml.print_endline (label ^ ": " ^ show v)
    | None -> Caml.print_endline (show v)

  let pp ppf v = PPrint.ToFormatter.pretty 1. 80 ppf (S.layout v)

  let dump ?label v =
    let s = S.sexp_of_t v in
    match label with
    | None -> Caml.Format.printf "%a@." Sexp.pp_hum s
    | Some label -> Caml.Format.printf "%s %a@." label Sexp.pp_hum s
end

let layout_var v =
  let open PPrint in
  let lvl = Option.(v.lvl |> map ~f:Int.to_string |> value ~default:"!") in
  if Debug.log_levels then string (Printf.sprintf "_%i@%s" v.id lvl)
  else string (Printf.sprintf "_%i" v.id)

let rec layout_con_var' ~names v =
  let open PPrint in
  match v.ty with
  | Some ty -> layout_ty' ~names ty
  | None -> (
    match Names.lookup names v.id with
    | Some name -> string name
    | None -> layout_var v)

and layout_ty' ~names ty =
  let open PPrint in
  let rec is_ty_arr = function
    | Ty_var var -> (
      match (Union_find.value var).ty with
      | None -> false
      | Some ty -> is_ty_arr ty)
    | Ty_arr _ -> true
    | _ -> false
  in
  let rec layout_ty = function
    | Ty_const name -> string name
    | Ty_arr ([ aty ], rty) ->
      (* Check if we can layout this as simply as [aty -> try] in case of a
         single argument. *)
      (if is_ty_arr aty then
       (* If the single arg is the Ty_arr we need to wrap it in parens. *)
       parens (layout_ty aty)
      else layout_ty aty)
      ^^ string " -> "
      ^^ layout_ty rty
    | Ty_arr (atys, rty) ->
      let sep = comma ^^ blank 1 in
      parens (separate sep (List.map atys ~f:layout_ty))
      ^^ string " -> "
      ^^ layout_ty rty
    | Ty_app (fty, atys) ->
      let sep = comma ^^ blank 1 in
      layout_ty fty ^^ brackets (separate sep (List.map atys ~f:layout_ty))
    | Ty_var var -> (
      let data = Union_find.value var in
      match data.ty with
      | None -> layout_con_var' ~names data
      | Some ty -> layout_ty ty)
  in
  layout_ty ty

let rec layout_con' ~names c =
  let open PPrint in
  match c with
  | C_trivial -> string "TRUE"
  | C_eq (ty1, ty2) ->
    layout_ty' ~names ty1 ^^ string " = " ^^ layout_ty' ~names ty2
  | C_and cs ->
    let sep = string " & " in
    separate sep (List.map cs ~f:(layout_con' ~names))
  | C_exists (vs, c) ->
    string "∃"
    ^^ separate comma
         (List.map vs ~f:(fun v ->
              let v = Union_find.value v in
              layout_con_var' ~names v))
    ^^ dot
    ^^ parens (layout_con' ~names c)
  | C_let (bindings, c) ->
    let layut_binding (name, ty_sch) =
      string name ^^ string " : " ^^ layout_ty_sch ty_sch
    in
    let sep = comma ^^ blank 1 in
    string "let "
    ^^ separate sep (List.map bindings ~f:layut_binding)
    ^^ string " in "
    ^^ layout_con' ~names c
  | C_inst (name, ty) -> string name ^^ string " ≲ " ^^ layout_ty' ~names ty

and layout_cty' ~names cty =
  let open PPrint in
  match cty with
  | C_trivial, ty -> layout_ty' ~names ty
  | c, ty -> layout_con' ~names c ^^ string " => " ^^ layout_ty' ~names ty

and layout_ty_sch ty_sch =
  let open PPrint in
  let names = Names.make () in
  match ty_sch with
  | [], cty -> layout_cty' ~names cty
  | vs, cty ->
    let sep = comma ^^ blank 1 in
    let vars =
      List.map vs ~f:(fun v ->
          let v = Union_find.value v in
          string (Names.alloc names v.id))
    in
    separate sep vars ^^ string " . " ^^ layout_cty' ~names cty

module Expr = struct
  type t = expr

  include Showable (struct
    type t = expr

    let sexp_of_t = sexp_of_expr

    let rec layout =
      let open PPrint in
      function
      | E_var name -> string name
      | E_abs ([ arg ], body) ->
        string "fun " ^^ string arg ^^ string " -> " ^^ group (layout body)
      | E_abs (args, body) ->
        let sep = comma ^^ blank 1 in
        string "fun "
        ^^ parens (separate sep (List.map args ~f:string))
        ^^ string " -> "
        ^^ group (layout body)
      | E_app (f, args) ->
        let sep = comma ^^ blank 1 in
        layout f ^^ parens (separate sep (List.map args ~f:layout))
      | E_let (name, e, b) ->
        string "let "
        ^^ string name
        ^^ string " = "
        ^^ layout e
        ^^ string " in "
        ^^ layout b
      | E_lit (Lit_string v) -> dquotes (string v)
      | E_lit (Lit_int v) -> dquotes (string (Int.to_string v))
  end)
end

module Ty = struct
  type t = ty

  let arr a b = Ty_arr (a, b)

  let var var = Ty_var var

  include Showable (struct
    type t = ty

    let sexp_of_t = sexp_of_ty

    let layout ty =
      let names = Names.make () in
      layout_ty' ~names ty
  end)
end

module C = struct
  type t = con

  let trivial = C_trivial

  let ( =~ ) x y = C_eq (x, y)

  let inst name cty = C_inst (name, cty)

  let fresh_var ?lvl () : var =
    let id = Id.fresh () in
    Union_find.make { ty = None; lvl; id }

  let exists tys c =
    match tys with
    | [] -> c
    | tys -> (
      match c with
      | C_exists (tys', c) -> C_exists (tys @ tys', c)
      | c -> C_exists (tys, c))

  let ( &~ ) x y =
    match (x, y) with
    | c, C_trivial -> c
    | C_trivial, c -> c
    | C_and xs, C_and ys -> C_and (xs @ ys)
    | C_and xs, x -> C_and (x :: xs)
    | x, C_and xs -> C_and (x :: xs)
    | x, y -> C_and [ x; y ]

  let let_in bindings c =
    match bindings with
    | [] -> c
    | bindings ->
      (* let cs = *)
      (*   List.fold bindings ~init:trivial ~f:(fun c (_, ty_sch) -> *)
      (*       let vs, (c', _) = ty_sch in *)
      (*       exists vs c' &~ c) *)
      (* in *)
      C_let (bindings, c)

  include Showable (struct
    type t = con

    let sexp_of_t = sexp_of_con

    let layout c =
      let names = Names.make () in
      layout_con' ~names c
  end)
end

module Cty = struct
  type t = cty

  include Showable (struct
    type t = cty

    let sexp_of_t = sexp_of_cty

    let layout cty =
      let names = Names.make () in
      layout_cty' ~names cty
  end)
end

module Ty_sch = struct
  type t = ty_sch

  include Showable (struct
    type t = ty_sch

    let sexp_of_t = sexp_of_ty_sch

    let layout = layout_ty_sch
  end)
end
