open! Base

type name = string [@@deriving sexp_of]

type id = int [@@deriving sexp_of]

type lvl = int [@@deriving sexp_of]

type expr =
  | E_var of name
  | E_abs of name list * expr
  | E_app of expr * expr list
  | E_let of (name * expr * ty_sch option ref) * expr
  | E_lit of lit

and lit = Lit_string of string | Lit_int of int [@@deriving sexp_of]

and ty =
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
  | C_let of (name * ty_sch * ty_sch option ref) list * con
  | C_inst of name * ty

and var = var_data Union_find.t

and var_data = {
  id : int;
  mutable lvl : lvl option;
      (** Levels are assigned when we enter [C_exists] or [C_let] constraints *)
  mutable ty : ty option;
      (** Types are discovered as a result of unification. *)
}

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
    let width = 60 in
    let buf = Buffer.create 100 in
    PPrint.ToBuffer.pretty 1. width buf (S.layout v);
    Buffer.contents buf

  let print ?label v =
    match label with
    | Some label -> Caml.print_endline (label ^ ": " ^ show v)
    | None -> Caml.print_endline (show v)

  let pp ppf v = PPrint.ToFormatter.pretty 1. 60 ppf (S.layout v)

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
    | Some name ->
      if Debug.log_levels then string name ^^ parens (layout_var v)
      else string name
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
    let layout_binding (name, ty_sch, _) =
      string name ^^ string " : " ^^ layout_ty_sch' ~names ty_sch
    in
    let sep = comma ^^ blank 1 in
    string "let "
    ^^ separate sep (List.map bindings ~f:layout_binding)
    ^^ string " in "
    ^^ layout_con' ~names c
  | C_inst (name, ty) -> string name ^^ string " ≲ " ^^ layout_ty' ~names ty

and layout_cty' ~names cty =
  let open PPrint in
  match cty with
  | C_trivial, ty -> layout_ty' ~names ty
  | c, ty -> layout_con' ~names c ^^ string " => " ^^ layout_ty' ~names ty

and layout_ty_sch' ~names ty_sch =
  let open PPrint in
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

and layout_expr' ~names =
  let open PPrint in
  function
  | E_var name -> string name
  | E_abs (args, body) ->
    let sep = comma ^^ blank 1 in
    let newline =
      (* Always break on let inside the body. *)
      match body with
      | E_let _ -> hardline
      | _ -> break 1
    in
    let args =
      match args with
      | [ arg ] -> string arg
      | args -> parens (separate sep (List.map args ~f:string))
    in
    group
      (group (string "fun " ^^ args ^^ string " ->")
      ^^ nest 2 (group (newline ^^ group (layout_expr' ~names body))))
  | E_app (f, args) ->
    let sep = comma ^^ blank 1 in
    layout_expr' ~names f
    ^^ parens (separate sep (List.map args ~f:(layout_expr' ~names)))
  | E_let _ as e ->
    let es =
      (* We do not want to print multiple nested let-expression with indents and
         therefore we linearize them first and print on the same indent instead. *)
      let rec linearize es e =
        match e with
        | E_let (_, b) -> linearize (e :: es) b
        | e -> e :: es
      in
      List.rev (linearize [] e)
    in
    let newline =
      (* If there's more than a single let-expression found (checking length > 2
         because es containts the body of the last let-expression too) we split
         them with a hardline. *)
      if List.length es > 2 then hardline else break 1
    in
    concat
      (List.map es ~f:(function
        | E_let ((name, expr, ty_sch), _) ->
          let ascription =
            (* We need to layout ty_sch first as it will allocate names for use
               down the road. *)
            match ty_sch.contents with
            | None -> empty
            | Some ty_sch -> string " : " ^^ layout_ty_sch' ~names ty_sch
          in
          let expr_newline =
            (* If there's [let x = let y = ... in ... in ...] then we want to
               force break. *)
            match expr with
            | E_let _ -> hardline
            | _ -> break 1
          in
          group
            (group (string "let " ^^ string name ^^ ascription ^^ string " =")
            ^^ nest 2 (expr_newline ^^ layout_expr' ~names expr)
            ^^ expr_newline
            ^^ string "in")
          ^^ newline
        | e -> layout_expr' ~names e))
  | E_lit (Lit_string v) -> dquotes (string v)
  | E_lit (Lit_int v) -> dquotes (string (Int.to_string v))

module Expr = struct
  type t = expr

  include Showable (struct
    type t = expr

    let sexp_of_t = sexp_of_expr

    let layout e =
      let names = Names.make () in
      layout_expr' ~names e
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

  let let_in bindings c =
    match bindings with
    | [] -> c
    | bindings -> C_let (bindings, c)

  let ( &~ ) x y =
    match (x, y) with
    | c, C_trivial -> c
    | C_trivial, c -> c
    | C_and xs, C_and ys -> C_and (xs @ ys)
    | C_and xs, x -> C_and (x :: xs)
    | x, C_and xs -> C_and (x :: xs)
    | x, y -> C_and [ x; y ]

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

    let layout =
      let names = Names.make () in
      layout_ty_sch' ~names
  end)
end
