open! Base

type name = string

type lvl = int

type id = int

module Ty_var_unbound = struct
  type t = { id : id; lvl : lvl }

  include Comparator.Make (struct
    type nonrec t = t

    let sexp_of_t { id; lvl } =
      Sexp.List [ Sexp.Atom (Int.to_string id); Sexp.Atom (Int.to_string lvl) ]

    let compare a b = Int.compare a.id b.id
  end)
end

type expr =
  | Expr_name of name
  | Expr_abs of name list * expr
  | Expr_app of expr * expr list
  | Expr_lit of lit
  | Expr_let of name * expr * expr
  | Expr_let_rec of name * expr * expr
  | Expr_record of (name * expr) list
  | Expr_record_proj of expr * name
  | Expr_record_extend of expr * (name * expr) list
  | Expr_record_update of expr * (name * expr) list

and lit = Lit_string of string | Lit_int of int

type ty =
  | Ty_const of name
  | Ty_var of ty var ref
  | Ty_app of ty * ty list
  | Ty_arr of ty list * ty
  | Ty_record of ty_row

and 'a var =
  | Ty_var_unbound of Ty_var_unbound.t
  | Ty_var_link of 'a
  | Ty_var_generic of id

and ty_row =
  | Ty_row_field of string * ty * ty_row
  | Ty_row_empty
  | Ty_row_var of ty_row var ref
  | Ty_row_const of string

and pred = string * ty list

and qual_ty = pred list * ty

and qual_pred = pred list * pred

let is_simple_expr = function
  | Expr_abs _
  | Expr_let_rec _
  | Expr_let _
  | Expr_record _
  | Expr_record_extend _
  | Expr_record_update _
  | Expr_lit _ ->
    false
  | Expr_app _
  | Expr_name _
  | Expr_record_proj _ ->
    true

let generic_ty_vars ty =
  let rec of_ty set = function
    | Ty_const _ -> set
    | Ty_arr (args, ret) -> List.fold args ~init:(of_ty set ret) ~f:of_ty
    | Ty_app (f, args) -> List.fold args ~init:(of_ty set f) ~f:of_ty
    | Ty_var { contents = Ty_var_link ty } -> of_ty set ty
    | Ty_var { contents = Ty_var_unbound _ } -> set
    | Ty_var { contents = Ty_var_generic id } -> Set.add set id
    | Ty_record row -> of_ty_row set row
  and of_ty_row set = function
    | Ty_row_empty -> set
    | Ty_row_var { contents = Ty_var_link ty_row } -> of_ty_row set ty_row
    | Ty_row_var { contents = Ty_var_unbound _ } -> set
    | Ty_row_var { contents = Ty_var_generic id } -> Set.add set id
    | Ty_row_const _ -> set
    | Ty_row_field (_, _, ty_row) -> of_ty_row set ty_row
  in
  of_ty (Set.empty (module Int)) ty

let rec layout_expr =
  let open PPrint in
  function
  | Expr_name name -> string name
  | Expr_abs ([ arg ], body) ->
    string "fun " ^^ string arg ^^ string " -> " ^^ group (layout_expr body)
  | Expr_abs (args, body) ->
    let sep = comma ^^ blank 1 in
    string "fun "
    ^^ parens (separate sep (List.map args ~f:string))
    ^^ string " -> "
    ^^ group (layout_expr body)
  | Expr_app (f, args) ->
    let sep = comma ^^ blank 1 in
    layout_expr f ^^ parens (separate sep (List.map args ~f:layout_expr))
  | Expr_lit (Lit_string v) -> dquotes (string v)
  | Expr_lit (Lit_int v) -> dquotes (string (Int.to_string v))
  | Expr_let (n, e, b) ->
    surround 2 1
      (string "let " ^^ string n ^^ string " =")
      (layout_expr e)
      (string "in " ^^ layout_expr b)
  | Expr_let_rec (n, e, b) ->
    surround 2 1
      (string "let rec " ^^ string n ^^ string " =")
      (layout_expr e)
      (string "in " ^^ layout_expr b)
  | Expr_record fields ->
    let sep = string ";" ^^ blank 1 in
    let f (n, e) = string n ^^ string " = " ^^ layout_expr e in
    surround 2 1 (string "{") (separate sep (List.map fields ~f)) (string "}")
  | Expr_record_proj (e, n) ->
    let head =
      if is_simple_expr e then layout_expr e else parens (layout_expr e)
    in
    head ^^ string "." ^^ string n
  | Expr_record_extend (e, fields) ->
    let sep = string ";" ^^ blank 1 in
    let f (n, e) = string n ^^ string " = " ^^ layout_expr e in
    surround 2 1 (string "{")
      (layout_expr e ^^ string " with " ^^ separate sep (List.map fields ~f))
      (string "}")
  | Expr_record_update (e, fields) ->
    let sep = string ";" ^^ blank 1 in
    let f (n, e) = string n ^^ string " := " ^^ layout_expr e in
    surround 2 1 (string "{")
      (layout_expr e ^^ string " with " ^^ separate sep (List.map fields ~f))
      (string "}")

let make_names () =
  let names = Hashtbl.create (module Int) in
  let count = ref 0 in
  let genname () =
    let i = !count in
    Int.incr count;
    let name =
      String.make 1 (Char.of_int_exn (97 + Int.rem i 26))
      ^ if i >= 26 then Int.to_string (i / 26) else ""
    in
    name
  in
  fun id -> Hashtbl.find_or_add names id ~default:genname

let layout_ty' ~lookup_name ty =
  let open PPrint in
  let rec layout_ty = function
    | Ty_const name -> string name
    | Ty_arr ([ (Ty_arr _ as arg) ], ret) ->
      parens (layout_ty arg) ^^ string " -> " ^^ layout_ty ret
    | Ty_arr ([ arg ], ret) -> layout_ty arg ^^ string " -> " ^^ layout_ty ret
    | Ty_arr (args, ret) ->
      let sep = comma ^^ blank 1 in
      parens (separate sep (List.map args ~f:layout_ty))
      ^^ string " -> "
      ^^ layout_ty ret
    | Ty_app (f, args) ->
      let sep = comma ^^ blank 1 in
      layout_ty f ^^ brackets (separate sep (List.map args ~f:layout_ty))
    | Ty_var { contents } -> layout_ty_var layout_ty contents
    | Ty_record row ->
      let rec layout_ty_row = function
        | Ty_row_empty -> empty
        | Ty_row_field (name, ty, row) -> (
          string name
          ^^ string ": "
          ^^ layout_ty ty
          ^^
          match row with
          | Ty_row_empty -> string ";"
          | row -> string "; " ^^ layout_ty_row row)
        | Ty_row_var { contents } -> layout_ty_var layout_ty_row contents
        | Ty_row_const _ -> assert false
      in
      surround 2 1 (string "{") (layout_ty_row row) (string "}")
  and layout_ty_var : 'a. ('a -> document) -> 'a var -> document =
   fun layout_v -> function
    | Ty_var_link v -> layout_v v
    | Ty_var_generic id -> string (lookup_name id)
    | Ty_var_unbound { id; lvl = _ } -> string ("_" ^ Int.to_string id)
  in
  layout_ty ty

let layout_forall' ~lookup_name ty_vars =
  let open PPrint in
  if Set.is_empty ty_vars then empty
  else
    let layout_ty_var id = string (lookup_name id) in
    let sep = comma ^^ blank 1 in
    separate sep (Set.to_list ty_vars |> List.map ~f:layout_ty_var)
    ^^ blank 1
    ^^ dot
    ^^ blank 1

let layout_pred' ~lookup_name (name, args) =
  let open PPrint in
  let sep = comma ^^ blank 1 in
  string name
  ^^ parens (separate sep (List.map args ~f:(layout_ty' ~lookup_name)))

let layout_ty ty =
  let lookup_name = make_names () in
  let ty_vars = generic_ty_vars ty in
  let open PPrint in
  layout_forall' ~lookup_name ty_vars ^^ layout_ty' ~lookup_name ty

let layout_pred p =
  let lookup_name = make_names () in
  layout_pred' ~lookup_name p

let layout_qual_ty qty =
  let open PPrint in
  let lookup_name = make_names () in
  let ty_vars =
    let ps, ty = qty in
    let init = generic_ty_vars ty in
    List.fold ps ~init ~f:(fun init (_, args) ->
        List.fold args ~init ~f:(fun set ty ->
            Set.union set (generic_ty_vars ty)))
  in
  layout_forall' ~lookup_name ty_vars
  ^^
  match qty with
  | [], ty -> layout_ty' ~lookup_name ty
  | cs, ty ->
    let sep = comma ^^ blank 1 in
    separate sep (List.map cs ~f:(layout_pred' ~lookup_name))
    ^^ string " => "
    ^^ layout_ty' ~lookup_name ty

let layout_qual_pred qp =
  let lookup_name = make_names () in
  let open PPrint in
  match qp with
  | [], pred -> layout_pred' ~lookup_name pred
  | cs, pred ->
    let sep = comma ^^ blank 1 in
    separate sep (List.map cs ~f:(layout_pred' ~lookup_name))
    ^^ string " => "
    ^^ layout_pred' ~lookup_name pred

let pp' doc ppf v = PPrint.ToFormatter.pretty 1. 80 ppf (doc v)

let show' ?(width = 80) doc v =
  let buf = Buffer.create 100 in
  PPrint.ToBuffer.pretty 1. width buf (doc v);
  Buffer.contents buf

let print' doc v = Stdlib.print_endline (show' doc v)

let pp_expr = pp' layout_expr

let show_expr = show' layout_expr

let print_expr = print' layout_expr

let pp_qual_ty = pp' layout_qual_ty

let show_qual_ty = show' layout_qual_ty

let print_qual_ty = print' layout_qual_ty

let pp_pred = pp' layout_pred

let show_pred = show' layout_pred

let print_pred = print' layout_pred

let pp_qual_pred = pp' layout_qual_pred

let show_qual_pred = show' layout_qual_pred

let print_qual_pred = print' layout_qual_pred
