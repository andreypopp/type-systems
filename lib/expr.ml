open! Base

type name = string

type lvl = int

type id = int

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
  | Ty_var_unbound of { id : id; lvl : int }
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

let rec doc_of_expr =
  let open PPrint in
  function
  | Expr_name name -> string name
  | Expr_abs ([ arg ], body) ->
    string "fun " ^^ string arg ^^ string " -> " ^^ group (doc_of_expr body)
  | Expr_abs (args, body) ->
    let sep = comma ^^ blank 1 in
    string "fun "
    ^^ parens (separate sep (List.map args ~f:string))
    ^^ string " -> "
    ^^ group (doc_of_expr body)
  | Expr_app (f, args) ->
    let sep = comma ^^ blank 1 in
    doc_of_expr f ^^ parens (separate sep (List.map args ~f:doc_of_expr))
  | Expr_lit (Lit_string v) -> dquotes (string v)
  | Expr_lit (Lit_int v) -> dquotes (string (Int.to_string v))
  | Expr_let (n, e, b) ->
    surround 2 1
      (string "let " ^^ string n ^^ string " =")
      (doc_of_expr e)
      (string "in " ^^ doc_of_expr b)
  | Expr_let_rec (n, e, b) ->
    surround 2 1
      (string "let rec " ^^ string n ^^ string " =")
      (doc_of_expr e)
      (string "in " ^^ doc_of_expr b)
  | Expr_record fields ->
    let sep = string ";" ^^ blank 1 in
    let f (n, e) = string n ^^ string " = " ^^ doc_of_expr e in
    surround 2 1 (string "{") (separate sep (List.map fields ~f)) (string "}")
  | Expr_record_proj (e, n) ->
    let head =
      if is_simple_expr e then doc_of_expr e else parens (doc_of_expr e)
    in
    head ^^ string "." ^^ string n
  | Expr_record_extend (e, fields) ->
    let sep = string ";" ^^ blank 1 in
    let f (n, e) = string n ^^ string " = " ^^ doc_of_expr e in
    surround 2 1 (string "{")
      (doc_of_expr e ^^ string " with " ^^ separate sep (List.map fields ~f))
      (string "}")
  | Expr_record_update (e, fields) ->
    let sep = string ";" ^^ blank 1 in
    let f (n, e) = string n ^^ string " := " ^^ doc_of_expr e in
    surround 2 1 (string "{")
      (doc_of_expr e ^^ string " with " ^^ separate sep (List.map fields ~f))
      (string "}")

let doc_of_ty ty =
  let lookup_name =
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
  in
  let open PPrint in
  let rec doc_of_ty = function
    | Ty_const name -> string name
    | Ty_arr ([ (Ty_arr _ as arg) ], ret) ->
      parens (doc_of_ty arg) ^^ string " -> " ^^ doc_of_ty ret
    | Ty_arr ([ arg ], ret) -> doc_of_ty arg ^^ string " -> " ^^ doc_of_ty ret
    | Ty_arr (args, ret) ->
      let sep = comma ^^ blank 1 in
      parens (separate sep (List.map args ~f:doc_of_ty))
      ^^ string " -> "
      ^^ doc_of_ty ret
    | Ty_app (f, args) ->
      let sep = comma ^^ blank 1 in
      doc_of_ty f ^^ brackets (separate sep (List.map args ~f:doc_of_ty))
    | Ty_var { contents } -> doc_of_ty_var doc_of_ty contents
    | Ty_record row ->
      let rec doc_of_ty_row = function
        | Ty_row_empty -> empty
        | Ty_row_field (name, ty, row) -> (
          string name
          ^^ string ": "
          ^^ doc_of_ty ty
          ^^
          match row with
          | Ty_row_empty -> string ";"
          | row -> string "; " ^^ doc_of_ty_row row)
        | Ty_row_var { contents } -> doc_of_ty_var doc_of_ty_row contents
        | Ty_row_const _ -> assert false
      in
      surround 2 1 (string "{") (doc_of_ty_row row) (string "}")
  and doc_of_ty_var : 'a. ('a -> document) -> 'a var -> document =
   fun doc_of_v -> function
    | Ty_var_link v -> doc_of_v v
    | Ty_var_generic id -> string (lookup_name id)
    | Ty_var_unbound { id; lvl = _ } -> string ("_" ^ Int.to_string id)
  in
  doc_of_ty ty

let doc_of_pred (name, args) =
  let open PPrint in
  let sep = comma ^^ blank 1 in
  string name ^^ parens (separate sep (List.map args ~f:doc_of_ty))

let doc_of_qual_ty qty =
  let open PPrint in
  match qty with
  | [], ty -> doc_of_ty ty
  | cs, ty ->
    let sep = comma ^^ blank 1 in
    separate sep (List.map cs ~f:doc_of_pred) ^^ string " => " ^^ doc_of_ty ty

let doc_of_qual_pred qp =
  let open PPrint in
  match qp with
  | [], pred -> doc_of_pred pred
  | cs, pred ->
    let sep = comma ^^ blank 1 in
    separate sep (List.map cs ~f:doc_of_pred)
    ^^ string " => "
    ^^ doc_of_pred pred

let pp' doc ppf v = PPrint.ToFormatter.pretty 1. 80 ppf (doc v)

let show' ?(width = 80) doc v =
  let buf = Buffer.create 100 in
  PPrint.ToBuffer.pretty 1. width buf (doc v);
  Buffer.contents buf

let print' doc v = Caml.print_endline (show' doc v)

let pp_expr = pp' doc_of_expr

let show_expr = show' doc_of_expr

let print_expr = print' doc_of_expr

let pp_ty = pp' doc_of_ty

let show_ty = show' doc_of_ty

let print_ty = print' doc_of_ty

let pp_qual_ty = pp' doc_of_qual_ty

let show_qual_ty = show' doc_of_qual_ty

let print_qual_ty = print' doc_of_qual_ty

let pp_pred = pp' doc_of_pred

let show_pred = show' doc_of_pred

let print_pred = print' doc_of_pred

let pp_qual_pred = pp' doc_of_qual_pred

let show_qual_pred = show' doc_of_qual_pred

let print_qual_pred = print' doc_of_qual_pred
