open! Base

type expr =
  | Expr_name of name
  | Expr_abs of name list * expr
  | Expr_app of expr * expr list
  | Expr_lit of lit
  | Expr_let of name * expr * expr

and lit = Lit_string of string | Lit_int of int

and name = string

type ty =
  | Ty_const of name
  | Ty_var of ty_var ref
  | Ty_app of ty * ty list
  | Ty_arr of ty list * ty

and ty_var =
  Ty_var_unbound of id | Ty_var_link of ty | Ty_var_generic of id

and id = int

let rec doc_of_expr =
  let open PPrint in
  function
  | Expr_name name -> string name
  | Expr_abs ([ arg ], body) ->
    string "fun " ^^ string arg ^^ string " -> " ^^ group (doc_of_expr body)
  | Expr_abs (args, body) ->
    string "fun "
    ^^ parens (separate comma (List.map args ~f:string))
    ^^ string " -> "
    ^^ group (doc_of_expr body)
  | Expr_app (f, args) ->
    doc_of_expr f ^^ parens (separate comma (List.map args ~f:doc_of_expr))
  | Expr_lit (Lit_string v) -> dquotes (string v)
  | Expr_lit (Lit_int v) -> dquotes (string (Int.to_string v))
  | Expr_let (n, e, b) ->
    surround 2 1
      (string "let " ^^ string n ^^ string " =")
      (doc_of_expr e)
      (string "in " ^^ doc_of_expr b)

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
  let rec aux =
    let open PPrint in
    function
    | Ty_const name -> string name
    | Ty_arr ([ arg ], ret) -> aux arg ^^ string " -> " ^^ aux ret
    | Ty_arr (args, ret) ->
      parens (separate comma (List.map args ~f:aux)) ^^ string " -> " ^^ aux ret
    | Ty_app (f, args) ->
      aux f ^^ parens (separate comma (List.map args ~f:aux))
    | Ty_var { contents = Ty_var_link ty } -> aux ty
    | Ty_var { contents = Ty_var_generic id } -> string (lookup_name id)
    | Ty_var { contents = Ty_var_unbound id } -> string ("_" ^ Int.to_string id)
  in
  aux ty

let show' ?(width = 80) doc v =
  let buf = Buffer.create 100 in
  PPrint.ToBuffer.pretty 1. width buf (doc v);
  Buffer.contents buf

let show_expr = show' doc_of_expr

let show_ty = show' doc_of_ty
