%{

open Expr

let build_ty var_name_list ty =
  let open Base in
	let env = List.fold_left
	  var_name_list
	  ~init:(Map.empty (module String))
		~f:(fun env var_name -> Map.set env ~key:var_name ~data:(Infer.newgenvar ()))
	in
	let rec build_ty ty = match ty with
		| Ty_const name -> (
		  match Map.find env name with
      | Some ty -> ty
      | None -> ty)
		| Ty_var _ -> ty
		| Ty_app (f, args) -> Ty_app (build_ty f, List.map args ~f:build_ty)
		| Ty_arr (args, ret) -> Ty_arr (List.map args ~f:build_ty, build_ty ret)
    | Ty_record ty_row -> Ty_record (build_ty_row ty_row)
  and build_ty_row ty_row = match ty_row with
    | Ty_row_empty
    | Ty_row_var _ -> ty_row
    | Ty_row_field (name, ty, ty_row) ->
      Ty_row_field (name, build_ty ty, build_ty_row ty_row)
	in
	build_ty ty

%}

%token <string> IDENT
%token FUN LET REC IN FORALL WITH
%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE
%token ARROW EQUALS COMMA DOT SEMI ASSIGN
%token EOF

%start expr_eof
%type <Expr.expr> expr_eof
%start ty_eof
%type <Expr.ty> ty_eof
%start ty_forall_eof
%type <Expr.ty> ty_forall_eof

%%

expr_eof:
	  e = expr EOF        { e }

ty_eof:
	  t = ty EOF          { t }

ty_forall_eof:
	  t = ty_forall EOF   { t }

expr:
	  e = simple_expr     { e }

	(* let-bindings *)
	| LET n = IDENT EQUALS e = expr IN b = expr     { Expr_let (n, e, b) }
	| LET REC n = IDENT EQUALS e = expr IN b = expr { Expr_let_rec (n, e, b) }

	(* functions *)
  | FUN arg = IDENT ARROW body = expr
    { Expr_abs ([arg], body) }
	| FUN LPAREN args = flex_list(COMMA, IDENT) RPAREN ARROW body = expr
	  { Expr_abs (args, body) }

  (* let-fun fused *)
	| LET n = IDENT arg = IDENT EQUALS e = expr IN b = expr
    { Expr_let (n, Expr_abs ([arg], e), b) }
	| LET n = IDENT LPAREN args = flex_list(COMMA, IDENT) RPAREN EQUALS e = expr IN b = expr
    { Expr_let (n, Expr_abs (args, e), b) }
	| LET REC n = IDENT arg = IDENT EQUALS e = expr IN b = expr
    { Expr_let_rec (n, Expr_abs ([arg], e), b) }
	| LET REC n = IDENT LPAREN args = flex_list(COMMA, IDENT) RPAREN EQUALS e = expr IN b = expr
    { Expr_let_rec (n, Expr_abs (args, e), b) }

  (* records *)
  | LBRACE fs = flex_list(SEMI, field) RBRACE
    { Expr_record fs }
  | LBRACE e = expr WITH fs = nonempty_flex_list(SEMI, field) RBRACE
    { Expr_record_extend (e, fs) }
  | LBRACE e = expr WITH fs = nonempty_flex_list(SEMI, field_update) RBRACE
    { Expr_record_update (e, fs) }

simple_expr:
	  n = IDENT              { Expr_name n }
	| LPAREN e = expr RPAREN { e }
	| f = simple_expr LPAREN args = flex_list(COMMA, expr) RPAREN
	  { Expr_app (f, args) }
  | e = simple_expr DOT n = IDENT
    { Expr_record_proj (e, n) }

field:
    n = IDENT EQUALS e = expr { (n, e) }

field_update:
    n = IDENT ASSIGN e = expr { (n, e) }

ident_list:
	  n = IDENT                 { [n] }
	| n = IDENT ns = ident_list { n :: ns }

ty_forall:
	  t = ty                                            { t }
	| FORALL LBRACKET vars = ident_list RBRACKET t = ty { build_ty vars t }

ty:
	  t = simple_ty
	  { t }
	| LPAREN RPAREN ARROW ret = ty
	  { Ty_arr ([], ret) }
	| arg = simple_ty ARROW ret = ty
	  { Ty_arr ([arg], ret) }
	| LPAREN arg = ty COMMA args = flex_list(COMMA, ty) RPAREN ARROW ret = ty 
	  { Ty_arr (arg :: args, ret) }

simple_ty:
	  n = IDENT             { Ty_const n }
	| LPAREN t = ty RPAREN  { t }
	| f = simple_ty LBRACKET args = nonempty_flex_list(COMMA, ty) RBRACKET
	  { Ty_app (f, args) }

(* Utilities for flexible lists (and its non-empty version).

   A flexible list [flex_list(delim, X)] is the delimited with [delim] list of
   it [X] items where it is allowed to have a trailing [delim].

   A non-empty [nonempty_flex_list(delim, X)] version of flexible list is
   provided as well.

   From http://gallium.inria.fr/blog/lr-lists/

 *)

flex_list(delim, X):
    { [] }
  | x = X { [x] }
  | x = X delim xs = flex_list(delim, X) { x::xs }

nonempty_flex_list(delim, X):
    x = X { [x] }
  | x = X delim xs = flex_list(delim, X) { x::xs }
