%{

open Syntax

let makeenv vars =
  let open Base in
  Var.reset ();
  let vs, map = List.fold_left
    vars
    ~init:([], Map.empty (module String))
    ~f:(fun (vs, env) name ->
      let v = Var.fresh ~name () in
      v::vs,
      Map.set env ~key:name ~data:(Ty.var v)) in
  List.rev vs, map

let build_ty_sch (vs, env) ty =
  let open Base in
	let rec build_ty ty = match ty with
		| Ty_const name -> (
		  match Map.find env name with
      | Some ty -> ty
      | None -> ty)
		| Ty_top
		| Ty_bot
		| Ty_var _ -> ty
		| Ty_nullable ty -> Ty_nullable (build_ty ty)
		| Ty_app (fty, atys) -> Ty_app (build_ty fty, List.map atys ~f:build_ty)
		| Ty_arr (atys, rty) -> Ty_arr (List.map atys ~f:build_ty, build_ty rty)
    | Ty_record row -> Ty_record (build_ty row)
    | Ty_row_empty -> ty
    | Ty_row_extend ((name, ty), row) ->
      Ty_row_extend ((name, build_ty ty), build_ty row)
	in
  vs, build_ty ty
%}

%token <string> IDENT
%token FUN LET IN WITH
%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE
%token ARROW EQUALS COMMA DOT COLON ASSIGN QUESTION ELLIPSIS
%token EOF

%start expr_eof
%type <Syntax.expr> expr_eof
%start ty_sch_eof
%type <Syntax.ty_sch> ty_sch_eof
%start ty_eof
%type <Syntax.ty> ty_eof

%%

expr_eof:
	  e = expr EOF { e }

ty_sch_eof:
	  t = ty_sch EOF { t }

ty_eof:
	  t = ty EOF { t }

expr:
	  e = simple_expr { e }

	| LPAREN e = expr t = expr_annot RPAREN { E_ann (e, t) }

	(* let-bindings *)
	| LET n = IDENT t = option(expr_annot) EQUALS e = expr IN b = expr
	  { E_let ((n, e, t), b) }

	(* functions *)
  | FUN ty_args = ty_args arg = IDENT ARROW body = expr
    { E_abs (ty_args, [arg, None], body) }
  | FUN ty_args = ty_args args = args ARROW body = expr
    { E_abs (ty_args, args, body) }

	| LET n = IDENT ty_args = ty_args arg = IDENT EQUALS e = expr IN b = expr
    { E_let ((n, E_abs (ty_args, [arg, None], e), None), b) }
	| LET n = IDENT ty_args = ty_args args = args EQUALS e = expr IN b = expr
    { E_let ((n, E_abs (ty_args, args, e), None), b) }

%inline expr_annot:
    COLON t = ty_sch { t }

args:
    LPAREN args = flex_list(COMMA, arg) RPAREN { args }

arg:
    n = IDENT t = option(arg_annot) { n, t }

ty_args:
    (* empty *) { [] }
  | LBRACKET vs = nonempty_flex_list(COMMA, ty_arg) RBRACKET { vs }

ty_arg: 
    n = IDENT { Var.fresh ~name:n () }

arg_annot:
    COLON t = ty { t }

simple_expr:
	  n = IDENT              { E_var n }
	| LPAREN e = expr RPAREN { e }
	| f = simple_expr LPAREN args = flex_list(COMMA, expr) RPAREN
	  { E_app (f, args) }
	| LBRACE fs = flex_list(COMMA, record_field) RBRACE
	  { E_record fs }
	| LBRACE e = expr WITH fs = nonempty_flex_list(COMMA, record_field) RBRACE
	  { E_record_extend (e, fs) }
	| LBRACE e = expr WITH fs = nonempty_flex_list(COMMA, record_field_update) RBRACE
	  { E_record_update (e, fs) }
	| e = simple_expr DOT n = IDENT
	  { E_record_project (e, n) }

record_field:
    n = IDENT EQUALS e = expr
    { n, e }

record_field_update:
    n = IDENT ASSIGN e = expr
    { n, e }

ident_list:
    xs = nonempty_flex_list(COMMA, IDENT) { xs }

ty_sch:
    t = ty { [], t }
	| vars = ident_list DOT t = ty
	  { let env = makeenv vars in build_ty_sch env t }

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
	| LBRACE RBRACE
	  { Ty_record Ty_row_empty }
	| LBRACE row = ty_row RBRACE
	  { Ty_record row }
	| t = simple_ty QUESTION
	  { Ty.nullable t }

ty_row:
    ELLIPSIS n = IDENT
    { Ty_const n }
  | n = IDENT COLON ty = ty COMMA?
    { Ty_row_extend ((n, ty), Ty_row_empty) }
  | n = IDENT COLON ty = ty COMMA row = ty_row
    { Ty_row_extend ((n, ty), row) }

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
