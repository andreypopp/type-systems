%{

open Expr

let makeenv vars =
  let open Base in
  Infer.reset_vars ();
  List.fold_left
    vars
    ~init:(Map.empty (module String))
    ~f:(fun env var_name ->
      Map.set env ~key:var_name ~data:(Infer.newgenvar ()))

let build_ty env ty =
  let open Base in
	let rec aux ty = match ty with
		| Ty_const name -> (
		  match Map.find env name with
      | Some ty -> ty
      | None -> ty)
		| Ty_var _ -> ty
		| Ty_app (f, args) -> Ty_app (aux f, List.map args ~f:aux)
		| Ty_arr (args, ret) -> Ty_arr (List.map args ~f:aux, aux ret)
    | Ty_record ty_row -> Ty_record (build_ty_row ty_row)
  and build_ty_row ty_row = match ty_row with
    | Ty_row_empty
    | Ty_row_var _ -> ty_row
    | Ty_row_field (name, ty, ty_row) ->
      Ty_row_field (name, aux ty, build_ty_row ty_row)
    | Ty_row_const name -> (
		  match Map.find env name with
      | Some (Ty_var {contents = Ty_var_generic id}) ->
        (* "convert" it to generic row variable *)
        Ty_row_var {contents = Ty_var_generic id}
      | Some _ ->
        (* shouldn't happen as we only insert generic vars into env *)
        assert false
      | None ->
        (* TODO: we should report a syntax error here as we only allow generic
           row variables at surface syntax. *)
        assert false)
	in
	aux ty

let build_qual_ty env (cs, ty : qual_ty) : qual_ty =
  let open Base in
  let cs = List.map cs ~f:(fun (n, tys) -> n, List.map tys ~f:(build_ty env)) in
  cs, build_ty env ty

let build_qual_pred env (deps, p) =
  let open Base in
  let build_pred (name, args) =
    name, List.map args ~f:(build_ty env)
  in
  List.map deps ~f:build_pred, build_pred p

%}

%token <string> IDENT
%token FUN LET REC IN WITH
%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE
%token ARROW EQUALS COMMA DOT SEMI COLON ASSIGN GTE
%token EOF

%start expr_eof
%type <Expr.expr> expr_eof
%start qual_ty_forall_eof
%type <Expr.qual_ty> qual_ty_forall_eof
%start qual_pred_eof
%type <Expr.qual_pred> qual_pred_eof

%%

expr_eof:
	  e = expr EOF        { e }

qual_ty_forall_eof:
	  t = qual_ty_forall EOF   { t }

qual_pred_eof:
  qp = qual_pred EOF { qp }

%inline qual_pred:
    p = pred EOF { [], p }
	| vars = ident_list DOT p = pred EOF {
    build_qual_pred (makeenv vars) ([], p)
	  }
	| vars = ident_list DOT deps = flex_list(COMMA, pred) GTE p = pred EOF {
      let env = makeenv vars in
      build_qual_pred env (deps, p)
	  }

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
    xs = nonempty_flex_list(COMMA, IDENT) { xs }

qual_ty_forall:
    qt = qual_ty { qt }
	| vars = ident_list DOT qt = qual_ty
	  { let env = makeenv vars in build_qual_ty env qt }

qual_ty:
    t = ty { ([], t) }
  | cs = nonempty_flex_list(COMMA, pred) GTE t = ty
    { (cs, t) }

pred:
  n = IDENT LPAREN args = nonempty_flex_list(COMMA, ty) RPAREN { (n, args) }

ty:
	  t = simple_ty
	  { t }
	| LPAREN RPAREN ARROW ret = ty
	  { Ty_arr ([], ret) }
	| arg = simple_ty ARROW ret = ty
	  { Ty_arr ([arg], ret) }
	| LPAREN arg = ty COMMA args = flex_list(COMMA, ty) RPAREN ARROW ret = ty 
	  { Ty_arr (arg :: args, ret) }
	| LBRACE row = ty_row RBRACE
    { Ty_record row }

ty_row:
    { Ty_row_empty }
  | t = IDENT { Ty_row_const t }
  | n = IDENT COLON t = ty  { Ty_row_field (n, t, Ty_row_empty) }
  | n = IDENT COLON t = ty SEMI r = ty_row  { Ty_row_field (n, t, r) }

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
