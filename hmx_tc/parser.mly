%{

open Syntax

let makeenv vars =
  let open Base in
  Var.reset ();
  let vs, map = List.fold_left
    vars
    ~init:([], Map.empty (module String))
    ~f:(fun (vs, env) name ->
      let v = Var.fresh () in
      v::vs,
      Map.set env ~key:name ~data:(Ty.var v)) in
  List.rev vs, map

let build_ty_sch (vs, env) (cs, ty) =
  let open Base in
	let rec build_ty ty = match ty with
		| Ty_const name -> (
		  match Map.find env name with
      | Some ty -> ty
      | None -> ty)
		| Ty_var _ -> ty
		| Ty_app (fty, atys) -> Ty_app (build_ty fty, List.map atys ~f:build_ty)
		| Ty_arr (atys, rty) -> Ty_arr (List.map atys ~f:build_ty, build_ty rty)
	and build_bound c =
	  match c with
    | B_class (name, tys) ->
      let tys = List.map tys ~f:build_ty in
      B_class (name, tys) 
	in
  vs, (List.map cs ~f:build_bound, build_ty ty)
%}

%token <string> IDENT
%token FUN LET REC IN WITH
%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE
%token ARROW EQUALS COMMA DOT SEMI COLON ASSIGN GTE
%token EOF

%start expr_eof
%type <Syntax.expr> expr_eof
%start ty_sch_eof
%type <Syntax.ty_sch> ty_sch_eof

%%

expr_eof:
	  e = expr EOF        { e }

ty_sch_eof:
	  t = ty_sch EOF   { t }

expr:
	  e = simple_expr     { e }

	(* let-bindings *)
	| LET n = IDENT EQUALS e = expr IN b = expr     { E_let ((n, e, None), b) }

	(* functions *)
  | FUN arg = IDENT ARROW body = expr
    { E_abs ([arg], body) }
  | FUN LPAREN args = flex_list(COMMA, IDENT) RPAREN ARROW body = expr
    { E_abs (args, body) }

	| LET n = IDENT arg = IDENT EQUALS e = expr IN b = expr
    { E_let ((n, E_abs ([arg], e), None), b) }
	| LET n = IDENT LPAREN args = flex_list(COMMA, IDENT) RPAREN EQUALS e = expr IN b = expr
    { E_let ((n, E_abs (args, e), None), b) }

simple_expr:
	  n = IDENT              { E_var n }
	| LPAREN e = expr RPAREN { e }
	| f = simple_expr LPAREN args = flex_list(COMMA, expr) RPAREN
	  { E_app (f, args) }

ident_list:
    xs = nonempty_flex_list(COMMA, IDENT) { xs }

ty_sch:
  t = cty { [], t }
	| vars = ident_list DOT t = cty
	  { let env = makeenv vars in build_ty_sch env t }

cty:
    t = ty { [], t }
  | bs = nonempty_flex_list(COMMA, bound) GTE ty = ty
    { bs, ty }

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
  | t = ty_app            { t }

ty_app:
	  f = simple_ty LBRACKET args = nonempty_flex_list(COMMA, ty) RBRACKET
	  { Ty_app (f, args) }

bound:
  t = ty_app
  { match t with
    | Ty_app (Ty_const name, args) -> B_class (name, args)
    | _ -> assert false
  }

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
