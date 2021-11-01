%{

open Syntax

let makeenv vars =
  let open Base in
  Var.reset ();
  let tbl = Hashtbl.create (module String) in
  let vs = List.map vars ~f:(fun name ->
    let v = Var.fresh () in
    Hashtbl.set tbl ~key:name ~data:(Ty.var v);
    v
  ) in
  List.rev vs, tbl

let is_ty_var name =
  Base.String.is_prefix name ~prefix:"'"

let build_ty_sch (vs, env) ty =
  let open Base in
	let rec build_ty ty = match ty with
    | Ty_name (Path.Path_ident name) -> (
		  match Hashtbl.find env name with
      | Some ty -> ty
      | None ->
        if is_ty_var name then (
          Hashtbl.find_or_add env name
            ~default:(fun () -> Ty.var (Var.fresh ()))
        ) else ty
      )
    | Ty_name _ -> ty
    | Ty_abstract _ -> assert false
		| Ty_var _ -> ty
		| Ty_app (ty, atys) -> Ty_app (build_ty ty, List.map atys ~f:build_ty)
		| Ty_arr (atys, rty) -> Ty_arr (List.map atys ~f:build_ty, build_ty rty)
	in
  vs, build_ty ty
%}

%token <string> IDENT
%token <string> CIDENT
%token FUN LET VAL REC IN WITH STRUCT SIG END TYPE MODULE
%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE
%token ARROW EQUALS COMMA DOT SEMI COLON ASSIGN GTE
%token EOF

%start expr_eof
%type <Syntax.expr> expr_eof
%start ty_sch_eof
%type <Syntax.ty_sch> ty_sch_eof
%start mstr_eof
%type <Syntax.mstr> mstr_eof

%%

expr_eof:
	  e = expr EOF        { e }

ty_sch_eof:
	  t = ty_sch EOF   { t }

mstr_eof:
	  s = mstr EOF        { s }

expr:
	  e = simple_expr     { e }

	(* let-bindings *)
	| LET n = IDENT a = option(ty_ascribe) EQUALS e = expr IN b = expr    
	  { E_let ((n, e, a), b) }

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
    mp = path_ident { E_var mp }
	| LPAREN e = expr RPAREN { e }
	| f = simple_expr LPAREN args = flex_list(COMMA, expr) RPAREN
	  { E_app (f, args) }

ty_ascribe:
  COLON t = ty
  { let env = makeenv [] in build_ty_sch env t }

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
    mp = path_ident { Ty_name mp }
	| LPAREN t = ty RPAREN  { t }
  | f = simple_ty LBRACKET args = nonempty_flex_list(COMMA, ty) RBRACKET
	  { Ty_app (f, args) }

mexpr:
    me = simple_mexpr { me }
  | STRUCT mstr = mstr END { M_str mstr }
  | me = simple_mexpr mty = mty_ascribe { M_constr (me, mty) }

simple_mexpr:
    p = path { M_path p }
  | LPAREN me = mexpr RPAREN { me }

mty:
    p = path { Mty_path p }
  | SIG msig = msig END { Mty_sig msig }

path_ident:
    p = path DOT n = IDENT { Path.Path_project (p, n) }
  | n = IDENT { Path.Path_ident n }

path:
    n = CIDENT { Path.Path_ident n }
  | p = path DOT n = CIDENT { Path.Path_project (p, n) }

%inline mstr:
  mstr = list(mstr_item) { mstr }

mstr_item:
    LET n = IDENT a = option(ty_ascribe) EQUALS e = expr
    { Mstr_val (n, a, e) }
  | TYPE n = IDENT vars = ty_params ty = option(ty_equals)
    { match ty with
      | None ->
        Mstr_ty (n, Ty_decl_abstract (List.length vars))
      | Some ty ->
        let env = makeenv vars in
        let ty_sch = build_ty_sch env ty in
        Mstr_ty (n, Ty_decl_alias ty_sch)
    }
  | MODULE n = CIDENT mty = option(mty_ascribe) EQUALS me = mexpr
    { match mty with
      | None -> Mstr_mexpr (n, me)
      | Some mty -> Mstr_mexpr (n, M_constr (me, mty))
    }
  | MODULE TYPE n = CIDENT EQUALS mty = mty
    { Mstr_mty (n, mty) }

%inline msig:
  msig = list(msig_item) { msig }

msig_item:
    VAL n = IDENT a = ty_ascribe
    { Msig_val (n, a) }
  | TYPE n = IDENT vars = ty_params ty = option(ty_equals)
    { match ty with
      | None ->
        Msig_ty (n, Ty_decl_abstract (List.length vars))
      | Some ty ->
        let env = makeenv vars in
        let ty_sch = build_ty_sch env ty in
        Msig_ty (n, Ty_decl_alias ty_sch)
    }
  | MODULE n = CIDENT COLON mty = mty
    { Msig_mexpr (n, mty) }
  | MODULE TYPE n = CIDENT EQUALS mty = mty
    { Msig_mty (n, mty) }

ty_params:
    { [] }
  | LBRACKET vs = nonempty_flex_list(COMMA, IDENT) RBRACKET { vs }

ty_equals:
  EQUALS ty = ty { ty }

mty_ascribe:
  COLON mty = mty
  { mty }

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
