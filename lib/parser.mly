%{

open Expr

let build_ty var_name_list ty =
  let open Base in
	let env = List.fold_left
	  var_name_list
	  ~init:(Map.empty (module String))
		~f:(fun env var_name -> Map.set env ~key:var_name ~data:(Infer.newgenvar ()))
	in
	let rec aux ty = match ty with
		| Ty_const name -> (
		  match Map.find env name with
      | Some ty -> ty
      | None -> ty)
		| Ty_var _ -> ty
		| Ty_app (f, args) -> Ty_app (aux f, List.map args ~f:aux)
		| Ty_arr (args, ret) -> Ty_arr (List.map args ~f:aux, aux ret)
	in
	aux ty

%}

%token <string> IDENT
%token FUN LET REC IN FORALL
%token LPAREN RPAREN LBRACKET RBRACKET
%token ARROW EQUALS COMMA
%token EOF

%start expr_eof
%type <Expr.expr> expr_eof
%start ty_eof
%type <Expr.ty> ty_eof
%start ty_forall_eof
%type <Expr.ty> ty_forall_eof

%%

expr_eof:
	| e = expr EOF        { e }

ty_eof:
	| t = ty EOF          { t }

ty_forall_eof:
	| t = ty_forall EOF   { t }

expr:
	| e = simple_expr                                       { e }
	| LET n = IDENT EQUALS e = expr IN b = expr             { Expr_let (n, e, b) }
	| LET REC n = IDENT EQUALS e = expr IN b = expr         { Expr_let_rec (n, e, b) }
  | FUN LPAREN RPAREN ARROW body = expr                   { Expr_abs ([], body) }
  | FUN arg = IDENT ARROW body = expr                     { Expr_abs ([arg], body) }
	| FUN LPAREN args = param_list RPAREN ARROW body = expr { Expr_abs (args, body) }

simple_expr:
	| n = IDENT                                            { Expr_name n }
	| LPAREN e = expr RPAREN                               { e }
	| f = simple_expr LPAREN args = expr_comma_list RPAREN { Expr_app (f, args) }
	| f = simple_expr LPAREN RPAREN                        { Expr_app (f, []) }

ident_list:
	| n = IDENT                 { [n] }
	| n = IDENT ns = ident_list { n :: ns }

param_list:
	| n = IDENT                       { [n] }
	| n = IDENT COMMA ns = param_list { n :: ns }

expr_comma_list:
	| e = expr                             { [e] }
	| e = expr COMMA es = expr_comma_list  { e :: es }

ty_forall:
	| t = ty                                            { t }
	| FORALL LBRACKET vars = ident_list RBRACKET t = ty { build_ty vars t }

ty:
	| t = simple_ty                                     { t }
	| LPAREN RPAREN ARROW ret = ty                      { Ty_arr ([], ret) }
	| arg = simple_ty ARROW ret = ty                    { Ty_arr ([arg], ret) }
	| LPAREN arg = ty COMMA args = ty_comma_list RPAREN ARROW ret = ty  { Ty_arr (arg :: args, ret) }

simple_ty:
	| n = IDENT                                            { Ty_const n }
	| f = simple_ty LBRACKET args = ty_comma_list RBRACKET { Ty_app (f, args) }
	| LPAREN t = ty RPAREN                                 { t }
	
ty_comma_list:
	| t = ty                           { [t] }
	| t = ty COMMA ts = ty_comma_list  { t :: ts }
