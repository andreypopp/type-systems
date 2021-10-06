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
  | LBRACE RBRACE                                         { Expr_record [] }
  | LBRACE fs = field_list RBRACE                         { Expr_record fs }
  | LBRACE e = expr WITH fs = field_list RBRACE           { Expr_record_extend (e, fs) }
  | LBRACE e = expr WITH fs = field_assign_list RBRACE    { Expr_record_update (e, fs) }

simple_expr:
	| n = IDENT                                            { Expr_name n }
	| LPAREN e = expr RPAREN                               { e }
	| f = simple_expr LPAREN args = expr_comma_list RPAREN { Expr_app (f, args) }
	| f = simple_expr LPAREN RPAREN                        { Expr_app (f, []) }
  | e = simple_expr DOT n = IDENT                        { Expr_record_proj (e, n) }

field_list:
  | n = IDENT EQUALS e = expr                             { [(n, e)] }
  | n = IDENT EQUALS e = expr SEMI fs = field_list        { (n, e) :: fs }

field_assign_list:
  | n = IDENT ASSIGN e = expr                             { [(n, e)] }
  | n = IDENT ASSIGN e = expr SEMI fs = field_assign_list { (n, e) :: fs }
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
