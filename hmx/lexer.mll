{

open Parser

exception Error of string

}


let ident = ['_' 'a'-'z' '\''] ['_' '\'' 'A'-'Z' 'a'-'z' '0'-'9']*
let cident = ['A'-'Z'] ['_' '\'' 'A'-'Z' 'a'-'z' '0'-'9']*
let integer = ['0'-'9']+

rule token = parse
	| [' ' '\t' '\r' '\n']  { token lexbuf }
	| "fun"                 { FUN }
	| "let"                 { LET }
	| "val"                 { VAL }
	| "rec"                 { REC }
	| "in"                  { IN }
	| "with"                { WITH }
	| "struct"              { STRUCT }
	| "sig"                 { SIG }
	| "end"                 { END }
	| "type"                { TYPE }
	| "module"              { MODULE }
	| cident                { CIDENT (Lexing.lexeme lexbuf) }
	| ident                 { IDENT (Lexing.lexeme lexbuf) }
	| '('     { LPAREN }
	| ')'     { RPAREN }
	| '['     { LBRACKET }
	| ']'     { RBRACKET }
	| '{'     { LBRACE }
  | '}'     { RBRACE }
	| '='     { EQUALS }
	| ':' '=' { ASSIGN }
	| "->"    { ARROW }
	| "=>"    { GTE }
	| ','     { COMMA }
	| '.'     { DOT }
	| ';'     { SEMI }
	| ':'     { COLON }
	| eof     { EOF }
	| _ as c  { raise (Error ("unexpected token: '" ^ Char.escaped c ^ "'")) }


{

let string_of_token = function
	| FUN -> "fun"
	| LET -> "let"
	| VAL -> "val"
	| REC -> "rec"
	| IN -> "in"
	| WITH -> "forall"
	| MODULE -> "module"
	| STRUCT -> "struct"
	| SIG -> "sig"
	| END -> "end"
	| TYPE -> "type"
	| IDENT ident -> ident
	| CIDENT ident -> ident
	| LPAREN -> "("
	| RPAREN -> ")"
	| LBRACKET -> "["
	| RBRACKET -> "]"
	| LBRACE -> "{"
  | RBRACE -> "}"
	| EQUALS -> "="
	| ASSIGN -> ":="
	| ARROW -> "->"
	| COMMA -> ","
	| DOT -> "."
	| SEMI -> "."
	| COLON -> ":"
	| GTE -> "=>"
	| EOF -> "<eof>"

}
