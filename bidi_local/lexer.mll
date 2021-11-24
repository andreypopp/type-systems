{

open Parser

exception Error of string

}


let ident = ['_' 'A'-'Z' 'a'-'z'] ['_' 'A'-'Z' 'a'-'z' '0'-'9']*
let integer = ['0'-'9']+

rule token = parse
	| [' ' '\t' '\r' '\n']  { token lexbuf }
	| "fun"                 { FUN }
	| "let"                 { LET }
	| "in"                  { IN }
	| "with"                { WITH }
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
	| ','     { COMMA }
	| '.'     { DOT }
	| '.' '.' '.' { ELLIPSIS }
	| ':'     { COLON }
	| '?'     { QUESTION }
	| eof     { EOF }
	| _ as c  { raise (Error ("unexpected token: '" ^ Char.escaped c ^ "'")) }


{

let string_of_token = function
	| FUN -> "fun"
	| LET -> "let"
	| IN -> "in"
	| WITH -> "forall"
	| IDENT ident -> ident
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
	| ELLIPSIS -> "."
	| COLON -> ":"
	| QUESTION -> "?"
	| EOF -> "<eof>"

}
