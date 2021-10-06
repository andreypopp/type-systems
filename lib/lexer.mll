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
	| "rec"                 { REC }
	| "in"                  { IN }
	| "forall"              { FORALL }
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
	| ';'     { SEMI }
	| eof     { EOF }
	| _ as c  { raise (Error ("unexpected token: '" ^ Char.escaped c ^ "'")) }


{

let string_of_token = function
	| FUN -> "fun"
	| LET -> "let"
	| REC -> "rec"
	| IN -> "in"
	| FORALL -> "forall"
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
	| SEMI -> "."
	| EOF -> "<eof>"

}
