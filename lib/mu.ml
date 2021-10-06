open! Base
module Expr = Expr
module Infer = Infer

module Expr_parser = Nice_parser.Make (struct
  type token = Parser.token

  type result = Expr.expr

  let parse = Parser.expr_eof

  let next_token = Lexer.token

  exception ParseError = Parser.Error

  exception LexError = Lexer.Error
end)

module Ty_parser = Nice_parser.Make (struct
  type token = Parser.token

  type result = Expr.ty

  let parse = Parser.ty_forall_eof

  let next_token = Lexer.token

  exception ParseError = Parser.Error

  exception LexError = Lexer.Error
end)

let parse_expr = Expr_parser.parse_string

let parse_ty = Ty_parser.parse_string

let empty_env = Map.empty (module String)

let infer_ty ?(env = empty_env) expr =
  try Ok (Infer.infer env expr) with
  | Infer.Type_error err -> Error err

let () =
  Expr_parser.pp_exceptions ();
  Ty_parser.pp_exceptions ()
