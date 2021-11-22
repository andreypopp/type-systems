module Expr = struct
  include Syntax.Expr

  include Nice_parser.Make (struct
    type token = Parser.token

    type result = Syntax.expr

    let parse = Parser.expr_eof

    let next_token = Lexer.token

    exception ParseError = Parser.Error

    exception LexError = Lexer.Error
  end)
end

module Ty = struct
  include Syntax.Ty

  include Nice_parser.Make (struct
    type token = Parser.token

    type result = Syntax.ty

    let parse = Parser.ty_eof

    let next_token = Lexer.token

    exception ParseError = Parser.Error

    exception LexError = Lexer.Error
  end)
end

module Ty_sch = struct
  include Syntax.Ty_sch

  include Nice_parser.Make (struct
    type token = Parser.token

    type result = Syntax.ty_sch

    let parse = Parser.ty_sch_eof

    let next_token = Lexer.token

    exception ParseError = Parser.Error

    exception LexError = Lexer.Error
  end)
end

module Type_error = Type_error
module Var = Var

module Env = struct
  include Infer.Env

  let assume_val name ty env =
    add_val ~kind:Val_top env name (Ty_sch.parse_string ty)
end

let infer = Infer.infer

let () = Expr.pp_exceptions ()
