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

module Bound = struct
  include Syntax.Bound
end

module Var = Var
module Type_error = Type_error

module Env = struct
  include Infer.Env

  let assume_val name ty env = add_val env name (Ty_sch.parse_string ty)

  let assume_tclass name ty env = add_tclass env name (Ty_sch.parse_string ty)

  let assume_tclass_instance name ty env =
    add_tclass_instance env name (Ty_sch.parse_string ty)
end

let infer = Infer.infer
