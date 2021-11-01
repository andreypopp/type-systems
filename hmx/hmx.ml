open! Base

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

module Mstr = struct
  include Syntax.Mstr

  include Nice_parser.Make (struct
    type token = Parser.token

    type result = Syntax.mstr

    let parse = Parser.mstr_eof

    let next_token = Lexer.token

    exception ParseError = Parser.Error

    exception LexError = Lexer.Error
  end)
end

module Type_error = Type_error
module Var = Var
module Syntax = Syntax

module Env = struct
  include Infer.Env

  let assume_val name ty env = add_val env name (Ty_sch.parse_string ty)

  let assume_type name arity env =
    let ty = Syntax.Ty_abstract (Syntax.Path.make name) in
    let vs = List.init arity ~f:(fun _ -> Var.fresh ()) in
    add_type env name (vs, ty)
end

let infer_to_result f =
  try Ok (f ()) with
  | Type_error.Type_error error -> Error error

let infer ~env e = infer_to_result (fun () -> Infer.infer_expr ~env e)

let infer_mstr ~env e = infer_to_result (fun () -> Infer.infer_mstr ~env e)

let () =
  Expr.pp_exceptions ();
  Ty_sch.pp_exceptions ();
  Mstr.pp_exceptions ()
