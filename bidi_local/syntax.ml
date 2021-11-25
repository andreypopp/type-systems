open! Import
include Syntax0

let kw = Layout.bold

let punct = Layout.fg White

let record_braces doc = Layout.(punct (string "{") ^^ doc ^^ punct (string "}"))

let ty_brackets doc = Layout.(punct (string "[") ^^ doc ^^ punct (string "]"))

let f_parens doc = Layout.(punct (string "(") ^^ doc ^^ punct (string ")"))

let rec layout_expr' (loc, expr) : Layout.layout =
  let open Layout in
  let is_simple_expr (_, expr) =
    match expr with
    | E_var _
    | E_app _
    | E_record _ ->
      true
    | _ -> false
  in
  match expr with
  | E_ann (expr, ty_sch) ->
    let* ty_sch = layout_ty_sch' ty_sch in
    let* expr = layout_expr' expr in
    return
      (group
         (f_parens (align (expr ^^ break 1 ^^ punct (string ": ") ^^ ty_sch))))
  | E_var name -> return (string name)
  | E_abs (vs, args, body) ->
    let sep = punct comma ^^ blank 1 in
    let* vs =
      match vs with
      | [] -> return empty
      | vs ->
        let+ items = list_map vs ~f:layout_poly_var' in
        ty_brackets (separate sep items)
    in
    let newline =
      (* Always break on let inside the body. *)
      match body with
      | _, E_let _ -> hardline
      | _ -> break 1
    in
    let* args =
      match args with
      | [ ((_loc, name), None) ] -> return (string name)
      | args ->
        let layout_arg = function
          | (_loc, name), None -> return (string name)
          | (_loc, name), Some ty ->
            let* ty = layout_ty' ty in
            return (string name ^^ punct (string ": ") ^^ ty)
        in
        let+ items = list_map args ~f:layout_arg in
        f_parens (separate sep items)
    in
    let* body = layout_expr' body in
    return
      (group
         (group
            (kw (string "fun")
            ^^ vs
            ^^ string " "
            ^^ args
            ^^ punct (string " ->"))
         ^^ nest 2 (group (newline ^^ group body))))
  | E_app (f, args) ->
    let sep = punct comma ^^ break 1 in
    let* f = layout_expr' f in
    let* args = list_map args ~f:layout_expr' in
    return
      (group (f ^^ f_parens (nest 2 (group (break 0 ^^ separate sep args)))))
  | E_let _ as e ->
    let es =
      (* We do not want to print multiple nested let-expression with indents and
         therefore we linearize them first and print on the same indent instead. *)
      let rec linearize es e =
        match e with
        | E_let (_, (_, b)) -> linearize (e :: es) b
        | e -> e :: es
      in
      List.rev (linearize [] e)
    in
    let newline =
      (* If there's more than a single let-expression found (checking length > 2
         because es containts the body of the last let-expression too) we split
         them with a hardline. *)
      if List.length es > 2 then hardline else break 1
    in
    let+ items =
      list_map es ~f:(function
        | E_let ((name, expr, ty), _) ->
          let* ascription =
            (* We need to layout ty_sch first as it will allocate names for use
               down the road. *)
            match ty with
            | None -> return empty
            | Some ty ->
              let ty_break, ty_nest =
                match ty with
                | [], Ty_record _ -> (space, 0)
                | _ -> (break 1, 4)
              in
              let+ ty = layout_ty_sch' ty in
              punct (string " :") ^^ nest ty_nest (ty_break ^^ ty)
          in
          let expr_newline, expr_nest =
            (* If there's [let x = let y = ... in ... in ...] then we want to
               force break. *)
            match expr with
            | _, E_let _ -> (hardline, 2)
            | _, E_record _ -> (space, 0)
            | _ -> (break 1, 2)
          in
          let* expr = layout_expr' expr in
          return
            (group
               (group
                  (kw (string "let ")
                  ^^ string name
                  ^^ ascription
                  ^^ punct (string " ="))
               ^^ nest expr_nest (expr_newline ^^ expr)
               ^^ expr_newline
               ^^ kw (string "in"))
            ^^ newline)
        | e -> layout_expr' (loc, e))
    in
    concat items
  | E_record fields ->
    let layout_field (name, expr) =
      let+ expr = layout_expr' expr in
      string name ^^ punct (string " = ") ^^ expr
    in
    let+ fields = Layout.list_map fields ~f:layout_field in
    let sep = punct comma ^^ break 1 in
    group (record_braces (nest 2 (break 0 ^^ separate sep fields) ^^ break 0))
  | E_record_project (expr, name) ->
    if is_simple_expr expr then
      let+ expr = layout_expr' expr in
      expr ^^ dot ^^ string name
    else
      let+ expr = layout_expr' expr in
      f_parens expr ^^ dot ^^ string name
  | E_record_extend (expr, fields) ->
    let layout_field (name, expr) =
      let+ expr = layout_expr' expr in
      string name ^^ punct (string " = ") ^^ expr
    in
    let* expr = layout_expr' expr in
    let* fields = Layout.list_map fields ~f:layout_field in
    let sep = punct comma ^^ break 1 in
    return (record_braces (expr ^^ kw (string " with ") ^^ separate sep fields))
  | E_record_update (expr, fields) ->
    let layout_field (name, expr) =
      let+ expr = layout_expr' expr in
      string name ^^ punct (string " := ") ^^ expr
    in
    let* expr = layout_expr' expr in
    let* fields = Layout.list_map fields ~f:layout_field in
    let sep = punct comma ^^ break 1 in
    return (record_braces (expr ^^ kw (string " with ") ^^ separate sep fields))
  | E_lit (Lit_string v) -> return (dquotes (string v))
  | E_lit (Lit_int v) -> return (dquotes (string (Int.to_string v)))

and layout_ty' ty =
  let open Layout in
  let rec is_ty_row_empty = function
    | Ty_row_empty -> true
    | Ty_bot -> true
    | Ty_var var -> (
      match (Union_find.value var).ty with
      | None -> false
      | Some ty -> is_ty_row_empty ty)
    | _ -> false
  in
  let rec is_ty_arr = function
    | Ty_var var -> (
      match (Union_find.value var).ty with
      | None -> false
      | Some ty -> is_ty_arr ty)
    | Ty_arr _ -> true
    | _ -> false
  in
  let rec layout_ty = function
    | Ty_const name -> return (string name)
    | Ty_arr ([ aty ], rty) ->
      (* Check if we can layout this as simply as [aty -> try] in case of a
         single argument. *)
      let is_ty_arr_to_the_left = is_ty_arr aty in
      let* aty = layout_ty aty in
      let* rty = layout_ty rty in
      return
        ((if is_ty_arr_to_the_left then
          (* If the single arg is the Ty_arr we need to wrap it in parens. *)
          f_parens aty
         else aty)
        ^^ punct (string " -> ")
        ^^ rty)
    | Ty_arr (atys, rty) ->
      let sep = punct comma ^^ blank 1 in
      let* atys = list_map atys ~f:layout_ty in
      let* rty = layout_ty rty in
      return (f_parens (separate sep atys) ^^ punct (string " -> ") ^^ rty)
    | Ty_app (fty, atys) ->
      let sep = punct comma ^^ blank 1 in
      let* fty = layout_ty fty in
      let* atys = list_map atys ~f:layout_ty in
      return (fty ^^ ty_brackets (separate sep atys))
    | Ty_nullable ty ->
      let* ty = layout_ty ty in
      return (ty ^^ string "?")
    | Ty_var var -> (
      match (Union_find.value var).ty with
      | None -> layout_var' var
      | Some ty -> layout_ty ty)
    | Ty_record ty_row ->
      let+ ty_row = layout_ty_row ty_row in
      group (record_braces (nest 2 (break 0 ^^ ty_row) ^^ break 0))
    | (Ty_row_empty | Ty_row_extend _) as ty -> layout_ty_row ty
    | Ty_bot -> return (string "⊥")
    | Ty_top -> return (string "⊤")
  and layout_ty_row = function
    | Ty_row_extend ((name, ty), next) ->
      let* field =
        let+ ty = layout_ty ty in
        string name ^^ punct (string ": ") ^^ ty
      in
      if is_ty_row_empty next then return field
      else
        let* next = layout_ty_row next in
        let sep = punct comma ^^ break 1 in
        return (field ^^ sep ^^ next)
    | Ty_row_empty -> return empty
    | Ty_var var -> (
      match (Union_find.value var).ty with
      | None ->
        let+ var = layout_var' var in
        punct (string "...") ^^ var
      | Some ty -> layout_ty_row ty)
    | Ty_const name -> return (string name)
    | ty ->
      Caml.Format.printf "%a@." Sexp.pp_hum (sexp_of_ty ty);
      assert false
  in
  layout_ty ty

and layout_unbound_var v =
  let open Layout in
  let+ variance =
    match v.variance with
    | None -> return empty
    | Some v -> layout_variance' v
  in
  variance ^^ string (Printf.sprintf "_%i" v.id)

and layout_var' v =
  let open Layout in
  let v' = Union_find.value v in
  match v'.ty with
  | Some ty -> layout_ty' ty
  | None ->
    let* name = lookup_var v in
    let+ doc =
      match name with
      | Some name -> return (string name)
      | None -> layout_unbound_var v'
    in
    if Debug.log_levels then doc ^^ layout_v_debug' v else doc

and layout_ty_sch' (ty_sch : ty_sch) =
  let open Layout in
  match ty_sch with
  | [], ty -> layout_ty' ty
  | vs, ty ->
    let* vs = layout_var_prenex' vs in
    let* ty = layout_ty' ty in
    return (group (vs ^^ ty))

and layout_var_prenex' vs =
  let open Layout in
  let sep = punct comma ^^ blank 1 in
  let* vs = list_map vs ~f:layout_poly_var' in
  return (separate sep vs ^^ punct (string " . "))

and layout_poly_var' v : Layout.layout =
  let open Layout in
  let+ doc = alloc_var v in
  if Debug.log_levels then string doc ^^ layout_v_debug' v else string doc

and layout_v_debug' v =
  let open Layout in
  let v = Union_find.value v in
  let lvl = Option.value v.lvl ~default:(-1) in
  string ("{" ^ Int.to_string v.id ^ "}" ^ "@" ^ Int.to_string lvl)

and layout_variance' v =
  let open Layout in
  Layout.return
    (match v with
    | Covariant -> string "+"
    | Contravariant -> string "-"
    | Invariant -> string "=")

module Expr = struct
  type t = expr

  let loc (loc, _) = loc

  let layout = layout_expr'

  include (
    Showable (struct
      type t = expr

      let layout e = Layout.render (layout e)
    end) :
      SHOWABLE with type t := t)

  include (
    Dumpable (struct
      type t = expr

      let sexp_of_t = sexp_of_expr
    end) :
      DUMPABLE with type t := t)
end

module Ty = struct
  type t = ty

  let arr a b = Ty_arr (a, b)

  let var var = Ty_var var

  let nullable ty =
    match ty with
    | Ty_nullable _ -> ty
    | Ty_bot -> ty
    | ty -> Ty_nullable ty

  let rec equal a b =
    match (a, b) with
    | Ty_const a, Ty_const b -> String.equal a b
    | Ty_var a, Ty_var b -> (
      Union_find.equal a b
      ||
      let a = Union_find.value a
      and b = Union_find.value b in
      match (a.ty, b.ty) with
      | None, None -> Int.equal a.id b.id
      | Some a, Some b -> equal a b
      | _ -> false)
    | Ty_var v, b -> (
      match (Union_find.value v).ty with
      | None -> false
      | Some a -> equal a b)
    | a, Ty_var v -> (
      match (Union_find.value v).ty with
      | None -> false
      | Some b -> equal a b)
    | Ty_app (a, args), Ty_app (b, brgs) -> (
      equal a b
      &&
      match List.for_all2 args brgs ~f:equal with
      | Unequal_lengths -> false
      | Ok v -> v)
    | Ty_nullable a, Ty_nullable b -> equal a b
    | Ty_arr (args, a), Ty_arr (brgs, b) -> (
      equal a b
      &&
      match List.for_all2 args brgs ~f:equal with
      | Unequal_lengths -> false
      | Ok v -> v)
    | Ty_record row1, Ty_record row2 -> equal row1 row2
    | Ty_row_empty, Ty_row_empty -> true
    | Ty_row_extend ((name1, ty1), row1), Ty_row_extend ((name2, ty2), row2) ->
      String.equal name1 name2 && equal ty1 ty2 && equal row1 row2
    | Ty_bot, Ty_bot -> true
    | Ty_top, Ty_top -> true
    | _, _ -> false

  let layout = layout_ty'

  include (
    Showable (struct
      type t = ty

      let layout ty = Layout.render (layout ty)
    end) :
      SHOWABLE with type t := t)

  include (
    Dumpable (struct
      type t = ty

      let sexp_of_t = sexp_of_ty
    end) :
      DUMPABLE with type t := t)
end

module Ty_sch = struct
  type t = ty_sch

  let layout = layout_ty_sch'

  include (
    Showable (struct
      type t = ty_sch

      let layout ty_sch = Layout.render (layout ty_sch)
    end) :
      SHOWABLE with type t := t)

  include (
    Dumpable (struct
      type t = ty_sch

      let sexp_of_t = sexp_of_ty_sch
    end) :
      DUMPABLE with type t := t)
end

module Variance = struct
  type t = variance

  let inv = function
    | Covariant -> Contravariant
    | Contravariant -> Covariant
    | Invariant -> Invariant

  let join a b =
    match (a, b) with
    | Invariant, _
    | _, Invariant ->
      Invariant
    | Covariant, Contravariant
    | Contravariant, Covariant ->
      Invariant
    | Covariant, Covariant -> Covariant
    | Contravariant, Contravariant -> Contravariant

  let layout = layout_variance'

  include (
    Showable (struct
      type nonrec t = t

      let layout v = Layout.render (layout v)
    end) :
      SHOWABLE with type t := t)
end
