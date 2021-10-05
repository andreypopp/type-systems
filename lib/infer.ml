open! Base

type env = (String.t, Expr.ty, String.comparator_witness) Map.t

exception Type_error of string

let type_error msg = raise (Type_error msg)

let type_errorf fmt =
  let kerr _ =
    let msg = Caml.Format.flush_str_formatter () in
    raise (Type_error msg)
  in
  Caml.Format.kfprintf kerr Caml.Format.str_formatter fmt

let type_error_doc doc =
  let msg =
    let buf = Buffer.create 100 in
    PPrint.ToBuffer.pretty 1. 80 buf doc;
    Buffer.contents buf
  in
  raise (Type_error msg)

let currentid = ref 0

let resetid () = currentid := 0

let nextid () =
  Int.incr currentid;
  !currentid

let newvar lvl () =
  Expr.Ty_var { contents = Ty_var_unbound { id = nextid (); lvl } }

let newgenvar () = Expr.Ty_var { contents = Ty_var_generic (nextid ()) }

let instantiate lvl (ty : Expr.ty) =
  let vars = Hashtbl.create (module Int) in
  let rec aux ty =
    match ty with
    | Expr.Ty_const _ -> ty
    | Ty_arr (ty_args, ty_ret) -> Ty_arr (List.map ty_args ~f:aux, aux ty_ret)
    | Ty_app (ty, ty_args) -> Ty_app (aux ty, List.map ty_args ~f:aux)
    | Ty_var { contents = Ty_var_link ty } -> aux ty
    | Ty_var { contents = Ty_var_unbound _ } -> ty
    | Ty_var { contents = Ty_var_generic id } ->
      Hashtbl.find_or_add vars id ~default:(newvar lvl)
  in
  aux ty

let rec generalize lvl (ty : Expr.ty) =
  match ty with
  | Ty_const _ -> ty
  | Ty_arr (ty_args, ty_ret) ->
    Ty_arr (List.map ty_args ~f:(generalize lvl), generalize lvl ty_ret)
  | Ty_app (ty, ty_args) ->
    Ty_app (generalize lvl ty, List.map ty_args ~f:(generalize lvl))
  | Ty_var { contents = Ty_var_link ty } -> generalize lvl ty
  | Ty_var { contents = Ty_var_generic _ } -> ty
  | Ty_var { contents = Ty_var_unbound { id; lvl = var_lvl } } ->
    if var_lvl > lvl then Ty_var { contents = Ty_var_generic id } else ty

let rec occurs_check lvl id ty =
  match ty with
  | Expr.Ty_const _ -> ()
  | Ty_arr (args, ret) ->
    List.iter args ~f:(occurs_check lvl id);
    occurs_check lvl id ret
  | Ty_app (f, args) ->
    occurs_check lvl id f;
    List.iter args ~f:(occurs_check lvl id)
  | Ty_var { contents = Ty_var_link ty } -> occurs_check lvl id ty
  | Ty_var { contents = Ty_var_generic _ } -> ()
  | Ty_var ({ contents = Ty_var_unbound v } as var) ->
    if v.id = id then type_error "recursive types"
    else if v.lvl < lvl then var := Ty_var_unbound { id = v.id; lvl }
    else ()

let rec unify (ty1 : Expr.ty) (ty2 : Expr.ty) =
  if phys_equal ty1 ty2 then ()
  else
    match (ty1, ty2) with
    | Ty_const name1, Ty_const name2 ->
      if not String.(name1 = name2) then type_error "unification error"
    | Ty_arr (args1, ret1), Ty_arr (args2, ret2) ->
      List.iter2_exn args1 args2 ~f:unify;
      unify ret1 ret2
    | Ty_app (f1, args1), Ty_app (f2, args2) ->
      unify f1 f2;
      List.iter2_exn args1 args2 ~f:unify
    | Ty_var { contents = Ty_var_link ty1 }, ty2
    | ty1, Ty_var { contents = Ty_var_link ty2 } ->
      unify ty1 ty2
    | Ty_var ({ contents = Ty_var_unbound { id; lvl } } as var), ty
    | ty, Ty_var ({ contents = Ty_var_unbound { id; lvl } } as var) ->
      occurs_check lvl id ty;
      var := Ty_var_link ty
    | ty1, ty2 ->
      type_error_doc
        PPrint.(
          string "unification error of"
          ^^ nest 2 (break 1 ^^ Expr.doc_of_ty ty1)
          ^^ (break 1 ^^ string "with")
          ^^ nest 2 (break 1 ^^ Expr.doc_of_ty ty2))

let rec unify_abs lvl arity ty =
  match ty with
  | Expr.Ty_arr (ty_args, ty_ret) ->
    if List.length ty_args <> arity then type_error "arity mismatch";
    (ty_args, ty_ret)
  | Ty_var var -> (
    match !var with
    | Ty_var_link ty -> unify_abs lvl arity ty
    | Ty_var_unbound _ ->
      let ty_ret = newvar lvl () in
      let ty_args = List.init arity ~f:(fun _ -> newvar lvl ()) in
      (* TODO: do we need an occurs check here? probably not *)
      var := Ty_var_link (Ty_arr (ty_args, ty_ret));
      (ty_args, ty_ret)
    | Ty_var_generic _ -> failwith "uninstantiated generic type")
  | Ty_app _
  | Ty_const _ ->
    type_error "expected a function"

let rec infer' lvl env (e : Expr.expr) =
  match e with
  | Expr_name name ->
    let ty =
      match Map.find env name with
      | Some ty -> ty
      | None -> type_errorf "unknown name `%s`" name
    in
    instantiate lvl ty
  | Expr_abs (args, body) ->
    let ty_args = List.map args ~f:(fun _ -> newvar lvl ()) in
    let ty_body =
      let env =
        List.fold_left (List.zip_exn args ty_args) ~init:env
          ~f:(fun env (arg, ty_arg) -> Map.set env ~key:arg ~data:ty_arg)
      in
      infer' lvl env body
    in
    Expr.Ty_arr (ty_args, ty_body)
  | Expr_app (func, args) ->
    let ty_args, ty_ret =
      let ty_func = infer' lvl env func in
      unify_abs lvl (List.length args) ty_func
    in
    let () =
      List.iter2_exn args ty_args ~f:(fun arg ty_arg ->
          let ty = infer' lvl env arg in
          unify ty ty_arg)
    in
    ty_ret
  | Expr_let (name, e, b) ->
    let ty_e = infer' (lvl + 1) env e in
    let ty_e = generalize lvl ty_e in
    let env = Map.set env ~key:name ~data:ty_e in
    infer' lvl env b
  | Expr_let_rec (name, e, b) ->
    let ty_e =
      let env = Map.set env ~key:name ~data:(newvar lvl ()) in
      infer' (lvl + 1) env e
    in
    let ty_e = generalize lvl ty_e in
    let env = Map.set env ~key:name ~data:ty_e in
    infer' lvl env b
  | Expr_lit (Lit_string _) -> Expr.Ty_const "string"
  | Expr_lit (Lit_int _) -> Expr.Ty_const "int"

let infer env e = generalize 0 (infer' 1 env e)
