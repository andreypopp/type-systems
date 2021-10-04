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

let newvar () = Expr.Ty_var { contents = Ty_var_unbound (nextid ()) }

let instantiate (ty : Expr.ty) =
  let vars = Hashtbl.create (module Int) in
  let rec aux ty =
    match ty with
    | Expr.Ty_const _ -> ty
    | Ty_arr (ty_args, ty_ret) -> Ty_arr (List.map ty_args ~f:aux, aux ty_ret)
    | Ty_app (ty, ty_args) -> Ty_app (aux ty, List.map ty_args ~f:aux)
    | Ty_var { contents = Ty_var_link ty } -> aux ty
    | Ty_var { contents = Ty_var_unbound _ } -> ty
    | Ty_var { contents = Ty_var_generic id } ->
      Hashtbl.find_or_add vars id ~default:newvar
  in
  aux ty

let rec generalize (ty : Expr.ty) =
  match ty with
  | Ty_const _ -> ty
  | Ty_arr (ty_args, ty_ret) ->
    Ty_arr (List.map ty_args ~f:generalize, generalize ty_ret)
  | Ty_app (ty, ty_args) ->
    Ty_app (generalize ty, List.map ty_args ~f:generalize)
  | Ty_var { contents = Ty_var_link ty } -> generalize ty
  | Ty_var { contents = Ty_var_generic _ } -> ty
  | Ty_var { contents = Ty_var_unbound id } ->
    (* TODO: this is unsound as we generalizing all unbound vars! *)
    Ty_var { contents = Ty_var_generic id }

let rec occurs_check v ty =
  match ty with
  | Expr.Ty_const _ -> ()
  | Ty_arr (args, ret) ->
    List.iter args ~f:(occurs_check v);
    occurs_check v ret
  | Ty_app (f, args) ->
    occurs_check v f;
    List.iter args ~f:(occurs_check v)
  | Ty_var { contents = Ty_var_link ty } -> occurs_check v ty
  | Ty_var { contents = Ty_var_unbound id } ->
    if id = v then type_error "recursive types"
  | Ty_var { contents = Ty_var_generic _ } -> ()

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
    | Ty_var ({ contents = Ty_var_unbound id } as var), ty
    | ty, Ty_var ({ contents = Ty_var_unbound id } as var) ->
      occurs_check id ty;
      var := Ty_var_link ty
    | ty1, ty2 ->
      type_error_doc
        PPrint.(
          string "unification error of"
          ^^ nest 2 (break 1 ^^ Expr.doc_of_ty ty1)
          ^^ (break 1 ^^ string "with")
          ^^ nest 2 (break 1 ^^ Expr.doc_of_ty ty2))

let rec unify_abs arity ty =
  match ty with
  | Expr.Ty_arr (ty_args, ty_ret) ->
    if List.length ty_args <> arity then type_error "arity mismatch";
    (ty_args, ty_ret)
  | Ty_var var -> (
    match !var with
    | Ty_var_link ty -> unify_abs arity ty
    | Ty_var_unbound _ ->
      let ty_ret = newvar () in
      let ty_args = List.init arity ~f:(fun _ -> newvar ()) in
      (* TODO: do we need an occurs check here? probably not *)
      var := Ty_var_link (Ty_arr (ty_args, ty_ret));
      (ty_args, ty_ret)
    | Ty_var_generic _ -> failwith "uninstantiated generic type")
  | Ty_app _
  | Ty_const _ ->
    type_error "expected a function"

let rec infer' env (e : Expr.expr) =
  match e with
  | Expr_name name ->
    let ty =
      match Map.find env name with
      | Some ty -> ty
      | None -> type_errorf "unknown name `%s`" name
    in
    instantiate ty
  | Expr_abs (args, body) ->
    let ty_args = List.map args ~f:(fun _ -> newvar ()) in
    let ty_body =
      let env =
        List.fold_left (List.zip_exn args ty_args) ~init:env
          ~f:(fun env (arg, ty_arg) -> Map.set env ~key:arg ~data:ty_arg)
      in
      infer' env body
    in
    Expr.Ty_arr (ty_args, ty_body)
  | Expr_app (func, args) ->
    let ty_args, ty_ret =
      let ty_func = infer' env func in
      unify_abs (List.length args) ty_func
    in
    let () =
      List.iter2_exn args ty_args ~f:(fun arg ty_arg ->
          let ty = infer' env arg in
          unify ty ty_arg)
    in
    ty_ret
  | Expr_let (name, e, b) ->
    let ty_e = infer' env e in
    let ty_e = generalize ty_e in
    let env = Map.set env ~key:name ~data:ty_e in
    infer' env b
  | Expr_lit (Lit_string _) -> Expr.Ty_const "string"
  | Expr_lit (Lit_int _) -> Expr.Ty_const "int"

let infer env e = generalize (infer' env e)
