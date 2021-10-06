open! Base

type env = (String.t, Expr.ty, String.comparator_witness) Map.t

type error =
  | Error_unification of Expr.ty * Expr.ty
  | Error_recursive_types
  | Error_recursive_row_types
  | Error_not_a_function
  | Error_unknown_name of string
  | Error_arity_mismatch of int * int

let doc_of_error =
  PPrint.(
    function
    | Error_recursive_types -> string "recursive types"
    | Error_recursive_row_types -> string "recursive row types"
    | Error_not_a_function -> string "expected a function"
    | Error_unknown_name name -> string "unknown name: " ^^ string name
    | Error_arity_mismatch (expected, got) ->
      string "arity mismatch: expected"
      ^^ string (Int.to_string expected)
      ^^ string " but got "
      ^^ string (Int.to_string got)
    | Error_unification (ty1, ty2) ->
      string "unification error of"
      ^^ nest 2 (break 1 ^^ Expr.doc_of_ty ty1)
      ^^ (break 1 ^^ string "with")
      ^^ nest 2 (break 1 ^^ Expr.doc_of_ty ty2))

let pp_error = Expr.pp' doc_of_error

let show_error = Expr.show' doc_of_error

exception Type_error of error

let type_error err = raise (Type_error err)

let currentid = ref 0

let resetid () = currentid := 0

let nextid () =
  Int.incr currentid;
  !currentid

let newvar ?id lvl () =
  let id =
    match id with
    | Some id -> id
    | None -> nextid ()
  in
  Expr.Ty_var { contents = Ty_var_unbound { id; lvl } }

let newrowvar ?id lvl () =
  let id =
    match id with
    | Some id -> id
    | None -> nextid ()
  in
  Expr.Ty_row_var { contents = Ty_var_unbound { id; lvl } }

let newgenvar () = Expr.Ty_var { contents = Ty_var_generic (nextid ()) }

let instantiate lvl (ty : Expr.ty) : Expr.ty =
  let vars = Hashtbl.create (module Int) in
  let rowvars = Hashtbl.create (module Int) in
  let rec instantiate_ty (ty : Expr.ty) : Expr.ty =
    match ty with
    | Ty_const _ -> ty
    | Ty_arr (ty_args, ty_ret) ->
      Ty_arr (List.map ty_args ~f:instantiate_ty, instantiate_ty ty_ret)
    | Ty_app (ty, ty_args) ->
      Ty_app (instantiate_ty ty, List.map ty_args ~f:instantiate_ty)
    | Ty_var { contents = Ty_var_link ty } -> instantiate_ty ty
    | Ty_var { contents = Ty_var_unbound _ } -> ty
    | Ty_var { contents = Ty_var_generic id } ->
      Hashtbl.find_or_add vars id ~default:(newvar lvl)
    | Ty_record row -> Ty_record (instantiate_ty_row row)
  and instantiate_ty_row (ty_row : Expr.ty_row) =
    match ty_row with
    | Ty_row_field (name, ty, ty_row) ->
      Ty_row_field (name, instantiate_ty ty, instantiate_ty_row ty_row)
    | Ty_row_empty -> ty_row
    | Ty_row_var { contents = Ty_var_link ty_row } -> instantiate_ty_row ty_row
    | Ty_row_var { contents = Ty_var_unbound _ } -> ty_row
    | Ty_row_var { contents = Ty_var_generic id } ->
      Hashtbl.find_or_add rowvars id ~default:(newrowvar lvl)
  in
  instantiate_ty ty

let generalize lvl (ty : Expr.ty) =
  let rec generalize_ty ty =
    match ty with
    | Expr.Ty_const _ -> ty
    | Ty_arr (ty_args, ty_ret) ->
      Ty_arr (List.map ty_args ~f:generalize_ty, generalize_ty ty_ret)
    | Ty_app (ty, ty_args) ->
      Ty_app (generalize_ty ty, List.map ty_args ~f:generalize_ty)
    | Ty_var { contents = Ty_var_link ty } -> generalize_ty ty
    | Ty_var { contents = Ty_var_generic _ } -> ty
    | Ty_var { contents = Ty_var_unbound { id; lvl = var_lvl } } ->
      if var_lvl > lvl then Ty_var { contents = Ty_var_generic id } else ty
    | Ty_record row -> Ty_record (generalize_ty_row row)
  and generalize_ty_row (ty_row : Expr.ty_row) =
    match ty_row with
    | Ty_row_field (name, ty, row) ->
      Ty_row_field (name, generalize_ty ty, generalize_ty_row row)
    | Ty_row_empty -> ty_row
    | Ty_row_var { contents = Ty_var_link ty_row } -> generalize_ty_row ty_row
    | Ty_row_var { contents = Ty_var_generic _ } -> ty_row
    | Ty_row_var { contents = Ty_var_unbound { id; lvl = var_lvl } } ->
      if var_lvl > lvl then Ty_row_var { contents = Ty_var_generic id }
      else ty_row
  in
  generalize_ty ty

let occurs_check lvl id ty =
  let rec occurs_check_ty (ty : Expr.ty) : unit =
    match ty with
    | Expr.Ty_const _ -> ()
    | Ty_arr (args, ret) ->
      List.iter args ~f:occurs_check_ty;
      occurs_check_ty ret
    | Ty_app (f, args) ->
      occurs_check_ty f;
      List.iter args ~f:occurs_check_ty
    | Ty_var { contents = Ty_var_link ty } -> occurs_check_ty ty
    | Ty_var { contents = Ty_var_generic _ } -> ()
    | Ty_var ({ contents = Ty_var_unbound v } as var) ->
      if v.id = id then type_error Error_recursive_types
      else if lvl < v.lvl then var := Ty_var_unbound { id = v.id; lvl }
      else ()
    | Ty_record ty_row -> occurs_check_ty_row ty_row
  and occurs_check_ty_row (ty_row : Expr.ty_row) : unit =
    match ty_row with
    | Ty_row_field (_name, ty, ty_row) ->
      occurs_check_ty ty;
      occurs_check_ty_row ty_row
    | Ty_row_empty -> ()
    | Ty_row_var { contents = Ty_var_link ty_row } -> occurs_check_ty_row ty_row
    | Ty_row_var { contents = Ty_var_generic _ } -> ()
    | Ty_row_var ({ contents = Ty_var_unbound v } as var) ->
      if v.id = id then type_error Error_recursive_types
      else if lvl < v.lvl then var := Ty_var_unbound { id = v.id; lvl }
      else ()
  in
  occurs_check_ty ty

let rec unify (ty1 : Expr.ty) (ty2 : Expr.ty) =
  if phys_equal ty1 ty2 then ()
  else
    match (ty1, ty2) with
    | Ty_const name1, Ty_const name2 ->
      if not String.(name1 = name2) then
        type_error (Error_unification (ty1, ty2))
    | Ty_arr (args1, ret1), Ty_arr (args2, ret2) ->
      List.iter2_exn args1 args2 ~f:unify;
      unify ret1 ret2
    | Ty_app (f1, args1), Ty_app (f2, args2) ->
      unify f1 f2;
      List.iter2_exn args1 args2 ~f:unify
    | Ty_record row1, Ty_record row2 -> unify_row row1 row2
    | Ty_var { contents = Ty_var_link ty1 }, ty2
    | ty1, Ty_var { contents = Ty_var_link ty2 } ->
      unify ty1 ty2
    | Ty_var ({ contents = Ty_var_unbound { id; lvl } } as var), ty
    | ty, Ty_var ({ contents = Ty_var_unbound { id; lvl } } as var) ->
      occurs_check lvl id ty;
      var := Ty_var_link ty
    | ty1, ty2 -> type_error (Error_unification (ty1, ty2))

and unify_row row1 row2 =
  if phys_equal row1 row2 then ()
  else
    match (row1, row2) with
    | Ty_row_empty, Ty_row_empty -> ()
    | Ty_row_field (name, ty, row1), Ty_row_field _ ->
      let exception Row_rewrite_error in
      let rec rewrite = function
        | Expr.Ty_row_empty -> raise Row_rewrite_error
        | Ty_row_field (name', ty', row') ->
          if String.(name = name') then (
            unify ty ty';
            row')
          else Ty_row_field (name', ty', rewrite row')
        | Ty_row_var { contents = Ty_var_link row' } -> rewrite row'
        | Ty_row_var ({ contents = Ty_var_unbound { id = _; lvl } } as var) ->
          let row' = newrowvar lvl () in
          var := Ty_var_link (Ty_row_field (name, ty, row'));
          row'
        | Ty_row_var { contents = Ty_var_generic _ } ->
          failwith "non instantiated row variable"
      in
      let row1_unbound =
        match row1 with
        | Ty_row_var ({ contents = Ty_var_unbound _ } as var) -> Some var
        | _ -> None
      in
      let row2 =
        try rewrite row2 with
        | Row_rewrite_error ->
          type_error (Error_unification (Ty_record row1, Ty_record row2))
      in
      (match row1_unbound with
      | Some { contents = Ty_var_link _ } ->
        type_error Error_recursive_row_types
      | _ -> ());
      unify_row row1 row2
    | Ty_row_var { contents = Ty_var_link row1 }, row2
    | row2, Ty_row_var { contents = Ty_var_link row1 } ->
      unify_row row1 row2
    | Ty_row_var ({ contents = Ty_var_unbound { id; lvl } } as var), row
    | row, Ty_row_var ({ contents = Ty_var_unbound { id; lvl } } as var) ->
      occurs_check lvl id (Ty_record row);
      var := Ty_var_link row
    | row1, row2 ->
      type_error (Error_unification (Ty_record row1, Ty_record row2))

let rec unify_abs arity ty =
  match ty with
  | Expr.Ty_arr (ty_args, ty_ret) ->
    if List.length ty_args <> arity then
      type_error (Error_arity_mismatch (arity, List.length ty_args));
    (ty_args, ty_ret)
  | Ty_var var -> (
    match !var with
    | Ty_var_link ty -> unify_abs arity ty
    | Ty_var_unbound v ->
      let ty_ret = newvar v.lvl () in
      let ty_args = List.init arity ~f:(fun _ -> newvar v.lvl ()) in
      var := Ty_var_link (Ty_arr (ty_args, ty_ret));
      (ty_args, ty_ret)
    | Ty_var_generic _ -> failwith "uninstantiated generic type")
  | Ty_app _
  | Ty_const _
  | Ty_record _ ->
    type_error Error_not_a_function

let rec infer' lvl env (e : Expr.expr) =
  match e with
  | Expr_name name ->
    let ty =
      match Map.find env name with
      | Some ty -> ty
      | None -> type_error (Error_unknown_name name)
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
      unify_abs (List.length args) ty_func
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
  | Expr_record fields ->
    let ty_row =
      List.fold_left fields ~init:Expr.Ty_row_empty ~f:(fun row (label, e) ->
          let ty_e = infer' lvl env e in
          Ty_row_field (label, ty_e, row))
    in
    Expr.Ty_record ty_row
  | Expr_record_proj (e, label) ->
    let ty_e = infer' lvl env e in
    let ty_proj = newvar lvl () in
    unify ty_e
      (Expr.Ty_record (Ty_row_field (label, ty_proj, newrowvar lvl ())));
    ty_proj
  | Expr_record_extend (e, fields) ->
    let ty_row = newrowvar lvl () in
    let return_ty_row =
      List.fold_left fields ~init:ty_row ~f:(fun ty_row (label, e) ->
          let ty_e = newvar lvl () in
          unify ty_e (infer' lvl env e);
          Ty_row_field (label, ty_e, ty_row))
    in
    unify (Expr.Ty_record ty_row) (infer' lvl env e);
    Expr.Ty_record return_ty_row
  | Expr_record_update (e, fields) ->
    let ty_row = newrowvar lvl () in
    let return_ty_row, _, to_unify =
      let labels = Set.empty (module String) in
      List.fold_left fields ~init:(ty_row, labels, [])
        ~f:(fun (ty_row, labels, to_unify) (label, e) ->
          (* if Set.mem labels label then *)
          (*   type_errorf "duplicate record label: `%s`" label *)
          (* else *)
          let ty_e = newvar lvl () in
          ( Ty_row_field (label, ty_e, ty_row),
            Set.add labels label,
            (e, ty_e) :: to_unify ))
    in
    unify (Expr.Ty_record return_ty_row) (infer' lvl env e);
    List.iter (List.rev to_unify) ~f:(fun (e, ty_e) ->
        unify ty_e (infer' lvl env e));
    Expr.Ty_record return_ty_row
  | Expr_lit (Lit_string _) -> Expr.Ty_const "string"
  | Expr_lit (Lit_int _) -> Expr.Ty_const "int"

let infer env e = generalize (-1) (infer' 0 env e)
