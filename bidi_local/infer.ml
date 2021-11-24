open! Import
open! Syntax

(** Typing environment. *)
module Env : sig
  type t

  type val_kind = Val_top | Val_local

  val empty : t

  val add_val : ?kind:val_kind -> t -> name -> ty_sch -> t

  val find_val : t -> name -> (val_kind * ty_sch) option

  val add_var : t -> name -> var -> t

  val build_ty_subst : ?init:Ty_subst.t -> t -> Ty_subst.t
end = struct
  type t = {
    vals : (name, val_kind * ty_sch, String.comparator_witness) Map.t;
    vars : (name, var, String.comparator_witness) Map.t;
  }

  and val_kind = Val_top | Val_local

  let add_val ?(kind = Val_local) env name ty_sch =
    { env with vals = Map.set env.vals ~key:name ~data:(kind, ty_sch) }

  let add_var env name var =
    { env with vars = Map.set env.vars ~key:name ~data:var }

  let find_val env name = Map.find env.vals name

  let empty =
    { vals = Map.empty (module String); vars = Map.empty (module String) }

  let build_ty_subst ?(init = Ty_subst.empty) env =
    Map.fold env.vars ~init ~f:(fun ~key:name ~data:v subst ->
        Ty_subst.add_name subst name v)
end

type ctx = { env : Env.t; lvl : lvl; variance : Variance.t }
(** Information we need to pass between different typechecking routines. *)

(** [instantiate ~lvl ty_sch] instantiates type scheme [ty_sch] into [ty] type.

    It does so by substituting all generic type variables with fresh type
    variables at specific level [lvl].
  *)
let instantiate ?(val_kind = Env.Val_local) ?env ~lvl ~variance ty_sch =
  let vs, ty = ty_sch in
  let subst =
    List.fold vs ~init:Ty_subst.empty ~f:(fun subst v ->
        let v' =
          match val_kind with
          | Env.Val_local -> Var.refresh ~lvl v
          | Env.Val_top -> Var.fresh ~lvl ()
        in
        Ty_subst.add_var subst v v')
  in
  let subst =
    match env with
    | None -> subst
    | Some env -> Env.build_ty_subst ~init:subst env
  in
  let ty = Ty_subst.apply_ty ~variance subst ty in
  if Debug.log_instantiate then
    Caml.Format.printf "INST lvl:%i %s@." lvl (Ty.show ty);
  ty

(** [generalize ~lvl ty] generalizes type [ty] to a type scheme.

    It finds all unresolved type variables marked with level > [lvl] and makes
    them generalized type variables. The level check acts as a scope check so we
    don't generalize over variables from the outer scope.
  *)
let generalize ~lvl ty =
  let vs = ref [] in
  let rec aux = function
    | Ty_top
    | Ty_bot
    | Ty_const _ ->
      ()
    | Ty_arr (args, ty) ->
      List.iter args ~f:aux;
      aux ty
    | Ty_app (ty, args) ->
      List.iter args ~f:aux;
      aux ty
    | Ty_nullable ty -> aux ty
    | Ty_var v -> (
      match Var.ty v with
      | Some ty -> aux ty
      | None -> if Var.lvl v > lvl then vs := v :: !vs else ())
    | Ty_record row -> aux row
    | Ty_row_empty -> ()
    | Ty_row_extend ((_, ty), row) ->
      aux ty;
      aux row
  in
  aux ty;
  let ty_sch = (List.dedup_and_sort ~compare:Var.compare !vs, ty) in
  if Debug.log_instantiate then
    Caml.Format.printf "GENR lvl:%i %s@." lvl (Ty_sch.show ty_sch);
  ty_sch

let rec promote ~lvl (ty : ty) =
  match ty with
  | Ty_const _ -> ty
  | Ty_var v -> (
    match Var.ty v with
    | None -> if Var.lvl v > lvl then Ty_top else ty
    | Some ty -> promote ~lvl ty)
  | Ty_app (ty, args) ->
    Ty_app (promote ~lvl ty, List.map args ~f:(promote ~lvl))
  | Ty_nullable ty -> Ty_nullable (promote ~lvl ty)
  | Ty_arr (args, ty) -> Ty_arr (List.map args ~f:(demote ~lvl), promote ~lvl ty)
  | Ty_record row -> Ty_record (promote ~lvl row)
  | Ty_row_empty -> ty
  | Ty_row_extend ((name, ty), row) ->
    Ty_row_extend ((name, promote ~lvl ty), promote ~lvl row)
  | Ty_bot -> ty
  | Ty_top -> ty

and demote ~lvl (ty : ty) =
  match ty with
  | Ty_const _ -> ty
  | Ty_var v -> (
    match Var.ty v with
    | None -> if Var.lvl v > lvl then Ty_bot else ty
    | Some ty -> demote ~lvl ty)
  | Ty_app (ty, args) -> Ty_app (promote ~lvl ty, List.map args ~f:(demote ~lvl))
  | Ty_nullable ty -> Ty_nullable (demote ~lvl ty)
  | Ty_arr (args, ty) -> Ty_arr (List.map args ~f:(promote ~lvl), demote ~lvl ty)
  | Ty_record row -> Ty_record (demote ~lvl row)
  | Ty_row_empty -> ty
  | Ty_row_extend ((name, ty), row) ->
    Ty_row_extend ((name, demote ~lvl ty), demote ~lvl row)
  | Ty_bot -> ty
  | Ty_top -> ty

let subsumes ~lvl constraints =
  let exception Row_rewrite_error in
  let rec aux ~super_ty ~sub_ty =
    if Debug.log_solve then
      Caml.Format.printf "??? %s <: %s@." (Ty.show sub_ty) (Ty.show super_ty);
    if phys_equal super_ty sub_ty || Ty.equal super_ty sub_ty then ()
    else
      match (sub_ty, super_ty) with
      | Ty_const name, Ty_const name' ->
        if not (String.equal name name') then
          Type_error.raise_not_a_subtype ~sub_ty ~super_ty
      | Ty_nullable sub_ty', Ty_nullable super_ty' ->
        aux ~super_ty:super_ty' ~sub_ty:sub_ty'
      | sub_ty', Ty_nullable super_ty' ->
        aux ~super_ty:super_ty' ~sub_ty:sub_ty'
      | Ty_app (sub_ty', sub_args), Ty_app (super_ty', super_args) -> (
        aux ~super_ty:super_ty' ~sub_ty:sub_ty';
        match
          List.iter2 super_args sub_args ~f:(fun super_ty' sub_ty' ->
              aux ~super_ty:super_ty' ~sub_ty:sub_ty')
        with
        | Unequal_lengths -> Type_error.raise_not_a_subtype ~sub_ty ~super_ty
        | Ok () -> ())
      | Ty_arr (sub_args, sub_ty'), Ty_arr (super_args, super_ty') ->
        (match
           List.iter2 super_args sub_args ~f:(fun super_ty' sub_ty' ->
               aux ~sub_ty:super_ty' ~super_ty:sub_ty')
         with
        | Unequal_lengths -> Type_error.raise_not_a_subtype ~sub_ty ~super_ty
        | Ok () -> ());
        aux ~sub_ty:sub_ty' ~super_ty:super_ty'
      | Ty_record sub_row, Ty_record super_row -> (
        try aux_row ~sub_row ~super_row with
        | Row_rewrite_error -> Type_error.raise_not_a_subtype ~sub_ty ~super_ty)
      | Ty_var sub_v, Ty_var super_v -> (
        match (Var.ty sub_v, Var.ty super_v) with
        | None, None -> Subtyping.union_vars sub_v super_v
        | Some sub_ty, None ->
          Subtyping.Constraint_set.add constraints super_v
            (promote ~lvl sub_ty, Ty_top)
        | None, Some super_ty ->
          Subtyping.Constraint_set.add constraints sub_v
            (Ty_bot, demote ~lvl super_ty)
        | Some sub_ty, Some super_ty -> aux ~sub_ty ~super_ty)
      | Ty_var sub_v, super_ty -> (
        match Var.ty sub_v with
        | Some sub_ty -> aux ~super_ty ~sub_ty
        | None ->
          Subtyping.Constraint_set.add constraints sub_v
            (Ty_bot, demote ~lvl super_ty))
      | sub_ty, Ty_var super_v -> (
        match Var.ty super_v with
        | Some super_ty -> aux ~super_ty ~sub_ty
        | None ->
          Subtyping.Constraint_set.add constraints super_v
            (promote ~lvl sub_ty, Ty_top))
      | _, Ty_top -> ()
      | Ty_bot, _ -> ()
      | _ -> Type_error.raise_not_a_subtype ~sub_ty ~super_ty
  and aux_row ~sub_row ~super_row =
    match (sub_row, super_row) with
    | Ty_row_empty, Ty_row_extend _ -> raise Row_rewrite_error
    | Ty_row_extend ((name, sub_ty), sub_row), Ty_row_extend _ ->
      let rec rewrite = function
        | Ty_row_empty -> raise Row_rewrite_error
        | Ty_row_extend ((name', super_ty), super_row) ->
          if String.(name = name') then (
            aux ~sub_ty ~super_ty;
            super_row)
          else Ty_row_extend ((name', super_ty), rewrite super_row)
        | Ty_var v -> (
          match Var.ty v with
          | Some super_row -> rewrite super_row
          | None ->
            let super_row' = Ty.var @@ Var.fresh ~lvl:(Var.lvl v) () in
            Var.set_ty v (Ty_row_extend ((name, sub_ty), super_row'));
            super_row')
        | _ -> assert false
      in
      let subrow_unbound =
        match sub_row with
        | Ty_var v -> if Var.is_empty v then Some v else None
        | _ -> None
      in
      let super_row = rewrite super_row in
      (match subrow_unbound with
      | Some v ->
        if not (Var.is_empty v) then
          Type_error.raise Error_recursive_record_type
      | _ -> ());
      aux_row ~sub_row ~super_row
    | Ty_var sub_v, Ty_row_extend ((name, super_ty), super_row) -> (
      match Var.ty sub_v with
      | Some sub_ty -> aux ~super_ty ~sub_ty
      | None ->
        let sub_row = Ty.var @@ Var.fresh ~lvl:(Var.lvl sub_v) () in
        let sub_ty = Ty_row_extend ((name, super_ty), sub_row) in
        Var.set_ty sub_v sub_ty;
        aux_row ~sub_row ~super_row)
    | Ty_row_extend ((name, sub_ty), sub_row), Ty_var super_v -> (
      match Var.ty super_v with
      | Some super_ty -> aux ~super_ty ~sub_ty
      | None ->
        let super_row = Ty.var @@ Var.fresh ~lvl:(Var.lvl super_v) () in
        let super_ty = Ty_row_extend ((name, sub_ty), sub_row) in
        Var.set_ty super_v super_ty;
        aux_row ~sub_row ~super_row)
    | sub_row, super_row -> aux ~sub_ty:sub_row ~super_ty:super_row
  in
  aux

let fresh_fun_ty ~arity v =
  let lvl = Var.lvl v in
  let args_ty = List.init arity ~f:(fun _ -> Ty.var (Var.fresh ~lvl ())) in
  let body_ty = Ty.var (Var.fresh ~lvl ()) in
  Var.set_ty v (Ty_arr (args_ty, body_ty));
  (args_ty, body_ty)

let fresh_record_ty v =
  let lvl = Var.lvl v in
  let row = Ty_var (Var.fresh ~lvl ()) in
  let ty = Ty_record row in
  Var.set_ty v ty;
  ty

let resolve_ty ty =
  match ty with
  | Ty_var v as ty -> Option.value (Var.ty v) ~default:ty
  | ty -> ty

let rec synth ~ctx expr =
  let ty, expr = synth' ~ctx expr in
  (resolve_ty ty, expr)

and synth' ~ctx expr =
  if Debug.log_check then
    Caml.Format.printf "SYNTH%s %s@."
      (Variance.show ctx.variance)
      (Expr.show expr);
  match expr with
  | E_var name ->
    let ty =
      match Env.find_val ctx.env name with
      | None -> Type_error.raise (Error_unknown_name name)
      | Some (val_kind, ty_sch) ->
        instantiate ~val_kind ~lvl:ctx.lvl ~variance:ctx.variance ty_sch
    in
    (ty, expr)
  | E_ann (expr, ty_sch) ->
    let ty =
      instantiate ~env:ctx.env ~lvl:ctx.lvl ~variance:ctx.variance ty_sch
    in
    (* TODO: here we drop E_ann, is this ok? *)
    (ty, check ~ctx expr ty)
  | E_abs (vs, args, body) ->
    let env, vs =
      List.fold vs ~init:(ctx.env, []) ~f:(fun (env, vs) v ->
          let v = Var.refresh ~lvl:ctx.lvl v in
          (Env.add_var env (Var.name v) v, v :: vs))
    in
    let env, args, args_ty =
      List.fold args ~init:(env, [], [])
        ~f:(fun (env, args, args_ty) (name, ty) ->
          match ty with
          | None ->
            Type_error.raise (Error_missing_type_annotation (E_var name))
          | Some ty ->
            let ty =
              instantiate ~env ~lvl:ctx.lvl
                ~variance:(Variance.inv ctx.variance)
                ([], ty)
            in
            ( Env.add_val env name ([], ty),
              (name, Some ty) :: args,
              ty :: args_ty ))
    in
    let body_ty, body = synth ~ctx:{ ctx with env } body in
    let vs =
      (* Only keep variables which were not solved during checking args and
         body. *)
      List.filter vs ~f:Var.is_empty
    in
    ( Ty_arr (List.rev args_ty, body_ty),
      E_abs (List.rev vs, List.rev args, body) )
  | E_app (f, args) ->
    (* S-App-InfAlg *)
    let (args_tys, body_ty), f =
      match synth ~ctx f with
      | Ty_arr (args_tys, body_ty), f -> ((args_tys, body_ty), f)
      | Ty_var v, f ->
        assert (Var.is_empty v);
        (fresh_fun_ty v ~arity:(List.length args), f)
      | ty, _ -> Type_error.raise (Error_expected_a_function ty)
    in
    let constraints = Subtyping.Constraint_set.empty () in
    let args =
      match
        List.map2 args_tys args ~f:(fun ty arg ->
            check'
              ~ctx:{ ctx with variance = Variance.inv ctx.variance }
              ~constraints arg ty)
      with
      | Unequal_lengths -> Type_error.raise Error_arity_mismatch
      | Ok args -> args
    in
    Subtyping.Constraint_set.solve constraints;
    let expr = E_app (f, args) in
    if Debug.log_solve then
      Caml.Format.printf "== SOLVED %s@."
        (Expr.show (E_ann (expr, ([], body_ty))));
    (body_ty, E_app (f, args))
  | E_record fields ->
    let row, fields =
      (* List.fold fields ~init:(Ty_row_empty, []) *)
      List.fold_right fields ~init:(Ty_row_empty, [])
        ~f:(fun (name, expr) (row, fields) ->
          let ty, expr = synth ~ctx expr in
          (Ty_row_extend ((name, ty), row), (name, expr) :: fields))
    in
    (Ty_record row, E_record fields)
  | E_record_project (expr, name) ->
    let row = Ty.var @@ Var.fresh ~lvl:ctx.lvl () in
    let ty = Ty.var @@ Var.fresh ~lvl:ctx.lvl () in
    let record_ty = Ty_record (Ty_row_extend ((name, ty), row)) in
    let constraints = Subtyping.Constraint_set.empty () in
    let expr = check' ~ctx ~constraints expr record_ty in
    Subtyping.Constraint_set.solve constraints;
    (ty, E_record_project (expr, name))
  | E_record_extend (expr, fields) ->
    let constraints = Subtyping.Constraint_set.empty () in
    let row = Ty.var @@ Var.fresh ~lvl:ctx.lvl () in
    let expr = check' ~ctx ~constraints expr (Ty_record row) in
    let row, fields =
      List.fold fields ~init:(row, []) ~f:(fun (row, fields) (name, expr) ->
          let ty, expr = synth ~ctx expr in
          (Ty_row_extend ((name, ty), row), (name, expr) :: fields))
    in
    let ty = Ty_record row in
    Subtyping.Constraint_set.solve constraints;
    (ty, E_record_extend (expr, List.rev fields))
  | E_record_update (expr, fields) ->
    let constraints = Subtyping.Constraint_set.empty () in
    let row = Ty.var @@ Var.fresh ~lvl:ctx.lvl () in
    let row, fields =
      List.fold fields ~init:(row, []) ~f:(fun (row, fields) (name, expr) ->
          let ty, expr = synth ~ctx expr in
          (Ty_row_extend ((name, ty), row), (name, expr) :: fields))
    in
    let ty = Ty_record row in
    let ty', expr = synth ~ctx expr in
    subsumes ~lvl:ctx.lvl constraints ~sub_ty:ty ~super_ty:ty';
    Subtyping.Constraint_set.solve constraints;
    (ty, E_record_update (expr, List.rev fields))
  | E_lit (Lit_string _) -> (Ty_const "string", expr)
  | E_lit (Lit_int _) -> (Ty_const "int", expr)
  | E_let ((name, expr, e_ty_sch), body) ->
    let e_ty, expr =
      match e_ty_sch with
      | None -> synth ~ctx:{ ctx with lvl = ctx.lvl + 1 } expr
      | Some e_ty_sch ->
        let e_ty =
          instantiate ~env:ctx.env ~lvl:(ctx.lvl + 1) ~variance:ctx.variance
            e_ty_sch
        in
        (e_ty, check ~ctx:{ ctx with lvl = ctx.lvl + 1 } expr e_ty)
    in
    let e_ty_sch = generalize ~lvl:ctx.lvl e_ty in
    let env = Env.add_val ctx.env name e_ty_sch in
    let body_ty, body = synth ~ctx:{ ctx with env } body in
    (body_ty, E_let ((name, expr, Some e_ty_sch), body))

and check' ~ctx ~constraints expr ty =
  if Debug.log_check then
    Caml.Format.printf "CHECK%s %s : %s@."
      (Variance.show ctx.variance)
      (Expr.show expr) (Ty.show ty);
  match expr with
  | E_abs (vs, args, body) ->
    let env, vs =
      List.fold vs ~init:(ctx.env, []) ~f:(fun (env, vs) v ->
          let v = Var.refresh ~lvl:ctx.lvl v in
          (Env.add_var env (Var.name v) v, v :: vs))
    in
    let args_ty, body_ty =
      match resolve_ty ty with
      | Ty_arr (args_ty, ret_ty) -> (args_ty, ret_ty)
      | Ty_var v ->
        assert (Var.is_empty v);
        fresh_fun_ty v ~arity:(List.length args)
      | ty -> Type_error.raise (Error_expected_a_function ty)
    in
    let env, args =
      match
        List.fold2 args args_ty ~init:(env, [])
          ~f:(fun (env, args) (name, ty') ty ->
            Option.iter ty' ~f:(fun ty' ->
                subsumes ~lvl:ctx.lvl constraints ~sub_ty:ty ~super_ty:ty');
            let env = Env.add_val env name ([], ty) in
            (env, (name, Some ty) :: args))
      with
      | Unequal_lengths -> Type_error.raise Error_arity_mismatch
      | Ok (env, args) -> (env, List.rev args)
    in
    let body = check' ~ctx:{ ctx with env } ~constraints body body_ty in
    E_abs (List.rev vs, args, body)
  | E_app (f, args) ->
    let f_ty, f = synth ~ctx f in
    let args_tys, args = args |> List.map ~f:(synth ~ctx) |> List.unzip in
    let args_tys', ty' =
      match resolve_ty f_ty with
      | Ty_arr (args_tys', ty') -> (args_tys', ty')
      | Ty_var v ->
        assert (Var.is_empty v);
        fresh_fun_ty v ~arity:(List.length args)
      | ty -> Type_error.raise (Error_expected_a_function ty)
    in
    let () =
      match
        List.iter2 args_tys' args_tys ~f:(fun ty' ty ->
            subsumes ~lvl:ctx.lvl constraints ~sub_ty:ty ~super_ty:ty')
      with
      | Unequal_lengths -> Type_error.raise Error_arity_mismatch
      | Ok () -> ()
    in
    subsumes ~lvl:ctx.lvl constraints ~sub_ty:ty' ~super_ty:ty;
    E_app (f, args)
  | expr ->
    let ty', expr = synth ~ctx expr in
    subsumes ~lvl:ctx.lvl constraints ~sub_ty:ty' ~super_ty:ty;
    expr

and check ~ctx expr ty =
  let constraints = Subtyping.Constraint_set.empty () in
  let expr = check' ~ctx ~constraints expr ty in
  Subtyping.Constraint_set.solve constraints;
  expr

let infer ~env expr : (expr, Type_error.t) Result.t =
  let ctx = { lvl = 1; env; variance = Covariant } in
  try
    Ok
      (let ty, expr = synth ~ctx expr in
       let ty = generalize ~lvl:0 ty in
       match expr with
       | E_let ((name, _, _), E_var name') when String.equal name name' -> expr
       | expr -> E_ann (expr, ty))
  with
  | Type_error.Type_error err -> Error err
