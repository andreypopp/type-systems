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

let subsumes ~lvl constraints ~sub:(sub_loc, sub_ty) ~super:(super_loc, super_ty)
    =
  let exception Subsumption_failed of { sub_ty : ty; super_ty : ty } in
  let rec aux ~sub_ty ~super_ty =
    if Debug.log_solve then
      Caml.Format.printf "??? %s <: %s@." (Ty.show sub_ty) (Ty.show super_ty);
    if phys_equal super_ty sub_ty || Ty.equal super_ty sub_ty then ()
    else
      match (sub_ty, super_ty) with
      | Ty_const name, Ty_const name' ->
        if not (String.equal name name') then
          raise (Subsumption_failed { sub_ty; super_ty })
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
        | Unequal_lengths -> raise (Subsumption_failed { sub_ty; super_ty })
        | Ok () -> ())
      | Ty_arr (sub_args, sub_ty'), Ty_arr (super_args, super_ty') ->
        (match
           List.iter2 super_args sub_args ~f:(fun super_ty' sub_ty' ->
               aux ~sub_ty:super_ty' ~super_ty:sub_ty')
         with
        | Unequal_lengths -> raise (Subsumption_failed { sub_ty; super_ty })
        | Ok () -> ());
        aux ~sub_ty:sub_ty' ~super_ty:super_ty'
      | Ty_record sub_row, Ty_record super_row -> (
        try
          Subtyping.unify_rows
            (fun sub_ty super_ty -> aux ~sub_ty ~super_ty)
            sub_row super_row
        with
        | Subtyping.Unification_error ->
          raise (Subsumption_failed { sub_ty; super_ty }))
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
      | Ty_row_empty, _
      | _, Ty_row_empty ->
        assert false
      | Ty_row_extend _, _
      | _, Ty_row_extend _ ->
        assert false
      | _ -> raise (Subsumption_failed { sub_ty; super_ty })
  in
  try aux ~sub_ty ~super_ty with
  | Subsumption_failed _ ->
    Type_error.raise_not_a_subtype ~sub_loc ~sub_ty ~super_loc ~super_ty ()

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
  | loc, E_var name ->
    let ty =
      match Env.find_val ctx.env name with
      | None -> Type_error.raise (Error_unknown_name { name = (loc, name) })
      | Some (val_kind, ty_sch) ->
        instantiate ~val_kind ~lvl:ctx.lvl ~variance:ctx.variance ty_sch
    in
    (ty, expr)
  | _, E_ann (expr, ty_sch) ->
    let ty =
      instantiate ~env:ctx.env ~lvl:ctx.lvl ~variance:ctx.variance ty_sch
    in
    (* TODO: here we drop E_ann, is this ok? *)
    (ty, check ~ctx expr ty)
  | loc, E_abs (vs, args, body) ->
    let env, vs =
      List.fold vs ~init:(ctx.env, []) ~f:(fun (env, vs) v ->
          let v = Var.refresh ~lvl:ctx.lvl v in
          (Env.add_var env (Var.name v) v, v :: vs))
    in
    let env, args, args_ty =
      List.fold args ~init:(env, [], [])
        ~f:(fun (env, args, args_ty) ((loc, name), ty) ->
          match ty with
          | None ->
            Type_error.raise
              (Error_missing_type_annotation { expr = (loc, E_var name) })
          | Some ty ->
            let ty =
              instantiate ~env ~lvl:ctx.lvl
                ~variance:(Variance.inv ctx.variance)
                ([], ty)
            in
            ( Env.add_val env name ([], ty),
              ((loc, name), Some ty) :: args,
              ty :: args_ty ))
    in
    let body_ty, body = synth ~ctx:{ ctx with env } body in
    let vs =
      (* Only keep variables which were not solved during checking args and
         body. *)
      List.filter vs ~f:Var.is_empty
    in
    ( Ty_arr (List.rev args_ty, body_ty),
      (loc, E_abs (List.rev vs, List.rev args, body)) )
  | loc, E_app (f, args) ->
    (* S-App-InfAlg *)
    let (args_tys, body_ty), f =
      match synth ~ctx f with
      | Ty_arr (args_tys, body_ty), f -> ((args_tys, body_ty), f)
      | Ty_var v, f ->
        assert (Var.is_empty v);
        (fresh_fun_ty v ~arity:(List.length args), f)
      | ty, _ ->
        Type_error.raise (Error_expected_a_function { loc = Expr.loc f; ty })
    in
    let constraints = Subtyping.Constraint_set.empty () in
    let args =
      match
        List.map2 args_tys args ~f:(fun ty arg ->
            check'
              ~ctx:{ ctx with variance = Variance.inv ctx.variance }
              ~constraints arg ty)
      with
      | Unequal_lengths -> Type_error.raise (Error_arity_mismatch { loc })
      | Ok args -> args
    in
    Subtyping.Constraint_set.solve constraints;
    let expr = E_app (f, args) in
    if Debug.log_solve then
      Caml.Format.printf "== SOLVED %s@."
        (Expr.show (loc, E_ann ((loc, expr), ([], body_ty))));
    (body_ty, (loc, E_app (f, args)))
  | loc, E_record fields ->
    let row, fields =
      (* List.fold fields ~init:(Ty_row_empty, []) *)
      List.fold_right fields ~init:(Ty_row_empty, [])
        ~f:(fun (name, expr) (row, fields) ->
          let ty, expr = synth ~ctx expr in
          (Ty_row_extend ((name, ty), row), (name, expr) :: fields))
    in
    (Ty_record row, (loc, E_record fields))
  | loc, E_record_project (expr, name) ->
    let row = Ty.var @@ Var.fresh ~lvl:ctx.lvl () in
    let ty = Ty.var @@ Var.fresh ~lvl:ctx.lvl () in
    let record_ty = Ty_record (Ty_row_extend ((name, ty), row)) in
    let constraints = Subtyping.Constraint_set.empty () in
    let expr = check' ~ctx ~constraints expr record_ty in
    Subtyping.Constraint_set.solve constraints;
    (ty, (loc, E_record_project (expr, name)))
  | loc, E_record_extend (expr, fields) ->
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
    (ty, (loc, E_record_extend (expr, List.rev fields)))
  | loc, E_record_update (expr, fields) ->
    let constraints = Subtyping.Constraint_set.empty () in
    let row, fields =
      let row = Ty.var @@ Var.fresh ~lvl:ctx.lvl () in
      List.fold fields ~init:(row, []) ~f:(fun (row, fields) (name, expr) ->
          let ty, expr = synth ~ctx expr in
          (Ty_row_extend ((name, ty), row), (name, expr) :: fields))
    in
    let ty = Ty_record row in
    let ty', expr = synth ~ctx expr in
    subsumes ~lvl:ctx.lvl constraints ~sub:(loc, ty) ~super:(Expr.loc expr, ty');
    Subtyping.Constraint_set.solve constraints;
    (ty, (loc, E_record_update (expr, List.rev fields)))
  | _, E_lit (Lit_string _) -> (Ty_const "string", expr)
  | _, E_lit (Lit_int _) -> (Ty_const "int", expr)
  | loc, E_let ((name, expr, e_ty_sch), body) ->
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
    (body_ty, (loc, E_let ((name, expr, Some e_ty_sch), body)))

and check' ~ctx ~constraints expr ty =
  if Debug.log_check then
    Caml.Format.printf "CHECK%s %s : %s@."
      (Variance.show ctx.variance)
      (Expr.show expr) (Ty.show ty);
  match expr with
  | loc, E_abs (vs, args, body) ->
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
      | ty -> Type_error.raise (Error_expected_a_function { loc; ty })
    in
    let env, args =
      match
        List.fold2 args args_ty ~init:(env, [])
          ~f:(fun (env, args) ((loc, name), ty') ty ->
            Option.iter ty' ~f:(fun ty' ->
                subsumes ~lvl:ctx.lvl constraints ~sub:(Location.none, ty)
                  ~super:(loc, ty'));
            let env = Env.add_val env name ([], ty) in
            (env, ((loc, name), Some ty) :: args))
      with
      | Unequal_lengths -> Type_error.raise (Error_arity_mismatch { loc })
      | Ok (env, args) -> (env, List.rev args)
    in
    let body = check' ~ctx:{ ctx with env } ~constraints body body_ty in
    (loc, E_abs (List.rev vs, args, body))
  | loc, E_app (f, args) ->
    let f_ty, f = synth ~ctx f in
    let args = args |> List.map ~f:(synth ~ctx) in
    let args_tys', ty' =
      match resolve_ty f_ty with
      | Ty_arr (args_tys', ty') -> (args_tys', ty')
      | Ty_var v ->
        assert (Var.is_empty v);
        fresh_fun_ty v ~arity:(List.length args)
      | ty ->
        Type_error.raise (Error_expected_a_function { loc = Expr.loc f; ty })
    in
    let () =
      match
        List.iter2 args_tys' args ~f:(fun ty' (ty, expr) ->
            subsumes ~lvl:ctx.lvl constraints
              ~sub:(Expr.loc expr, ty)
              ~super:(Location.none, ty'))
      with
      | Unequal_lengths -> Type_error.raise (Error_arity_mismatch { loc })
      | Ok () -> ()
    in
    subsumes ~lvl:ctx.lvl constraints ~sub:(loc, ty') ~super:(Location.none, ty);
    (loc, E_app (f, List.map args ~f:snd))
  | expr ->
    let ty', expr = synth ~ctx expr in
    subsumes ~lvl:ctx.lvl constraints
      ~sub:(Expr.loc expr, ty')
      ~super:(Location.none, ty);
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
       | _, E_let ((name, _, _), (_, E_var name')) when String.equal name name'
         ->
         expr
       | loc, expr -> (loc, E_ann ((loc, expr), ty)))
  with
  | Type_error.Type_error err -> Error err
