open Base
open Expr

module Instance = struct
  type t = { instance : qual_pred; witness : String.t }
end

module Typeclass = struct
  type t = { typeclass : qual_pred; instances : Instance.t list }
end

module Env : sig
  type t

  (* Construction API. *)

  val empty : t

  val add : t -> String.t -> qual_ty -> t

  val add_typeclass : t -> qual_pred -> t

  val add_instance : t -> qual_pred -> String.t -> t

  (* Query API. *)

  val find : t -> String.t -> qual_ty option

  val dependencies : t -> String.t -> qual_pred list

  val instances : t -> String.t -> qual_pred list
end = struct
  type t = {
    env : (String.t, qual_ty, String.comparator_witness) Map.t;
    typeclasses : (String.t, Typeclass.t, String.comparator_witness) Map.t;
  }

  let empty =
    { env = Map.empty (module String); typeclasses = Map.empty (module String) }

  let add env name qty = { env with env = Map.set env.env ~key:name ~data:qty }

  let add_typeclass env (qp : Expr.qual_pred) =
    (* TODO: add checks *)
    let _, (name, _) = qp in
    {
      env with
      typeclasses =
        Map.set env.typeclasses ~key:name
          ~data:{ typeclass = qp; instances = [] };
    }

  let add_instance env qp witness =
    (* TODO: add checks *)
    let _, (name, _) = qp in
    let cls =
      match Map.find env.typeclasses name with
      | None -> failwith (Printf.sprintf "no such typeclass %s" name)
      | Some cls -> cls
    in
    let cls =
      { cls with instances = { instance = qp; witness } :: cls.instances }
    in
    { env with typeclasses = Map.set env.typeclasses ~key:name ~data:cls }

  let dependencies env id =
    let cls = Map.find_exn env.typeclasses id in
    List.map (fst cls.typeclass) ~f:(fun (name, _) ->
        let dep = Map.find_exn env.typeclasses name in
        dep.typeclass)

  let instances env id =
    let cls = Map.find_exn env.typeclasses id in
    List.map cls.instances ~f:(fun instance -> instance.instance)

  let find env = Map.find env.env
end

type error =
  | Error_unification of ty * ty
  | Error_recursive_types
  | Error_recursive_row_types
  | Error_not_a_function of ty
  | Error_unknown_name of string
  | Error_arity_mismatch of ty * int * int
  | Error_missing_typeclass_instance of pred
  | Error_ambigious_predicate of pred

exception Type_error of error

let type_error err = raise (Type_error err)

let doc_of_error =
  PPrint.(
    function
    | Error_recursive_types -> string "recursive types"
    | Error_recursive_row_types -> string "recursive row types"
    | Error_not_a_function ty ->
      string "expected a function but got:" ^^ nest 2 (break 1 ^^ doc_of_ty ty)
    | Error_unknown_name name -> string "unknown name: " ^^ string name
    | Error_arity_mismatch (ty, expected, got) ->
      string "arity mismatch: expected "
      ^^ string (Int.to_string expected)
      ^^ string " arguments but got "
      ^^ string (Int.to_string got)
      ^^ nest 2 (break 1 ^^ doc_of_ty ty)
    | Error_unification (ty1, ty2) ->
      string "unification error of"
      ^^ nest 2 (break 1 ^^ doc_of_ty ty1)
      ^^ (break 1 ^^ string "with")
      ^^ nest 2 (break 1 ^^ doc_of_ty ty2)
    | Error_missing_typeclass_instance p ->
      string "missing typeclass instance: " ^^ doc_of_pred p
    | Error_ambigious_predicate p ->
      string "ambigious predicate: " ^^ doc_of_pred p)

let pp_error = pp' doc_of_error

let show_error = show' doc_of_error

module Vars : sig
  val newvar : lvl -> unit -> ty

  val newrowvar : lvl -> unit -> ty_row

  val reset_vars : unit -> unit

  val newgenvar : unit -> ty
end = struct
  let currentid = ref 0

  let reset_vars () = currentid := 0

  let newid () =
    Int.incr currentid;
    !currentid

  let newvar lvl () =
    Ty_var { contents = Ty_var_unbound { id = newid (); lvl } }

  let newrowvar lvl () =
    Ty_row_var { contents = Ty_var_unbound { id = newid (); lvl } }

  let newgenvar () = Ty_var { contents = Ty_var_generic (newid ()) }
end

include Vars

(** Instantiation of type schemas into types.

    This is done by replacing all generic type variables with fresh unbound type
    variables.

 *)
module Instantiate : sig
  val instantiate_qual_ty : lvl -> qual_ty -> qual_ty

  val instantiate_qual_pred : lvl -> qual_pred -> qual_pred

  val instantiate_pred : lvl -> pred -> pred
end = struct
  type ctx = {
    lvl : Int.t;
    vars : (Int.t, ty) Hashtbl.t;
    rowvars : (Int.t, ty_row) Hashtbl.t;
  }

  let make_ctx lvl =
    {
      lvl;
      vars = Hashtbl.create (module Int);
      rowvars = Hashtbl.create (module Int);
    }

  let rec instantiate_ty' ctx (ty : ty) : ty =
    match ty with
    | Ty_const _ -> ty
    | Ty_arr (ty_args, ty_ret) ->
      Ty_arr
        (List.map ty_args ~f:(instantiate_ty' ctx), instantiate_ty' ctx ty_ret)
    | Ty_app (ty, ty_args) ->
      Ty_app (instantiate_ty' ctx ty, List.map ty_args ~f:(instantiate_ty' ctx))
    | Ty_var { contents = Ty_var_link ty } -> instantiate_ty' ctx ty
    | Ty_var { contents = Ty_var_unbound _ } -> ty
    | Ty_var { contents = Ty_var_generic id } ->
      Hashtbl.find_or_add ctx.vars id ~default:(newvar ctx.lvl)
    | Ty_record row -> Ty_record (instantiate_ty_row' ctx row)

  and instantiate_ty_row' ctx (ty_row : ty_row) =
    match ty_row with
    | Ty_row_field (name, ty, ty_row) ->
      Ty_row_field (name, instantiate_ty' ctx ty, instantiate_ty_row' ctx ty_row)
    | Ty_row_empty -> ty_row
    | Ty_row_var { contents = Ty_var_link ty_row } ->
      instantiate_ty_row' ctx ty_row
    | Ty_row_var { contents = Ty_var_unbound _ } -> ty_row
    | Ty_row_var { contents = Ty_var_generic id } ->
      Hashtbl.find_or_add ctx.rowvars id ~default:(newrowvar ctx.lvl)
    | Ty_row_const _ -> assert false

  and instantiate_pred' ctx (name, args) =
    (name, List.map args ~f:(instantiate_ty' ctx))

  and instantiate_qual_ty' ctx qty =
    let preds, ty = qty in
    (List.map preds ~f:(instantiate_pred' ctx), instantiate_ty' ctx ty)

  let instantiate_pred lvl p =
    let ctx = make_ctx lvl in
    instantiate_pred' ctx p

  let instantiate_qual_ty lvl qty =
    let ctx = make_ctx lvl in
    instantiate_qual_ty' ctx qty

  let instantiate_qual_pred lvl (ps, p) =
    let ctx = make_ctx lvl in
    (List.map ps ~f:(instantiate_pred' ctx), instantiate_pred' ctx p)
end

include Instantiate

module Pred_solver : sig
  val solve_preds :
    lvl ->
    Env.t ->
    (Ty_var_unbound.t, Ty_var_unbound.comparator_witness) Set.t ->
    pred list ->
    pred list * pred list
  (** Solve a set of predicates.

      This raises a [Type_error] in case it cannot find a suitable instance for
      a ground predicate or if a predicate is ambigious.

      The function returns a pair of predicate sets [deferred, retained] where
      [retained] should be generalized while [deferred] should be propagated
      upwards.
   *)
end = struct
  let match_ty ty1 ty2 =
    (* invariant: this destructs only ty1 *)
    (* TODO: handle closed record types. *)
    let rec aux ty1 ty2 : bool =
      if phys_equal ty1 ty2 then true
      else
        match (ty1, ty2) with
        | ty1, Ty_var { contents = Ty_var_link ty2 } -> aux ty1 ty2
        | Ty_app (f1, args1), Ty_app (f2, args2) ->
          aux f1 f2
          && List.length args1 = List.length args2
          && List.for_all2_exn args1 args2 ~f:(fun ty1 ty2 -> aux ty1 ty2)
        | Ty_var { contents = Ty_var_link ty1 }, ty2 -> aux ty1 ty2
        | Ty_var ({ contents = Ty_var_unbound _ } as var), ty2 ->
          var := Ty_var_link ty2;
          true
        | Ty_var { contents = Ty_var_generic _ }, _ ->
          failwith "uninstantiated type variable"
        | Ty_const name1, Ty_const name2 -> String.(name1 = name2)
        | _, _ -> false
    in
    aux ty1 ty2

  let match_pred (name1, args1) (name2, args2) =
    if not String.(name1 = name2) then false
    else
      let rec aux args1 args2 =
        match (args1, args2) with
        | [], [] -> true
        | [], _ -> false
        | _, [] -> false
        | a1 :: args1, a2 :: args2 -> match_ty a1 a2 && aux args1 args2
      in
      aux args1 args2

  let entailments_of_dependencies _lvl env pred =
    (* TODO: need to return a list of all things here *)
    let rec aux entailments pred =
      let dependencies = Env.dependencies env (fst pred) in
      List.fold dependencies ~init:(pred :: entailments)
        ~f:(fun entailments dep -> aux entailments (snd dep))
    in
    aux [] pred

  (* Try each instance of the class and on first match return the list of
     dependencies.

     We are looking for the first match becuase we are supposed to have
     non-overlapping instances in the environment (that's a TODO to enforce this
     invatiant on environment construction). *)
  let entailments_of_instances lvl env pred =
    let rec aux = function
      | [] -> None
      | q :: qs ->
        let deps', pred' = instantiate_qual_pred lvl q in
        if match_pred pred' pred then Some deps' else aux qs
    in
    aux (Env.instances env (fst pred))

  (* Entailment relation between predicates.

     [entail lvl env ps p] returns [true] in case predicates [ps] are enough to
     establish [p] predicate. *)
  let rec entail lvl env ps p =
    let rec inspect_dependencies = function
      | [] -> false
      | q :: qs ->
        let deps = entailments_of_dependencies lvl env q in
        List.exists deps ~f:(fun dep ->
            let dep = instantiate_pred lvl dep in
            match_pred dep p)
        || inspect_dependencies qs
    in
    inspect_dependencies ps
    ||
    match entailments_of_instances lvl env p with
    | None -> false
    | Some qs -> List.for_all qs ~f:(fun q -> entail lvl env ps q)

  (* Check that a predicate in a head normal form (HNF).

     A predicate is in HNF if all its arguments are type variables (this HNF
     definition is specific for languages with first order polymorphism only). *)
  let is_hnf (_name, args) =
    let rec aux = function
      | Ty_var { contents = Ty_var_link ty } -> aux ty
      | Ty_var { contents = Ty_var_generic _ } -> assert false
      | Ty_var { contents = Ty_var_unbound _ } -> true
      | Ty_app _ -> false
      | Ty_arr _ -> false
      | Ty_const _ -> false
      | Ty_record _ -> false
    in
    List.for_all args ~f:aux

  (* Try to convert a predicate into a HNF.

     Raises a type error if some instances are missing. *)
  let rec to_hnf lvl env p =
    if is_hnf p then [ p ]
    else
      match entailments_of_instances lvl env p with
      | None -> type_error (Error_missing_typeclass_instance p)
      | Some ps -> to_hnfs lvl env ps

  and to_hnfs lvl env ps = List.concat (List.map ps ~f:(to_hnf lvl env))

  (* Simplify a list of predicates.

     Simplification is performed by removing those predicates which can be
     inferred from other predicates in the same list (for which an entailment
     relation holds). *)
  let simplify lvl env ps =
    let rec aux simplified = function
      | [] -> simplified
      | p :: ps ->
        if entail lvl env (simplified @ ps) p then aux simplified ps
        else aux (p :: simplified) ps
    in
    aux [] ps

  (* Reduce a list of predicates. *)
  let reduce lvl env ps =
    let ps = to_hnfs lvl env ps in
    simplify lvl env ps

  let ty_vars ((_name, args) as p) =
    let rec inspect = function
      | Ty_var { contents = Ty_var_unbound tv } -> tv
      | Ty_var { contents = Ty_var_link ty } -> inspect ty
      | _ -> failwith (Printf.sprintf "predicate not in HNF: %s" (show_pred p))
    in
    List.map args ~f:inspect

  let solve_preds lvl env vars ps =
    let ps = reduce lvl env ps in
    let should_defer p =
      List.for_all (ty_vars p) ~f:(fun tv -> tv.lvl <= lvl)
    in
    let rec aux (deferred, retained) = function
      | [] -> (deferred, retained)
      | p :: ps ->
        if should_defer p then aux (p :: deferred, retained) ps
        else
          let not_in_vars tv = not (Set.mem vars tv) in
          if List.exists (ty_vars p) ~f:not_in_vars then
            type_error (Error_ambigious_predicate p);
          aux (deferred, p :: retained) ps
    in
    aux ([], []) ps
end

include Pred_solver

let generalize lvl env (qty : qual_ty) =
  let generalize_ty ty =
    (* Along with generalizing the type we also find all unbound type variables
       which we later use to check predicates for ambiguity. *)
    let seen = ref (Set.empty (module Ty_var_unbound)) in
    let mark id = Ref.replace seen (fun seen -> Set.add seen id) in
    let rec generalize_ty ty =
      match ty with
      | Ty_const _ -> ty
      | Ty_arr (ty_args, ty_ret) ->
        Ty_arr (List.map ty_args ~f:generalize_ty, generalize_ty ty_ret)
      | Ty_app (ty, ty_args) ->
        Ty_app (generalize_ty ty, List.map ty_args ~f:generalize_ty)
      | Ty_var { contents = Ty_var_link ty } -> generalize_ty ty
      | Ty_var { contents = Ty_var_generic _ } -> ty
      | Ty_var { contents = Ty_var_unbound tv } ->
        mark tv;
        if tv.lvl > lvl then Ty_var { contents = Ty_var_generic tv.id } else ty
      | Ty_record row -> Ty_record (generalize_ty_row row)
    and generalize_ty_row (ty_row : ty_row) =
      match ty_row with
      | Ty_row_field (name, ty, row) ->
        Ty_row_field (name, generalize_ty ty, generalize_ty_row row)
      | Ty_row_empty -> ty_row
      | Ty_row_var { contents = Ty_var_link ty_row } -> generalize_ty_row ty_row
      | Ty_row_var { contents = Ty_var_generic _ } -> ty_row
      | Ty_row_var { contents = Ty_var_unbound { id; lvl = var_lvl } } ->
        if var_lvl > lvl then Ty_row_var { contents = Ty_var_generic id }
        else ty_row
      | Ty_row_const _ -> assert false
    in
    let ty = generalize_ty ty in
    (ty, !seen)
  in
  let generalize_pred (name, args) =
    let args = List.map args ~f:(fun ty -> fst (generalize_ty ty)) in
    (name, args)
  in
  let ps, ty = qty in
  let ty, vars = generalize_ty ty in
  let deferred, retained = solve_preds lvl env vars ps in
  (deferred @ List.map retained ~f:generalize_pred, ty)

let occurs_check lvl id ty =
  let rec occurs_check_ty (ty : ty) : unit =
    match ty with
    | Ty_const _ -> ()
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
  and occurs_check_ty_row (ty_row : ty_row) : unit =
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
    | Ty_row_const _ -> assert false
  in
  occurs_check_ty ty

let rec unify (ty1 : ty) (ty2 : ty) =
  if phys_equal ty1 ty2 then ()
  else
    match (ty1, ty2) with
    | Ty_const name1, Ty_const name2 ->
      if not String.(name1 = name2) then
        type_error (Error_unification (ty1, ty2))
    | Ty_arr (args1, ret1), Ty_arr (args2, ret2) -> (
      match List.iter2 args1 args2 ~f:unify with
      | Unequal_lengths ->
        type_error
          (Error_arity_mismatch (ty1, List.length args2, List.length args1))
      | Ok () -> unify ret1 ret2)
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
        | Ty_row_empty -> raise Row_rewrite_error
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
        | Ty_row_const _ -> assert false
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
  | Ty_arr (ty_args, ty_ret) ->
    if List.length ty_args <> arity then
      type_error (Error_arity_mismatch (ty, List.length ty_args, arity));
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
    type_error (Error_not_a_function ty)

let rec infer' lvl (env : Env.t) (e : expr) =
  match e with
  | Expr_name name ->
    let qty =
      match Env.find env name with
      | Some ty -> ty
      | None -> type_error (Error_unknown_name name)
    in
    instantiate_qual_ty lvl qty
  | Expr_abs (args, body) ->
    let ty_args = List.map args ~f:(fun _ -> newvar lvl ()) in
    let cs, ty_body =
      let env =
        List.fold_left (List.zip_exn args ty_args) ~init:env
          ~f:(fun env (arg, ty_arg) -> Env.add env arg ([], ty_arg))
      in
      infer' lvl env body
    in
    (cs, Ty_arr (ty_args, ty_body))
  | Expr_app (func, args) ->
    let cs, ty_func = infer' lvl env func in
    let ty_args, ty_ret = unify_abs (List.length args) ty_func in
    let cs =
      List.fold2_exn args ty_args ~init:cs ~f:(fun cs arg ty_arg ->
          let cs', ty = infer' lvl env arg in
          unify ty ty_arg;
          cs @ cs')
    in
    (cs, ty_ret)
  | Expr_let (name, e, b) ->
    let ty_e = infer' (lvl + 1) env e in
    let ty_e = generalize lvl env ty_e in
    let env = Env.add env name ty_e in
    infer' lvl env b
  | Expr_let_rec (name, e, b) ->
    let ty_e =
      (* fix : a . (a -> a) -> a *)
      let ty_ret = newvar lvl () in
      let ty_fun = Ty_arr ([ ty_ret ], ty_ret) in
      let cs, ty_fun' = infer' (lvl + 1) env (Expr_abs ([ name ], e)) in
      unify ty_fun' ty_fun;
      (cs, ty_ret)
    in
    let ty_e = generalize lvl env ty_e in
    let env = Env.add env name ty_e in
    infer' lvl env b
  | Expr_record fields ->
    let cs, ty_row =
      List.fold_left fields ~init:([], Ty_row_empty)
        ~f:(fun (cs, row) (label, e) ->
          let cs', ty_e = infer' lvl env e in
          (cs @ cs', Ty_row_field (label, ty_e, row)))
    in
    (cs, Ty_record ty_row)
  | Expr_record_proj (e, label) ->
    let cs, ty_e = infer' lvl env e in
    let ty_proj = newvar lvl () in
    unify ty_e (Ty_record (Ty_row_field (label, ty_proj, newrowvar lvl ())));
    (cs, ty_proj)
  | Expr_record_extend (e, fields) ->
    let ty_row = newrowvar lvl () in
    let cs, return_ty_row =
      List.fold_left fields ~init:([], ty_row)
        ~f:(fun (cs, ty_row) (label, e) ->
          let ty_e = newvar lvl () in
          let cs', ty_e' = infer' lvl env e in
          unify ty_e ty_e';
          (cs @ cs', Ty_row_field (label, ty_e, ty_row)))
    in
    let cs', ty_e' = infer' lvl env e in
    unify (Ty_record ty_row) ty_e';
    (cs @ cs', Ty_record return_ty_row)
  | Expr_record_update (e, fields) ->
    let ty_row = newrowvar lvl () in
    let return_ty_row, to_unify =
      List.fold fields ~init:(ty_row, [])
        ~f:(fun (ty_row, to_unify) (label, e) ->
          let ty_e = newvar lvl () in
          (Ty_row_field (label, ty_e, ty_row), (e, ty_e) :: to_unify))
    in
    let cs, ty_e = infer' lvl env e in
    unify (Ty_record return_ty_row) ty_e;
    let cs =
      List.fold (List.rev to_unify) ~init:cs ~f:(fun cs (e, ty_e) ->
          let cs', ty_e' = infer' lvl env e in
          unify ty_e ty_e';
          cs @ cs')
    in
    (cs, Ty_record return_ty_row)
  | Expr_lit (Lit_string _) -> ([], Ty_const "string")
  | Expr_lit (Lit_int _) -> ([], Ty_const "int")

let infer env e =
  let qty = infer' 0 env e in
  generalize (-1) env qty
