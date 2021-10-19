open! Base
open Syntax

(** Constraints generation. *)
let rec generate : expr -> ty -> expr Constraint.t =
 fun e ty ->
  match e with
  | E_lit (Lit_int _) -> Constraint.(ty =~ Ty_const "int" >>| fun () -> e)
  | E_lit (Lit_string _) -> Constraint.(ty =~ Ty_const "string" >>| fun () -> e)
  | E_var name -> Constraint.inst name ty
  | E_app (f, args) ->
    let vs, arg_tys, args =
      List.fold args ~init:([], [], []) ~f:(fun (vs, arg_tys, args) arg ->
          let v = Var.fresh () in
          let arg_ty = Ty.var v in
          let arg = generate arg arg_ty in
          (v :: vs, arg_ty :: arg_tys, arg :: args))
    in
    let f_ty = Ty.(arr (List.rev arg_tys) ty) in
    let f = generate f f_ty in
    let args = Constraint.list (List.rev args) in
    Constraint.(exists vs (f &~ args) >>| fun (f, args) -> E_app (f, args))
  | E_abs (args, b) ->
    let vs, bindings, atys =
      List.fold args ~init:([], [], []) ~f:(fun (vs, bindings, atys) param ->
          let v = Var.fresh () in
          let ty = Ty.var v in
          ( v :: vs,
            (param, [], Constraint.return (E_var param), ty) :: bindings,
            Ty.var v :: atys ))
    in
    let v = Var.fresh () in
    let b = generate b (Ty.var v) in
    let ty' = Ty.arr (List.rev atys) (Ty.var v) in
    Constraint.(
      exists (v :: vs) (let_in (List.rev bindings) b &~ (ty' =~ ty))
      >>| fun ((_tys, b), ()) -> E_abs (args, b))
  | E_let ((name, e, _), b) -> (
    let v = Var.fresh () in
    let e_ty = Ty.var v in
    let e = generate e e_ty in
    let b = generate b ty in
    Constraint.(
      let_in [ (name, [ v ], e, e_ty) ] b >>| fun (tys, b) ->
      match tys with
      | [ (e, ty_sch) ] -> E_let ((name, e, Some ty_sch), b)
      | _ -> failwith "impossible as we are supplying a single binding"))
  | E_tclass_method _ ->
    (* This is a part of elaborated terms so we can't reach it here. Consider
       splitting source terms and elaborated terms. *)
    assert false

(* [unify ty1 ty2] unifies two types [ty1] and [ty2]. *)
let rec unify ty1 ty2 =
  if Debug.log_unify then
    Caml.Format.printf "UNIFY %s ~ %s@." (Ty.show ty1) (Ty.show ty2);
  if phys_equal ty1 ty2 then ()
  else
    match (ty1, ty2) with
    | Ty_const a, Ty_const b ->
      if not String.(a = b) then Type_error.raise (Error_unification (ty1, ty2))
    | Ty_app (a1, b1), Ty_app (a2, b2) -> (
      unify a1 a2;
      match List.iter2 b1 b2 ~f:unify with
      | Unequal_lengths -> Type_error.raise (Error_unification (ty1, ty2))
      | Ok () -> ())
    | Ty_arr (a1, b1), Ty_arr (a2, b2) -> (
      match List.iter2 a1 a2 ~f:unify with
      | Unequal_lengths -> Type_error.raise (Error_unification (ty1, ty2))
      | Ok () -> unify b1 b2)
    | Ty_var var1, Ty_var var2 -> (
      match Var.unify var1 var2 with
      | Some (ty1, ty2) -> unify ty1 ty2
      | None -> ())
    | Ty_var var, ty
    | ty, Ty_var var -> (
      match Var.ty var with
      | None ->
        Var.occurs_check_adjust_lvl var ty;
        Var.set_ty ty var
      | Some ty' -> unify ty' ty)
    | _, _ -> Type_error.raise (Error_unification (ty1, ty2))

(* [matches ty1 ty2] checks if [ty2] matches [ty1] shape. It does destructive
   substitution inside the [ty2] argument but keeps [ty1] intact and therefore
   [ty1] can be used in multiple [matches] calls. *)
let rec matches ty1 ty2 =
  if phys_equal ty1 ty2 then true
  else
    match (ty1, ty2) with
    | Ty_const a, Ty_const b -> String.(a = b)
    | Ty_app (a1, b1), Ty_app (a2, b2) -> (
      matches a1 a2
      &&
      match
        List.fold2 b1 b2 ~init:true ~f:(fun ok b1 b2 -> ok && matches b1 b2)
      with
      | Unequal_lengths -> false
      | Ok ok -> ok)
    | Ty_arr (a1, b1), Ty_arr (a2, b2) -> (
      match
        List.fold2 a1 a2 ~init:true ~f:(fun ok a1 a2 -> ok && matches a1 a2)
      with
      | Unequal_lengths -> false
      | Ok ok -> ok && matches b1 b2)
    | Ty_var var1, Ty_var var2 -> (
      if Var.equal var1 var2 then true
      else
        match (Var.ty var1, Var.ty var2) with
        | (Some _ | None), None ->
          if Var.bound_lvl var1 < Var.bound_lvl var2 then (
            if Debug.log_match then
              Caml.Format.printf "MATCH %s <-! %s@." (Var.show var1)
                (Var.show var2);
            Union_find.link ~target:var1 var2;
            true)
          else false
        | Some ty1, Some ty2 -> matches ty1 ty2
        | None, Some _ -> assert false)
    | Ty_var var1, ty2 -> (
      match Var.ty var1 with
      | Some ty1 -> matches ty1 ty2
      | None -> false)
    | ty1, Ty_var var2 -> (
      match Var.ty var2 with
      | None ->
        Var.set_ty ty1 var2;
        true
      | Some ty2 -> matches ty1 ty2)
    | _, _ -> false

let matches ty1 ty2 =
  if Debug.log_match then
    Caml.Format.printf "MATCH %s <-? %s@." (Ty.show ty1) (Ty.show ty2);
  matches ty1 ty2

let matches_bound b1 b2 = matches (Bound.to_ty b1) (Bound.to_ty b2)

(** A substitution over [ty] terms. *)
module Subst : sig
  type t

  val empty : t

  val make : (var * ty) list -> t

  val apply_cty : t -> cty -> cty

  val apply_ty : t -> ty -> ty

  val apply_bound : t -> bound -> bound
end = struct
  type t = (var * ty) list

  let empty = []

  let make pairs = pairs

  let find subst var =
    match List.Assoc.find ~equal:Var.equal subst var with
    | Some ty -> Some ty
    | None -> None

  let rec apply_cty subst (bs, ty) =
    (List.map bs ~f:(apply_bound subst), apply_ty subst ty)

  and apply_ty subst ty =
    match ty with
    | Ty_const _ -> ty
    | Ty_app (a, args) ->
      Ty_app (apply_ty subst a, List.map args ~f:(apply_ty subst))
    | Ty_arr (args, b) ->
      Ty_arr (List.map args ~f:(apply_ty subst), apply_ty subst b)
    | Ty_var v -> (
      match Var.ty v with
      | Some ty -> apply_ty subst ty
      | None -> (
        match find subst v with
        | Some ty -> ty
        | None -> ty))

  and apply_bound subst = function
    | B_class (name, tys) -> B_class (name, List.map tys ~f:(apply_ty subst))
end

(** Implicit params represent function parameters to be filled in by typeclass
    instances. *)
module Implicit_param : sig
  type t

  val make : lvl:lvl -> string -> t

  val link : target:t -> t -> unit

  val reset : unit -> unit

  val param : t -> name
end = struct
  type t = name Union_find.t

  module Id = MakeId ()

  let make ~lvl name =
    let name = Printf.sprintf "_%s_%i_%i" name lvl (Id.fresh ()) in
    Union_find.make name

  let link = Union_find.link

  let param = Union_find.value

  let reset = Id.reset
end

(** An applicative structure which is used to build a computation which
    elaborates terms. *)
module Elab : sig
  type 'a t

  val run : 'a t -> 'a
  (** Compute a value.

      This should be run at the very end, when all holes are elaborated. *)

  val return : 'a -> 'a t

  val map : 'a t -> ('a -> 'b) -> 'b t

  val both : 'a t -> 'b t -> ('a * 'b) t

  val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t

  val ( and+ ) : 'a t -> 'b t -> ('a * 'b) t

  val list : 'a t list -> 'a list t

  module Hole : sig
    type 'a hole = private
      | Hole_expr of { bounds : bound list; mutable elab : 'a t }
      | Hole_method of {
          bound : bound;
          name : string;
          mutable elab : 'a t option;
        }
      | Hole_implicit_param of 'a implicit_param_hole

    and 'a implicit_param_hole = private {
      bound : bound;
      param : Implicit_param.t;
      mutable elab : 'a t;
    }

    val implicit_param :
      lvl:lvl -> bound -> name -> expr t * expr implicit_param_hole

    val make_implicit_param : expr implicit_param_hole -> expr t * expr hole

    val make_expr : bound list -> expr -> expr t * expr hole

    val make_method : bound -> name -> expr t * expr hole

    val set_elab : 'a t -> 'a hole -> unit
  end
end = struct
  type 'a t = unit -> 'a

  let run elab = elab ()

  let return v () = v

  let map v f () = f (v ())

  let both a b () = (a (), b ())

  let ( let+ ) = map

  let ( and+ ) = both

  let list es () = List.map es ~f:run

  module Hole = struct
    type 'a hole =
      | Hole_expr of { bounds : bound list; mutable elab : 'a t }
      | Hole_method of {
          bound : bound;
          name : string;
          mutable elab : 'a t option;
        }
      | Hole_implicit_param of 'a implicit_param_hole

    and 'a implicit_param_hole = {
      bound : bound;
      param : Implicit_param.t;
      mutable elab : 'a t;
    }

    let of_hole hole () =
      match hole with
      | Hole_expr e -> e.elab ()
      | Hole_method { elab = Some expr; name; _ } ->
        E_tclass_method (expr (), name)
      | Hole_method { elab = None; _ } -> failwith "unresolved typeclass method"
      | Hole_implicit_param { elab; _ } -> elab ()

    let of_implicit_param param () = E_var (Implicit_param.param param)

    let implicit_param ~lvl bound name =
      let param = Implicit_param.make ~lvl name in
      let elab = of_implicit_param param in
      let hole = { elab; param; bound } in
      (of_hole (Hole_implicit_param hole), hole)

    let make_implicit_param param =
      let hole = Hole_implicit_param param in
      (of_hole hole, hole)

    let make_expr bounds expr =
      let hole = Hole_expr { bounds; elab = return expr } in
      (of_hole hole, hole)

    let make_method bound name =
      let hole = Hole_method { bound; name; elab = None } in
      (of_hole hole, hole)

    let set_elab elab hole =
      match hole with
      | Hole_expr hole -> hole.elab <- elab
      | Hole_method hole -> hole.elab <- Some elab
      | Hole_implicit_param hole -> hole.elab <- elab
  end
end

(** Instantiate type scheme into a constrained type. *)
let instantiate ?bound_lvl ~lvl (ty_sch : ty_sch) : cty =
  match ty_sch with
  | [], ty ->
    (* No ∀-quantified variables, return the type as-is *)
    ty
  | vars, cty ->
    let subst =
      Subst.make
        (List.map vars ~f:(fun v -> (v, Ty.var (Var.fresh ?bound_lvl ~lvl ()))))
    in
    Subst.apply_cty subst cty

let instantiate ?bound_lvl ~lvl ty_sch =
  if Debug.log_instantiate then Ty_sch.print ~label:"I<" ty_sch;
  let cty = instantiate ?bound_lvl ~lvl ty_sch in
  if Debug.log_instantiate then Cty.print ~label:"I>" cty;
  cty

module Env0 = struct
  type t = {
    values : (name, def_kind * def, String.comparator_witness) Map.t;
    tclasses : (name, tclass, String.comparator_witness) Map.t;
  }

  and def = { name : name; ty_sch : ty_sch }

  and def_kind = Def_value | Def_method

  and tclass = { def : def; method_def : def; instances : def list }

  let empty =
    { values = Map.empty (module String); tclasses = Map.empty (module String) }

  let find_val env name = Map.find env.values name

  let find_tclass env name = Map.find env.tclasses name

  let add_val ?(kind = Def_value) env name ty_sch =
    if Debug.log_define then
      Caml.Format.printf "val %s : %s@." name (Ty_sch.show ty_sch);
    let () =
      match (kind, ty_sch) with
      | Def_method, (_, ([ _ ], _)) -> ()
      | Def_method, (_, (_, _)) -> failwith "method with multiple constraints"
      | Def_value, _ -> ()
    in
    {
      env with
      values = Map.set env.values ~key:name ~data:(kind, { name; ty_sch });
    }
end

let rec ty_resolved = function
  | Ty_var v -> (
    match Var.ty v with
    | Some ty -> ty_resolved ty
    | None -> false)
  | Ty_const _ -> true
  | Ty_arr (args, ret) -> List.for_all args ~f:ty_resolved && ty_resolved ret
  | Ty_app (head, args) -> ty_resolved head && List.for_all args ~f:ty_resolved

let is_unresolved_v = function
  | Ty_var v -> Option.is_none (Var.ty v)
  | _ -> false

(** Elaborates on all the holes and returns a list of params and bounds in the
    Head First Normal (HNF) form.

    Bounds in HNF are considered solved bounds (there's nothing to solve further
    about them). *)
module Hole_elaborator : sig
  val elaborate :
    lvl:id ->
    env:Env0.t ->
    expr Elab.Hole.hole list ->
    expr Elab.Hole.implicit_param_hole list
end = struct
  (* Compute a list of super bounds for the bound. *)
  let lineage ~bound_lvl ~lvl ~env =
    let rec aux entailments (B_class (name, _) as bound) =
      match Env0.find_tclass env name with
      | None -> assert false
      | Some tclass -> (
        let c_ty = Bound.to_ty bound in
        let bounds, ty = instantiate ~bound_lvl ~lvl tclass.def.ty_sch in
        match bounds with
        | [] -> bound :: entailments
        | bounds ->
          (* This is not just an assert but also a way to associate [ty]
             variables with [c_ty], so [bounds] has all vars unified as well. *)
          assert (matches c_ty ty);
          List.fold bounds ~init:(bound :: entailments) ~f:aux)
    in
    aux []

  (* [entails others c] checks if the [c] bound can be "inferred" from [others]
     bounds. *)
  let entails ~bound_lvl ~lvl ~env others hole =
    let rec aux = function
      | [] -> None
      | hole' :: others' ->
        if
          List.exists (lineage ~bound_lvl ~lvl ~env hole'.Elab.Hole.bound)
            ~f:(fun bound' -> matches_bound hole.Elab.Hole.bound bound')
        then Some hole'
        else aux others'
    in
    aux others

  (* Simple bounds. *)
  let simpl_bounds ~bound_lvl ~lvl ~env =
    let rec aux simplified = function
      | [] -> simplified
      | hole :: holes -> (
        let others = simplified @ holes in
        match entails ~bound_lvl ~lvl ~env others hole with
        | Some hole' ->
          Implicit_param.link ~target:hole'.param hole.Elab.Hole.param;
          aux simplified holes
        | None -> aux (hole :: simplified) holes)
    in
    fun holes -> List.rev (aux [] holes)

  (* Check if bound is in HNF. *)
  let is_hnf (B_class (_name, tys)) =
    let resolved = List.for_all tys ~f:ty_resolved in
    (not resolved)
    && List.for_all tys ~f:(fun ty -> is_unresolved_v ty || ty_resolved ty)

  let find_tclass_instance ~bound_lvl ~lvl ~env bound : Env0.def * bound list =
    let (B_class (name, _)) = bound in
    let instances =
      match Env0.find_tclass env name with
      | None -> Type_error.raise (Error_unknown_tclass name)
      | Some tclass -> tclass.instances
    in
    let bound_ty = Bound.to_ty bound in
    match
      List.find_map instances ~f:(fun def ->
          let cty = instantiate ~bound_lvl ~lvl def.Env0.ty_sch in
          let bounds, ty = cty in
          let m = matches bound_ty ty in
          if m then Some (def, bounds) else None)
    with
    | None -> Type_error.raise (Error_no_tclass_instance bound_ty)
    | Some found -> found

  let holes_to_hnf ~bound_lvl ~lvl ~env (holes : expr Elab.Hole.hole list) =
    let rec solve_bound bound =
      if is_hnf bound then
        (* Bound is in HNF, so we allocate an implicit param for it. *)
        let (B_class (name, _)) = bound in
        let elab, hole = Elab.Hole.implicit_param ~lvl bound name in
        (elab, [ hole ])
      else
        (* Not in HNF, so we find an instance and recurse into its bounds. *)
        let def, bounds' = find_tclass_instance ~bound_lvl ~lvl ~env bound in
        let elab' = Elab.return (E_var def.name) in
        solve_bounds elab' bounds'
    and solve_bounds elab bounds =
      let es, solved =
        List.fold bounds ~init:([], []) ~f:(fun (es, solved) bound ->
            let e', solved' = solve_bound bound in
            (e' :: es, solved' @ solved))
      in
      let elab =
        Elab.(
          let+ es = list es
          and+ e = elab in
          match List.rev es with
          | [] -> e
          | es -> E_app (e, es))
      in
      (elab, solved)
    in
    List.concat
      (List.map holes ~f:(fun hole ->
           match hole with
           | Elab.Hole.Hole_implicit_param p ->
             if is_hnf p.bound then [ p ]
             else
               let elab, solved = solve_bound p.bound in
               Elab.Hole.set_elab elab hole;
               solved
           | Hole_expr p ->
             let elab, solved = solve_bounds p.elab p.bounds in
             Elab.Hole.set_elab elab hole;
             solved
           | Hole_method p ->
             let elab, solved = solve_bound p.bound in
             Elab.Hole.set_elab elab hole;
             solved))

  module Epoch = MakeId ()

  let elaborate ~lvl ~env (holes : expr Elab.Hole.hole list) =
    Implicit_param.reset ();
    let bound_lvl = Epoch.fresh () in
    let holes = holes_to_hnf ~bound_lvl ~lvl ~env holes in
    simpl_bounds ~bound_lvl ~lvl ~env holes
end

let simple_vs vs =
  let rec simple_vs vs' = function
    | [] -> vs'
    | v :: vs ->
      if Option.is_some (Var.ty v) then
        (* Skipping as the var is already bound. *)
        simple_vs vs' vs
      else if List.mem ~equal:Var.equal vs v then
        (* Skipping as the var is duplicated within [vs]. *)
        simple_vs vs' vs
      else simple_vs (v :: vs') vs
  in
  simple_vs [] vs

let bound_vs (B_class (_name, tys)) =
  List.filter_map tys ~f:(function
    | Ty_var v as ty -> if is_unresolved_v ty then Some v else None
    | _ -> None)

let ty_vs ~lvl ty =
  let rec aux vs = function
    | Ty_const _ -> vs
    | Ty_app (a, args) ->
      let vs = aux vs a in
      List.fold args ~init:vs ~f:aux
    | Ty_arr (args, b) ->
      let vs = aux vs b in
      List.fold args ~init:vs ~f:aux
    | Ty_var v -> (
      match Var.ty v with
      | Some ty -> aux vs ty
      | None -> if Var.lvl v > lvl then v :: vs else vs)
  in
  aux [] ty

let partition_bounds ~lvl =
  (* Given a set of "deferred" variables (variables we want to prevent to
     be generalized) we compute if we need to defer the current bound and a set
     of variables we want to "restrict" *)
  let should_defer dvs bound =
    let is_deferred_v v = Var.lvl v <= lvl || List.mem dvs v ~equal:Var.equal in
    let vs = bound_vs bound in
    let dvs', defer =
      List.fold vs ~init:([], false) ~f:(fun (dvs', defer) v ->
          if is_deferred_v v then (dvs', true) else (v :: dvs', defer))
    in
    if defer then
      (* if we are going to defer this bound, then all others not-yet deferred
         vars should be treated as deferred next. *)
      Some dvs'
    else None
  in
  let rec aux ~dvs ~next_dvs (rbs, dbs) holes =
    match holes with
    | [] -> (
      match next_dvs with
      | [] ->
        (* No deferred vars found, return what's found. *)
        ((rbs, dbs), dvs)
      | next_dvs ->
        (* Check retained bounds once more with new deferred vars. *)
        aux ~dvs:(simple_vs next_dvs) ~next_dvs:[] ([], dbs) rbs)
    | hole :: bounds -> (
      match should_defer dvs hole.Elab.Hole.bound with
      | None -> aux ~dvs ~next_dvs (hole :: rbs, dbs) bounds
      | Some next_dvs' ->
        (* Ok, we want to defer this bound, collect deferred vars. *)
        aux ~dvs ~next_dvs:(next_dvs' @ next_dvs) (rbs, hole :: dbs) bounds)
  in
  aux ~dvs:[] ~next_dvs:[] ([], [])

let generalize ~lvl (holes, ty) =
  let gvs = simple_vs (ty_vs ~lvl ty) in
  let (retained, holes), dvs = partition_bounds ~lvl holes in
  let gvs =
    List.filter gvs ~f:(fun v -> not (List.mem dvs v ~equal:Var.equal))
  in
  let holes =
    List.map holes ~f:(fun hole ->
        let _, hole = Elab.Hole.make_implicit_param hole in
        hole)
  in
  let params, bounds =
    let not_in_vs v = not (List.mem gvs v ~equal:Var.equal) in
    List.fold retained ~init:([], []) ~f:(fun (params, bounds) hole ->
        if List.exists (bound_vs hole.Elab.Hole.bound) ~f:not_in_vs then
          Type_error.raise
            (Error_ambigious_tclass_application hole.Elab.Hole.bound);
        (hole.param :: params, hole.bound :: bounds))
  in
  (List.rev params, (simple_vs gvs, (List.rev bounds, ty)), holes)

let generalize ~lvl (holes, ty) =
  (if Debug.log_generalize then
   let bounds = List.map holes ~f:(fun hole -> hole.Elab.Hole.bound) in
   Cty.print ~label:"G<" (bounds, ty));
  let params, ty_sch, holes = generalize ~lvl (holes, ty) in
  if Debug.log_generalize then Ty_sch.print ~label:"G>" ty_sch;
  (params, ty_sch, holes)

let rec solve :
    type a.
    lvl:lvl ->
    env:Env0.t ->
    a Constraint.t ->
    a Elab.t * expr Elab.Hole.hole list =
 fun ~lvl ~env c ->
  match c with
  | C_trivial -> (Elab.return (), [])
  | C_eq (a, b) ->
    unify a b;
    (Elab.return (), [])
  | C_map (c, f) ->
    let v, holes = solve ~lvl ~env c in
    (Elab.map v f, holes)
  | C_and (a, b) ->
    let a, aholes = solve ~lvl ~env a in
    let b, bholes = solve ~lvl ~env b in
    (Elab.both a b, aholes @ bholes)
  | C_and_list cs ->
    let vs, holes =
      List.fold cs ~init:([], []) ~f:(fun (vs, holes) c ->
          let v, holes' = solve ~lvl ~env c in
          (v :: vs, holes' @ holes))
    in
    let elab =
      Elab.(
        let+ vs = list vs in
        List.rev vs)
    in
    (elab, holes)
  | C_exists (vs, c) ->
    List.iter vs ~f:(Var.set_lvl lvl);
    solve ~lvl ~env c
  | C_let (bindings, c) ->
    let env, values, holes =
      let env0 = env in
      List.fold bindings ~init:(env, [], [])
        ~f:(fun (env, values, holes) (name, vs, c, ty) ->
          (* Need to set levels here as [C_let] works as [C_exists] as well. *)
          List.iter vs ~f:(Var.set_lvl (lvl + 1));
          let e, ty_sch, holes' =
            solve_and_generalize ~lvl:(lvl + 1) ~env:env0 c ty
          in
          let env = Env0.add_val env name ty_sch in
          (env, e :: values, holes' @ holes))
    in
    let v, holes' = solve ~lvl ~env c in
    let values = Elab.list (List.rev values) in
    (Elab.(both values v), holes' @ holes)
  | C_inst (name, ty) -> (
    let kind, ty_sch =
      match Env0.find_val env name with
      | Some (kind, def) -> (kind, def.ty_sch)
      | None -> Type_error.raise (Error_unknown_name name)
    in
    let bounds', ty' = instantiate ~lvl ty_sch in
    unify ty ty';
    match (kind, bounds') with
    | Def_value, [] -> (Elab.return (E_var name), [])
    | Def_value, bounds ->
      let elab, hole = Elab.Hole.make_expr bounds (E_var name) in
      (elab, [ hole ])
    | Def_method, [ c ] ->
      let elab, hole = Elab.Hole.make_method c name in
      (elab, [ hole ])
    | Def_method, _ -> assert false)

and solve_and_generalize ~lvl ~env c ty =
  let e, holes = solve ~lvl ~env c in
  let holes = Hole_elaborator.elaborate ~lvl:(lvl - 1) ~env holes in
  let params, ty_sch, holes = generalize ~lvl:(lvl - 1) (holes, ty) in
  let e =
    Elab.(
      let+ e = e in
      let e =
        match params with
        | [] -> e
        | params -> E_abs (List.map params ~f:Implicit_param.param, e)
      in
      (e, ty_sch))
  in
  (e, ty_sch, holes)

(** [infer ~env e] infers the type scheme for expression [e].

    It returns either an [Ok (ty_sch, elaborated)] where [ty_sch] is the type
    scheme inferred and [elaborated] is an elaborated expression corresponding
    to [e].

    ... or in case of an error it returns [Error err].
    *)
let infer ~env e : (expr, Type_error.t) Result.t =
  (* To infer an expression type we first generate constraints *)
  let v = Var.fresh () in
  let ty = Ty.var v in
  let c = generate e ty in
  let c = Constraint.exists [ v ] c in
  try
    (* and then solve them and generaralize!. *)
    let e, _ty_sch, holes = solve_and_generalize ~lvl:1 ~env c ty in
    if List.length holes > 0 then
      failwith "unelaborated expressions at the top level";
    Ok
      Elab.(
        run
          (let+ e, ty_sch = e in
           E_let (("_", e, Some ty_sch), E_var "_")))
  with
  | Type_error.Type_error error -> Error error

(** Now that we have all needed machinery we can extend [Env0] with methods for
    adding new definitions to the environment. *)
module Env = struct
  include Env0

  let add_tclass env name ty_sch =
    if Debug.log_define then
      Caml.Format.printf "typeclass %s = %s@." name (Ty_sch.show ty_sch);
    let def =
      let vs, (bounds, _) = ty_sch in
      let ty_sch =
        (vs, (bounds, Ty_app (Ty_const name, List.map vs ~f:Ty.var)))
      in
      { name; ty_sch }
    in
    let method_def = { name; ty_sch } in
    let env =
      let ty_sch =
        let vs, (_, ty) = ty_sch in
        let c = B_class (name, List.map vs ~f:Ty.var) in
        (vs, ([ c ], ty))
      in
      add_val ~kind:Def_method env name ty_sch
    in
    {
      env with
      tclasses =
        (match
           Map.add env.tclasses ~key:name
             ~data:{ def; method_def; instances = [] }
         with
        | `Ok tclass -> tclass
        | `Duplicate ->
          failwith (Printf.sprintf "typeclass %s is already defined" name));
    }

  let add_tclass_instance env name ty_sch =
    if Debug.log_define then
      Caml.Format.printf "instance %s : %s@." name (Ty_sch.show ty_sch);
    let vs, bounds, cls_name, cls_args =
      let vs, (bounds, ty) = ty_sch in
      match ty with
      | Ty_app (Ty_const name, args) -> (vs, bounds, name, args)
      | _ ->
        failwith
          (Printf.sprintf "typeclass instance should be a type applicaton")
    in
    let instance = { name; ty_sch } in
    let tclass =
      match Map.find env.tclasses cls_name with
      | Some tclass -> tclass
      | None -> failwith (Printf.sprintf "no typeclass found: %s" cls_name)
    in
    let tclass = { tclass with instances = instance :: tclass.instances } in
    let env =
      let vs', cty = tclass.method_def.ty_sch in
      let subst =
        match List.zip vs' cls_args with
        | Unequal_lengths ->
          failwith
            (Printf.sprintf "invalid number of arguments: %s for %s"
               (Ty_sch.show instance.ty_sch)
               (Ty_sch.show ty_sch))
        | Ok items -> Subst.make items
      in
      let bounds', ty' = Subst.apply_cty subst cty in
      let bounds =
        let _, hole =
          Elab.Hole.make_expr (bounds' @ bounds) (E_var instance.name)
        in
        Hole_elaborator.elaborate ~lvl:1 ~env [ hole ]
        |> List.map ~f:(fun hole -> hole.Elab.Hole.bound)
      in
      add_val env name (vs, (bounds, ty'))
    in
    { env with tclasses = Map.set env.tclasses ~key:cls_name ~data:tclass }
end
