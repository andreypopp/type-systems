open Import
open Syntax

exception Unification_error

let rec unify (a : ty) (b : ty) =
  if Debug.log_solve then
    Caml.Format.printf "UNIFY %s %s@." (Ty.show a) (Ty.show b);
  match (a, b) with
  | Ty_const a, Ty_const b -> if not String.(a = b) then raise Unification_error
  | Ty_app (af, aargs), Ty_app (bf, bargs) -> (
    unify af bf;
    match List.iter2 aargs bargs ~f:unify with
    | Unequal_lengths -> raise Unification_error
    | Ok () -> ())
  | Ty_nullable a, Ty_nullable b -> unify a b
  | Ty_arr (aargs, ab), Ty_arr (bargs, bb) ->
    (match List.iter2 aargs bargs ~f:unify with
    | Unequal_lengths -> raise Unification_error
    | Ok () -> ());
    unify ab bb
  | Ty_record a, Ty_record b -> unify_rows unify a b
  | Ty_row_empty, _
  | _, Ty_row_empty ->
    assert false
  | Ty_row_extend _, _
  | _, Ty_row_extend _ ->
    assert false
  | Ty_bot, Ty_bot -> ()
  | Ty_top, Ty_top -> ()
  | Ty_var v1, Ty_var v2 -> (
    match (Var.ty v1, Var.ty v2) with
    | None, None -> union_vars v1 v2
    | Some a, Some b -> unify a b
    | None, Some ty -> Var.set_ty v1 ty
    | Some ty, None -> Var.set_ty v2 ty)
  | Ty_var v, ty
  | ty, Ty_var v -> (
    match Var.ty v with
    | None -> Var.set_ty v ty
    | Some ty' -> unify ty ty')
  | _, _ -> raise Unification_error

and unify_rows unify_ty a b =
  if Debug.log_solve then
    Caml.Format.printf "UNIFY %s %s@." (Ty.show a) (Ty.show b);
  match (a, b) with
  | Ty_row_empty, Ty_row_empty -> ()
  | Ty_row_empty, Ty_row_extend _ -> raise Unification_error
  | Ty_row_extend ((name, ty), a), b ->
    let a_unbound =
      match a with
      | Ty_var v -> if Var.is_empty v then Some v else None
      | _ -> None
    in
    let rec rewrite = function
      | Ty_row_empty -> raise Unification_error
      | Ty_row_extend ((name', ty'), b) ->
        if String.(name = name') then (
          unify_ty ty ty';
          b)
        else Ty_row_extend ((name', ty'), rewrite b)
      | Ty_var v -> (
        match Var.ty v with
        | Some b -> rewrite b
        | None ->
          let b = Ty.var @@ Var.fresh ~lvl:(Var.lvl v) () in
          Var.set_ty v (Ty_row_extend ((name, ty), b));
          b)
      | _ -> assert false
    in
    let b = rewrite b in
    (match a_unbound with
    | Some v ->
      if not (Var.is_empty v) then Type_error.raise Error_recursive_record_type
    | _ -> ());
    unify_rows unify_ty a b
  | Ty_var av, Ty_var bv -> (
    match (Var.ty av, Var.ty bv) with
    | None, None -> union_vars av bv
    | Some a, Some b -> unify_rows unify_ty a b
    | None, Some ty -> Var.set_ty av ty
    | Some ty, None -> Var.set_ty bv ty)
  | Ty_var v, b -> (
    match Var.ty v with
    | None -> Var.set_ty v b
    | Some ty -> unify_rows unify_ty ty b)
  | a, Ty_var v -> (
    match Var.ty v with
    | None -> Var.set_ty v a
    | Some b -> unify_rows unify_ty a b)
  | _, _ -> assert false

and unifiable a b =
  try
    unify a b;
    true
  with
  | Unification_error -> false

and meet_rows meet_ty =
  let exception Meet_error in
  let rec aux a b =
    if Debug.log_solve then
      Caml.Format.printf "UNIFY %s %s@." (Ty.show a) (Ty.show b);
    match (a, b) with
    | Ty_row_empty, Ty_row_empty -> Ty_row_empty
    | Ty_row_empty, Ty_row_extend _ -> raise Meet_error
    | Ty_row_extend ((name, ty), a), b ->
      let a_unbound =
        match a with
        | Ty_var v -> if Var.is_empty v then Some v else None
        | _ -> None
      in
      let rec rewrite = function
        | Ty_row_empty -> raise Meet_error
        | Ty_row_extend ((name', ty'), b) ->
          if String.(name = name') then
            let ty = meet_ty ty ty' in
            (ty, b)
          else
            let ty, b = rewrite b in
            (ty, Ty_row_extend ((name', ty'), b))
        | Ty_var v -> (
          match Var.ty v with
          | Some b -> rewrite b
          | None ->
            let b = Ty.var @@ Var.fresh ~lvl:(Var.lvl v) () in
            Var.set_ty v (Ty_row_extend ((name, ty), b));
            (Ty_var v, b))
        | _ -> assert false
      in
      let ty, b = rewrite b in
      (match a_unbound with
      | Some v ->
        if not (Var.is_empty v) then
          Type_error.raise Error_recursive_record_type
      | _ -> ());
      Ty_row_extend ((name, ty), aux a b)
    | Ty_var v1, Ty_var v2 -> (
      match (Var.ty v1, Var.ty v2) with
      | None, None ->
        union_vars v1 v2;
        a
      | Some a, Some b -> aux a b
      | None, Some ty ->
        Var.set_ty v1 ty;
        ty
      | Some ty, None ->
        Var.set_ty v2 ty;
        ty)
    | Ty_var v, ty
    | ty, Ty_var v -> (
      match Var.ty v with
      | None ->
        Var.set_ty v ty;
        ty
      | Some ty' -> aux ty ty')
    | _, _ -> assert false
  in
  fun a b ->
    try Some (aux a b) with
    | Meet_error -> None

(** [greatest_lower_bound' a b] computes a Greatest-Lower-Bound of [a] and [b]. *)
and greatest_lower_bound =
  let rec aux a b =
    if Debug.log_solve then
      Caml.Format.printf "GLB %s %s@." (Ty.show a) (Ty.show b);
    if phys_equal a b then a
    else
      match (a, b) with
      | a, Ty_top
      | Ty_top, a ->
        a
      | _, Ty_bot
      | Ty_bot, _ ->
        Ty_bot
      | Ty_const aname, Ty_const bname ->
        if String.equal aname bname then a else Ty_bot
      | Ty_arr (aargs, aty), Ty_arr (bargs, bty) -> (
        match List.map2 aargs bargs ~f:least_upper_bound with
        | Unequal_lengths -> Ty_bot
        | Ok args -> Ty_arr (args, aux aty bty))
      | Ty_app (aty, aargs), Ty_app (bty, bargs) -> (
        match List.map2 aargs bargs ~f:aux with
        | Unequal_lengths -> Ty_bot
        | Ok args -> Ty_app (aux aty bty, args))
      | Ty_record a, Ty_record b -> (
        match meet_rows aux a b with
        | Some row -> Ty_record row
        | None -> Ty_bot)
      | Ty_row_empty, Ty_row_empty -> assert false
      | Ty_row_extend _, Ty_row_extend _ -> assert false
      | Ty_nullable a, b -> aux a b
      | a, Ty_nullable b -> aux a b
      | Ty_var v1, Ty_var v2 -> (
        match (Var.ty v1, Var.ty v2) with
        | None, None ->
          union_vars v1 v2;
          a
        | Some a, Some b -> aux a b
        | None, Some ty ->
          Var.set_ty v1 ty;
          ty
        | Some ty, None ->
          Var.set_ty v2 ty;
          ty)
      | Ty_var v, ty
      | ty, Ty_var v -> (
        match Var.ty v with
        | None ->
          Var.set_ty v ty;
          ty
        | Some ty' -> aux ty ty')
      | _, _ -> Ty_bot
  in
  aux

(** [least_upper_bound a b] computes a Least-Upper-Bound of [a] and [b]. *)
and least_upper_bound =
  let rec aux a b =
    if Debug.log_solve then
      Caml.Format.printf "LUB %s & %s@." (Ty.show a) (Ty.show b);
    if phys_equal a b then a
    else
      match (a, b) with
      | _, Ty_top
      | Ty_top, _ ->
        Ty_top
      | a, Ty_bot
      | Ty_bot, a ->
        a
      | Ty_const aname, Ty_const bname ->
        if String.equal aname bname then a else Ty_top
      | Ty_arr (aargs, aty), Ty_arr (bargs, bty) -> (
        match List.map2 aargs bargs ~f:greatest_lower_bound with
        | Unequal_lengths -> Ty_top
        | Ok args -> Ty_arr (args, aux aty bty))
      | Ty_app (aty, aargs), Ty_app (bty, bargs) -> (
        match List.map2 aargs bargs ~f:aux with
        | Unequal_lengths -> Ty_top
        | Ok args -> Ty_app (aux aty bty, args))
      | Ty_record a, Ty_record b -> (
        match meet_rows aux a b with
        | Some row -> Ty_record row
        | None -> Ty_top)
      | Ty_row_empty, Ty_row_empty -> assert false
      | Ty_row_extend _, Ty_row_extend _ -> assert false
      | Ty_nullable a, b -> Ty.nullable (aux a b)
      | a, Ty_nullable b -> Ty.nullable (aux a b)
      | Ty_var v1, Ty_var v2 -> (
        match (Var.ty v1, Var.ty v2) with
        | None, None ->
          union_vars v1 v2;
          a
        | Some a, Some b -> aux a b
        | None, Some ty ->
          Var.set_ty v1 ty;
          ty
        | Some ty, None ->
          Var.set_ty v2 ty;
          ty)
      | Ty_var v, ty
      | ty, Ty_var v -> (
        match Var.ty v with
        | None ->
          Var.set_ty v ty;
          ty
        | Some ty' -> aux ty ty')
      | _, _ -> Ty_top
  in
  aux

and union_vars a b =
  Var.union ~merge_lower:least_upper_bound ~merge_upper:greatest_lower_bound a b

let is_subtype ~sub_ty ~super_ty =
  let lub = least_upper_bound sub_ty super_ty in
  Ty.equal lub super_ty

module Constraint_set : sig
  type t
  (* A set of constraints (mutable). *)

  val empty : unit -> t
  (** Create new constraint set. *)

  val add : t -> var -> ty * ty -> unit
  (** [add cset v (lower, upper)] adds a new constraint for variable [v] with
      [lower] and [upper] bounds. *)

  val solve : t -> unit
  (** [solve cset] solves all constraints in [cset], raising [Type_error] if
      it's unable to solve it. *)
end = struct
  module Elem = struct
    type t = var

    let layout v =
      let open Layout in
      let v' = Union_find.value v in
      let* lower = layout_ty' v'.lower in
      let* v = Var.layout v in
      let* upper = layout_ty' v'.upper in
      return (lower ^^ string " <: " ^^ v ^^ string " <: " ^^ upper)

    include (
      Showable (struct
        type nonrec t = t

        let layout c = Layout.render (layout c)
      end) :
        SHOWABLE with type t := t)
  end

  type t = var list ref
  (** Set of constraints on type variables. For each type variable we have a
      lower and an upper bound. *)

  let layout set =
    let open Layout in
    let* items = list_map !set ~f:Elem.layout in
    let sep = string ", " in
    return (braces (separate sep items))

  include (
    Showable (struct
      type nonrec t = t

      let layout v = Layout.render (layout v)
    end) :
      SHOWABLE with type t := t)

  let empty () = ref []

  let add cs v (lower, upper) =
    if Debug.log_solve then
      Caml.Format.printf "ADD %s <: %s <: %s@." (Ty.show lower) (Var.show v)
        (Ty.show upper);
    cs := v :: !cs;
    let v' = Union_find.value v in
    v'.lower <- least_upper_bound v'.lower lower;
    v'.upper <- greatest_lower_bound v'.upper upper

  let ensure_is_subtype ~sub_ty ~super_ty =
    if not (is_subtype ~sub_ty ~super_ty) then
      Type_error.raise_not_a_subtype ~sub_ty ~super_ty ()

  let solve set =
    set := List.dedup_and_sort ~compare:Var.compare !set;
    if Debug.log_solve then Caml.Format.printf "SOLVE %s@." (show set);
    let solve v =
      if Debug.log_solve then Caml.Format.printf "LOOKING %s@." (Elem.show v);
      let v' = Union_find.value v in
      match (v'.variance, v'.lower, v'.ty, v'.upper) with
      | _, _, Some _, _ -> failwith "constraints against a resolved var"
      | (None | Some Covariant), lower, None, upper ->
        ensure_is_subtype ~sub_ty:lower ~super_ty:upper;
        Var.set_ty v lower
      | Some Contravariant, lower, None, Ty_top -> Var.set_ty v lower
      | Some Contravariant, lower, None, upper ->
        ensure_is_subtype ~sub_ty:lower ~super_ty:upper;
        Var.set_ty v upper
      | Some Invariant, Ty_bot, None, Ty_top -> assert false
      | Some Invariant, Ty_bot, None, upper ->
        (* TODO: not sure this case is ok *)
        Var.set_ty v upper
      | Some Invariant, lower, None, Ty_top ->
        (* TODO: not sure this case is ok *)
        Var.set_ty v lower
      | Some Invariant, lower, None, upper ->
        if not (unifiable lower upper) then
          Type_error.raise (Error_not_equal (lower, upper));
        Var.set_ty v lower
    in
    List.iter !set ~f:(fun v -> solve v)
end
