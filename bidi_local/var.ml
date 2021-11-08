open Import
open Syntax

type t = var

module Id = MakeId ()

let fresh ?name ?lvl () : var =
  let id = Id.fresh () in
  Union_find.make
    {
      id;
      name;
      lvl;
      variance = None;
      ty = None;
      lower = Ty_bot;
      upper = Ty_top;
    }

let refresh ?lvl var =
  let id = Id.fresh () in
  let var = Union_find.value var in
  Union_find.make
    {
      id;
      name = var.name;
      lvl;
      variance = None;
      ty = None;
      lower = Ty_bot;
      upper = Ty_top;
    }

let reset = Id.reset

let layout = layout_var'

include (
  Showable (struct
    type nonrec t = t

    let layout v = Layout.render (layout_var' v)
  end) :
    SHOWABLE with type t := t)

let sexp_of_t v = Sexp.Atom (show v)

let equal = Union_find.equal

let compare a b =
  let a' = Union_find.value a in
  let b' = Union_find.value b in
  Int.compare a'.id b'.id

let merge_lvl lvl1 lvl2 =
  match (lvl1, lvl2) with
  | None, None
  | Some _, None
  | None, Some _ ->
    failwith "lvl is not assigned"
  | Some lvl1, Some lvl2 -> Some (Int.min lvl1 lvl2)

let merge_variance variance1 variance2 =
  match (variance1, variance2) with
  | None, None -> None
  | Some v, None
  | None, Some v ->
    Some v
  | Some v1, Some v2 -> Some (Variance.join v1 v2)

let merge_name v1 v2 =
  match (v1.name, v2.name) with
  | None, None -> None
  | None, n -> n
  | n, None -> n
  | Some n1, Some n2 ->
    Some
      (if Option.value v1.lvl ~default:(-1) > Option.value v2.lvl ~default:(-1)
      then n2
      else n1)

let name v =
  match (Union_find.value v).name with
  | None -> failwith "name is not assigned"
  | Some name -> name

let lvl v =
  match (Union_find.value v).lvl with
  | None -> failwith "lvl is not assigned"
  | Some lvl -> lvl

let variance v =
  match (Union_find.value v).variance with
  | None -> failwith "variance is not assigned"
  | Some variance -> variance

let set_variance v variance =
  let v = Union_find.value v in
  match v.variance with
  | None -> v.variance <- Some variance
  | Some variance' -> v.variance <- Some (Variance.join variance' variance)

(** [occurs_check_adjust_lvl v ty] checks that variable [v] is not
    contained within type [ty] and adjust levels of all unbound vars within
    the [ty]. *)
let occurs_check_adjust_lvl v =
  let v = Union_find.value v in
  let rec occurs_check_ty ty' : unit =
    match ty' with
    | Ty_top
    | Ty_bot
    | Ty_const _ ->
      ()
    | Ty_arr (args, ret) ->
      List.iter args ~f:occurs_check_ty;
      occurs_check_ty ret
    | Ty_nullable ty -> occurs_check_ty ty
    | Ty_app (f, args) ->
      occurs_check_ty f;
      List.iter args ~f:occurs_check_ty
    | Ty_var other_var -> (
      let other_var = Union_find.value other_var in
      match other_var.ty with
      | Some ty' -> occurs_check_ty ty'
      | None ->
        if Int.equal other_var.id v.id then
          Type_error.raise Error_recursive_type
        else v.lvl <- merge_lvl v.lvl other_var.lvl)
  in
  occurs_check_ty

let ty v =
  match (Union_find.value v).ty with
  | Some (Ty_var _) -> assert false
  | Some ty -> Some ty
  | None -> None

let set_ty v ty =
  let v' = Union_find.value v in
  match (v'.ty, ty) with
  | Some _, _ -> failwith "ty is already assigned"
  | None, Ty_var _ -> failwith "unable to set ty to another var"
  | None, ty ->
    (* Caml.Format.printf "SET %s %s@." (show v) (Ty.show ty); *)
    occurs_check_adjust_lvl v ty;
    v'.ty <- Some ty

let is_empty v = Option.is_none (ty v)

let union ~merge_lower ~merge_upper v1 v2 =
  (* Caml.Format.printf "MERGE %s %s@." (show v1) (show v2); *)
  if equal v1 v2 then ()
  else
    match (ty v1, ty v2) with
    | None, None ->
      Union_find.union v1 v2 ~f:(fun v1 v2 ->
          v1.name <- merge_name v1 v2;
          v1.lvl <- merge_lvl v1.lvl v2.lvl;
          v1.variance <- merge_variance v1.variance v2.variance;
          v1.lower <- merge_lower v1.lower v2.lower;
          v1.upper <- merge_upper v1.upper v2.upper;
          v1)
    | _ -> failwith "cannot unify already resolved variables"
