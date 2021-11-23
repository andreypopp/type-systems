open! Base
open! Syntax

type t = {
  vars : (var * var) list;
  names : (name, var, String.comparator_witness) Map.t;
}

let empty = { vars = []; names = Map.empty (module String) }

let add_var subst var ty = { subst with vars = (var, ty) :: subst.vars }

let add_name subst name ty =
  { subst with names = Map.set subst.names ~key:name ~data:ty }

let find_var subst var = List.Assoc.find ~equal:Var.equal subst.vars var

let find_name subst name = Map.find subst.names name

let rec apply_ty ~variance subst ty =
  match ty with
  | Ty_bot
  | Ty_top ->
    ty
  | Ty_const name -> (
    match find_name subst name with
    | None -> ty
    | Some v ->
      Var.set_variance v variance;
      Ty_var v)
  | Ty_nullable ty -> Ty_nullable (apply_ty ~variance subst ty)
  | Ty_app (a, args) ->
    Ty_app
      (apply_ty ~variance subst a, List.map args ~f:(apply_ty ~variance subst))
  | Ty_arr (args, b) ->
    Ty_arr
      ( List.map args ~f:(apply_ty ~variance:(Variance.inv variance) subst),
        apply_ty ~variance subst b )
  | Ty_var v -> (
    match Var.ty v with
    | Some ty -> apply_ty ~variance subst ty
    | None -> (
      match find_var subst v with
      | Some v ->
        Var.set_variance v variance;
        Ty_var v
      | None -> ty))
  | Ty_record row -> Ty_record (apply_ty ~variance subst row)
  | Ty_row_empty -> ty
  | Ty_row_extend ((name, ty), row) ->
    Ty_row_extend
      ((name, apply_ty ~variance subst ty), apply_ty ~variance subst row)
