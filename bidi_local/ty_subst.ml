open! Base
open! Syntax

type t = {
  vars : (var * ty) list;
  names : (name, ty, String.comparator_witness) Map.t;
}

let empty = { vars = []; names = Map.empty (module String) }

let add_var subst var ty = { subst with vars = (var, ty) :: subst.vars }

let add_name subst name ty =
  { subst with names = Map.set subst.names ~key:name ~data:ty }

let find_var subst var = List.Assoc.find ~equal:Var.equal subst.vars var

let find_name subst name = Map.find subst.names name

let rec apply_ty subst ty =
  match ty with
  | Ty_bot
  | Ty_top ->
    ty
  | Ty_const name -> (
    match find_name subst name with
    | None -> ty
    | Some ty -> ty)
  | Ty_nullable ty -> Ty_nullable (apply_ty subst ty)
  | Ty_app (a, args) ->
    Ty_app (apply_ty subst a, List.map args ~f:(apply_ty subst))
  | Ty_arr (args, b) ->
    Ty_arr (List.map args ~f:(apply_ty subst), apply_ty subst b)
  | Ty_var v -> (
    match Var.ty v with
    | Some ty -> apply_ty subst ty
    | None -> (
      match find_var subst v with
      | Some ty -> ty
      | None -> ty))
