open! Import
open Syntax

type t = (Path.t, Path.t, Path.comparator_witness) Map.t

let empty = Map.empty (module Path)

let add s n p = Map.set s ~key:(Path.make n) ~data:p

let merge s1 s2 =
  Map.merge s1 s2 ~f:(fun ~key:_ -> function
    | `Both _ -> failwith "TODO: shouldn't happen once we use stamped names"
    | `Left p
    | `Right p ->
      Some p)

let prefix_image prefix s = Map.map s ~f:(Path.prefix prefix)

let prefix prefix s =
  let s =
    Map.to_sequence s
    |> Sequence.map ~f:(fun (k, v) ->
           (Path.prefix prefix k, Path.prefix prefix v))
    |> Map.of_sequence (module Path)
  in
  match s with
  | `Ok s -> s
  | `Duplicate_key _ -> assert false

let rec subst_path s p =
  match Map.find s p with
  | Some p -> p
  | None -> (
    match p with
    | Path.Path_ident _ -> p
    | Path_project (p, name) -> Path_project (subst_path s p, name))

let rec subst_ty s ty =
  match ty with
  | Ty_name p -> Ty_name (subst_path s p)
  | Ty_abstract p -> Ty_abstract (subst_path s p)
  | Ty_var v -> (
    match Var.ty v with
    | None -> ty
    | Some ty -> subst_ty s ty)
  | Ty_app (f, args) -> Ty_app (subst_ty s f, List.map args ~f:(subst_ty s))
  | Ty_arr (args, r) -> Ty_arr (List.map args ~f:(subst_ty s), subst_ty s r)

let subst_ty_sch s (vs, ty) = (vs, subst_ty s ty)

include (
  Showable (struct
    type nonrec t = t

    let layout s =
      let open PPrint in
      separate hardline
        (Map.to_alist s
        |> List.map ~f:(fun (p1, p2) ->
               Path.layout p1 ^^ string " -> " ^^ Path.layout p2))
  end) :
    SHOWABLE with type t := t)
