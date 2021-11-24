open! Import
open! Syntax0

module Var_name : sig
  type t

  val make : string -> int -> t

  val to_string : t -> string

  (* val of_string : string -> t *)

  val succ : t -> t

  (* val next : t -> t *)

  include Comparator.S with type t := t
end = struct
  type t = string * int

  let make s n = (s, n)

  let to_string = function
    | s, 0 -> s
    | s, n -> Printf.sprintf "%s/%i" s n

  (* let of_string s = *)
  (*   if String.length s = 0 then raise (Invalid_argument s); *)
  (*   (s, 0) *)

  let succ (s, n) =
    if String.length s > 1 then (s ^ "'", n)
    else
      match String.get s 0 with
      | 'z' -> (s ^ "'", n)
      | c -> (String.of_char (Char.of_int_exn (Char.to_int c + 1)), n)

  (* let next (c, n) = (c, n + 1) *)

  include Comparator.Make (struct
    type nonrec t = t

    let compare (ac, an) (bc, bn) =
      match String.compare ac bc with
      | 0 -> Int.compare an bn
      | n -> n

    let sexp_of_t a = Sexp.Atom (to_string a)
  end)
end

module Names : sig
  type t

  val empty : t

  val alloc_var : var -> t -> t * string

  val lookup_var : var -> t -> string option
end = struct
  type t = {
    by_id : (int, string, Int.comparator_witness) Map.t;
    by_name : (string, int, String.comparator_witness) Map.t;
  }

  let empty =
    { by_id = Map.empty (module Int); by_name = Map.empty (module String) }

  let lookup_var var names =
    let var = Union_find.value var in
    Map.find names.by_id var.id

  let alloc_var var names =
    let var = Union_find.value var in
    match Map.find names.by_id var.id with
    | Some name -> (names, name)
    | None ->
      let names, name =
        match var.name with
        | Some name ->
          let name', n =
            match Map.find names.by_name name with
            | None -> (name, 1)
            | Some n -> (Printf.sprintf "%s/%i" name n, n + 1)
          in
          let by_name = Map.set names.by_name ~key:name ~data:n in
          ({ names with by_name }, name')
        | None ->
          let name =
            Var_name.succ
              (match Map.max_elt names.by_name with
              | None -> Var_name.make "a" 0
              | Some (s, n) -> Var_name.make s n)
          in
          (names, Var_name.to_string name)
      in
      let by_id = Map.set names.by_id ~key:var.id ~data:name in
      ({ names with by_id }, name)
end

include PPrint

type 'a t = Names.t -> Names.t * 'a

let render layout =
  let _, v = layout Names.empty in
  v

type layout = document t

let alloc_var = Names.alloc_var

let lookup_var var : string option t =
 fun names -> (names, Names.lookup_var var names)

type names = Names.t

let names names = (names, names)

let closed ?names v cnames =
  let names =
    match names with
    | None -> cnames
    | Some names -> names
  in
  let _names, v = v names in
  (names, v)

type color = Black | Red | Green | Yellow | Blue | Magenta | Cyan | White

let int_of_color col =
  match col with
  | Black -> 0
  | Red -> 1
  | Green -> 2
  | Yellow -> 3
  | Blue -> 4
  | Magenta -> 5
  | Cyan -> 6
  | White -> 7

let enable_colors_flag = ref false

let enable_colors enable = enable_colors_flag := enable

let bold doc =
  if not !enable_colors_flag then doc
  else fancystring "\x1B[1m" 0 ^^ doc ^^ fancystring "\x1B[0m" 0

let fg color doc =
  if not !enable_colors_flag then doc
  else
    let opening = Printf.sprintf "\x1B[3%dm" (int_of_color color) in
    fancystring opening 0 ^^ doc ^^ fancystring "\x1B[0m" 0

include Monad.Make (struct
  type nonrec 'a t = 'a t

  let return v names = (names, v)

  let bind v ~f names =
    let names, v = v names in
    let names, v = f v names in
    (names, v)

  let map v ~f names =
    let names, v = v names in
    (names, f v)

  let map = `Custom map
end)

include Monad_syntax

let list_map xs ~f =
  let rec aux = function
    | [] -> return []
    | x :: xs ->
      let* x = f x in
      let* xs = aux xs in
      return (x :: xs)
  in
  aux xs
