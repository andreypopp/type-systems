open! Base

type 'a loc = Root of 'a | Link of 'a t

and 'a t = 'a loc ref [@@deriving sexp_of]

let make value = ref (Root value)

let rec root p : _ t =
  match p.contents with
  | Root _ -> p
  | Link p' ->
    let p'' = root p' in
    (* Perform path compression. *)
    if not (phys_equal p' p'') then p.contents <- p'.contents;
    p''

let value p =
  match (root p).contents with
  | Root value -> value
  | Link _ -> assert false

let union ~f a b =
  if phys_equal a b then ()
  else
    let a = root a in
    let b = root b in
    if phys_equal a b then ()
    else
      match (a.contents, b.contents) with
      | Root avalue, Root bvalue ->
        a.contents <- Link b;
        b.contents <- Root (f avalue bvalue)
      | Root _, Link _
      | Link _, Root _
      | Link _, Link _ ->
        assert false

let link ~target p = union ~f:(fun _b target -> target) p target

let equal a b = phys_equal a b || phys_equal (root a) (root b)
