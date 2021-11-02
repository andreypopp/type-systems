open! Import

type t = { name : string; stamp : int }

let current_stamp = ref 0

let make name =
  Int.incr current_stamp;
  { name; stamp = !current_stamp }

let compare n1 n2 = Int.compare n1.stamp n2.stamp

let equal n1 n2 = Int.equal n1.stamp n2.stamp

let name n = n.name

let sexp_of_t n = Sexp.Atom (n.name ^ "/" ^ Int.to_string n.stamp)

include Comparator.Make (struct
  type nonrec t = t

  let compare = compare

  let sexp_of_t = sexp_of_t
end)

include (
  Showable (struct
    type nonrec t = t

    let layout n =
      let open PPrint in
      string n.name
  end) :
    SHOWABLE with type t := t)

module type Int_like = sig
  type t

  val to_int : t -> int
end

let to_int (type a) (module M : Int_like with type t = a) (n : M.t) = M.to_int n
