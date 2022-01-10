include Base

module Monad = struct
  include Base.Monad

  (** A signature for modules implementing monadic let-syntax. *)
  module type MONAD_SYNTAX = sig
    type 'a t

    val return : 'a -> 'a t

    val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t

    val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t
  end

  (** Make a monadic syntax out of the monad. *)
  module Make_monad_syntax (P : Base.Monad.S) :
    MONAD_SYNTAX with type 'a t := 'a P.t = struct
    let return = P.return

    let ( let* ) v f = P.bind v ~f

    let ( let+ ) v f = P.map v ~f
  end

  module type S = sig
    include Base.Monad.S

    module Monad_syntax : MONAD_SYNTAX with type 'a t := 'a t
  end

  module Make (P : Basic) : S with type 'a t := 'a P.t = struct
    module Self = Base.Monad.Make (P)
    include Self

    module Monad_syntax = Make_monad_syntax (struct
      type 'a t = 'a P.t

      include Self
    end)
  end
end

module MakeId () = struct
  let c = ref 0

  let fresh () =
    Int.incr c;
    !c

  let reset () = c := 0
end

module type SHOWABLE = sig
  type t

  val show : t -> string

  val print : ?label:string -> t -> unit
end

module Showable (S : sig
  type t

  val layout : t -> PPrint.document
end) : SHOWABLE with type t = S.t = struct
  type t = S.t

  let show v =
    let width = 60 in
    let buf = Buffer.create 100 in
    PPrint.ToBuffer.pretty 1. width buf (S.layout v);
    Buffer.contents buf

  let print ?label v =
    match label with
    | Some label -> Caml.print_endline (label ^ ": " ^ show v)
    | None -> Caml.print_endline (show v)
end

module type DUMPABLE = sig
  type t

  val dump : ?label:string -> t -> unit

  val sdump : ?label:string -> t -> string
end

module Dumpable (S : sig
  type t

  val sexp_of_t : t -> Sexp.t
end) : DUMPABLE with type t = S.t = struct
  type t = S.t

  let dump ?label v =
    let s = S.sexp_of_t v in
    match label with
    | None -> Caml.Format.printf "%a@." Sexp.pp_hum s
    | Some label -> Caml.Format.printf "%s %a@." label Sexp.pp_hum s

  let sdump ?label v =
    let s = S.sexp_of_t v in
    match label with
    | None -> Caml.Format.asprintf "%a@." Sexp.pp_hum s
    | Some label -> Caml.Format.asprintf "%s %a@." label Sexp.pp_hum s
end
