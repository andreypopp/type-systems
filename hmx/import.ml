include Base

module type SHOWABLE = sig
  type t

  val layout : t -> PPrint.document

  val show : t -> string

  val print : ?label:string -> t -> unit
end

module Showable (S : sig
  type t

  val layout : t -> PPrint.document
end) : SHOWABLE with type t = S.t = struct
  type t = S.t

  let layout = S.layout

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
