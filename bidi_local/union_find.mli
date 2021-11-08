(** Union find. *)

open! Base

type 'a t
(** Represents a single element.

    Each element belongs to an equivalence class and each equivalence class has
    a value of type ['a] assocated with it. *)

val make : 'a -> 'a t
(** [make v] creates a new equivalence class consisting of a single element
    which is returned to the caller.
    
    The value [v] is assocated with the equivalence class being created. *)

val value : 'a t -> 'a
(** [value e] returns the value associated with equivalence class the element
    [e] belongs to. *)

val union : f:('a -> 'a -> 'a) -> 'a t -> 'a t -> unit
(** [union ~f a b] makes elements [a] and [b] belong to the same equivalence
    class so that [equal a b] returns [true] afterwards.

    The resulted value associated with the equivalence class is being merged as
    specified by the [f] function. *)

val link : target:'a t -> 'a t -> unit
(** [link a b] is the same as [union a b] but guarantees to link [b] to [a] and
    not vice versa. *)

val equal : 'a t -> 'a t -> bool
(** [equal a b] checks that both elements [a] and [b] belong to the same
    equivalence class. *)

val sexp_of_t : ('a -> Sexp.t) -> 'a t -> Sexp.t
