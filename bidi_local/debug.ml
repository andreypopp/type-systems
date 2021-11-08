(**
  
  Debug flags which influence the amount of logging information and pretty
  printing.

  Flags are controlled through DEBUG environment variables, use it like:

    $ DEBUG=sgi dune exec -- COMMAND

  The above invocation will toggle glags [s], [g] and [i] to be "on".

 *)

open! Base

let flags = Caml.Sys.getenv_opt "DEBUG" |> Option.value ~default:""

let log_solve = String.mem flags 's'

let log_generalize = String.mem flags 'g'

let log_instantiate = String.mem flags 'i'

let log_check = String.mem flags 'c'

let log_levels = String.mem flags 'l'
