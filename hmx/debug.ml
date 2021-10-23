open! Base

let flags = Caml.Sys.getenv_opt "HMX_DEBUG" |> Option.value ~default:""

let log_levels = String.mem flags 'l'

let log_instantiate = String.mem flags 'i'

let log_generalize = String.mem flags 'g'

let log_unify = String.mem flags 'u'

let log_define = String.mem flags 'd'
