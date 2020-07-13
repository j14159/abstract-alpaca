type 'a t

type namespace =
  | Local of string
  (* For dotted reference, e.g. Module.label  *)
  | Scoped of string * string

val make : unit -> 'a t

val next_var : 'a t -> (string * 'a t)

val bind : string -> 'a -> 'a t -> 'a t
