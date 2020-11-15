type 'a t

type namespace =
  | Local of string
  (* For dotted reference, e.g. Module.label  *)
  | Scoped of string * namespace

val make : unit -> 'a t

val level : 'a t -> int

val next_var : 'a t -> (string * 'a t)

val bind : namespace -> 'a -> 'a t -> 'a t

val local : string -> 'a t -> 'a option

val bind_type : namespace -> 'a -> 'a t -> 'a t
val local_type : string -> 'a t -> 'a option

val enter_level : 'a t -> 'a t
val leave_level : 'a t -> 'a t

val next_level : 'a t -> ('a t -> ('a t * 'b)) -> ('a t * 'b)
