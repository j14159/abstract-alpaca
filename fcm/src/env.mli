type ('a, 'b) t

type namespace =
  | Local of string
  (* For dotted reference, e.g. Module.label  *)
  | Scoped of string * namespace

val make : unit -> ('a, 'b) t

val level : ('a, 'b) t -> int

val next_var : ('a, 'b) t -> (string * ('a, 'b) t)

val bind : namespace -> 'a -> ('a, 'b) t -> ('a, 'b) t

val local : string -> ('a, 'b) t -> 'a option

val bind_type : namespace -> 'b -> ('a, 'b) t -> ('a, 'b) t
val local_type : string -> ('a, 'b) t -> 'b option

val enter_level : ('a, 'b) t -> ('a, 'b) t
val leave_level : ('a, 'b) t -> ('a, 'b) t

val next_level : ('a, 'b) t -> (('a, 'b) t -> (('a, 'b) t * 'b)) -> (('a, 'b) t * 'b)
