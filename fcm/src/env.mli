type ('a, 'b) t

val make : unit -> ('a, 'b) t

val level : ('a, 'b) t -> int

val next_var : ('a, 'b) t -> (string * ('a, 'b) t)

val bind : Core.identifier -> 'a -> ('a, 'b) t -> ('a, 'b) t

val get : string -> ('a, 'b) t -> 'a option

val bind_type : Core.identifier -> 'b -> ('a, 'b) t -> ('a, 'b) t
val get_type : string -> ('a, 'b) t -> 'b option

val enter_level : ('a, 'b) t -> ('a, 'b) t
val leave_level : ('a, 'b) t -> ('a, 'b) t

val next_level : ('a, 'b) t -> (('a, 'b) t -> (('a, 'b) t * 'b)) -> (('a, 'b) t * 'b)
