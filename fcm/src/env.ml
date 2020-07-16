type namespace =
  | Local of string
  (* For dotted reference, e.g. Module.label  *)
  | Scoped of string * string

type 'a t = { next_var : int
            ; bindings : (namespace * 'a) list
            }

let var_prefix = "v_"

let make _ =
  { next_var = 0
  ; bindings = []
  }

let next_var ({ next_var; _ } as e) =
  let rv = var_prefix ^ (string_of_int next_var) in
  rv, { e with next_var = next_var + 1 }

let bind name expr ({ bindings; _ } as e) =
  { e with bindings = (name, expr) :: bindings }
