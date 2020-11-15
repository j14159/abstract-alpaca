type namespace =
  | Local of string
  (* For dotted reference, e.g. Module.label  *)
  | Scoped of string * namespace


type 'a t = {
    (* For type unification and inference.  *)
    level : int
  (* Synthetic/generated variable names. *)
  ; next_var : int
  ; bindings : (namespace * 'a) list
  (* For type -> kind bindings.  *)
  ; types : (namespace * 'a) list
  }

let var_prefix = "v_"

let make _ =
  { level = 0
  ; next_var = 0
  ; bindings = []
  ; types = []
  }

let level { level; _ } = level

let next_var ({ next_var; _ } as e) =
  let rv = var_prefix ^ (string_of_int next_var) in
  rv, { e with next_var = next_var + 1 }

let bind name expr ({ bindings; _ } as e) =
  { e with bindings = (name, expr) :: bindings }

let local name { bindings; _ } =
  List.assoc_opt (Local name) bindings

let bind_type name kind ({ types; _ } as e) =
  { e with types = (name, kind) :: types }

let local_type name { types; _ } =
  List.assoc_opt (Local name) types

let enter_level ({ level; _ } as e) =
  { e with level = level + 1 }
let leave_level ({ level; _ } as e) =
  { e with level = level - 1 }

let next_level ({ level; _ } as env) f =
  let e2, res = f { env with level = level + 1 } in
  { e2 with level }, res
