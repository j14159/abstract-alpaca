type ('a, 'b) t = {
    (* For type unification and inference.  *)
    level : int
  (* Synthetic/generated variable names. *)
  ; next_var : int
  ; bindings : (Core.identifier * 'a) list
  (* For type -> kind bindings.  *)
  ; types : (Core.identifier * 'b) list
  }
[@@deriving show]

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

let get name { bindings; _ } =
  List.assoc_opt name bindings

let bind_type name kind ({ types; _ } as e) =
  { e with types = (name, kind) :: types }

let get_type name { types; _ } =
  List.assoc_opt name types

let enter_level ({ level; _ } as e) =
  { e with level = level + 1 }
let leave_level ({ level; _ } as e) =
  { e with level = level - 1 }

let next_level ({ level; _ } as env) f =
  let e2, res = f { env with level = level + 1 } in
  { e2 with level }, res

let bindings { bindings; _ } = bindings
