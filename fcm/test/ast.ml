(*
  Eventually needs to move to the main library, just making some convenience
  functions easier to share across tests.
 *)
open Fcm.Core
open Fcm.Typing

let null_node x = { n = x; pos = null_pos }
let pseudo_pos idx = { uri = ""; col = 0; line = idx }

module Core_ast = struct
  let str ~pos decls = { n = Mod decls; pos }
  let type_decl constr t_expr = Type_decl (constr, t_expr)

  let t_unit ~pos = { n = TE_Unit; pos }
  let t_bool ~pos = { n = TE_Bool; pos }
  let t_int ~pos = { n = TE_Int; pos }


  let bind ~pos name expr = Let_bind ({ n = name; pos }, expr)
  let v_bool ~pos b = Term { n = b; pos }
  let v_fun ~pos arg arg_t body = Term { n = Fun ((arg, arg_t), body); pos }
  let v_label ~pos l = Term { n = Label l; pos }

  let te_arrow ~pos a b = { n = TE_Arrow (a, b); pos }
  let te_named ~pos n = { n = TE_Named n; pos }

  let let_bind name expr = Let_bind (name, expr)
end

module Null_pos_core = struct
  include Core_ast
  let np_str = str ~pos:null_pos
  let np_t_unit = t_unit ~pos:null_pos
  let np_t_bool = t_bool ~pos:null_pos
  let np_v_bool = v_bool ~pos:null_pos
  let np_t_int = t_int ~pos:null_pos
  let np_bind = bind ~pos:null_pos

  let np_v_fun = v_fun ~pos:null_pos
  let np_v_label = v_label ~pos:null_pos
  let np_te_arrow = te_arrow ~pos:null_pos
  let np_te_named = te_named ~pos:null_pos
  let np_t_fun = v_fun ~pos:null_pos
end

(* Convenience methods for the System F AST.  They're here as a sort of
   prototyping/staging area and will move somewhere like src/typing.ml
   later.
 *)
module F_ast = struct
  let tbase b = null_node (TBase b)
  let tvar n = null_node (TVar n)
  let tnamed n = null_node (TNamed n)
  let tarrow eff x y = null_node (Arrow_F (eff, x, y))
  let tsig ?row:(var = Absent) fs = null_node (TRow { fields = fs; var })
  let tabs v e = null_node (Abs_FT (v, e))
  let tapp x y = null_node (TApp (x, y))
  let tskol a vs = null_node (TSkol (a, vs))
  let uni n k = Uni (n, k)
  let exi n k = Exi (n, k)

  let abs var body = { n = Abs_F (var, body); pos = null_pos }
  let ident n = null_node (Ident_F n)
  let app a b = null_node (App_F (a, b))

  let str_sig ~pos decls = { n = Signature decls; pos }
  let np_str_sig = str_sig ~pos:null_pos

  let constr : pos:pos -> identifier -> type_expr node list -> type_constructor =
    fun ~pos name args -> ({ n = name; pos }, args)

  let np_constr = constr ~pos:null_pos

  let t_var ~pos name = { n = TE_Var name; pos }
  let np_t_var = t_var ~pos:null_pos

  let opaque_decl constr = Opaque_type constr
  let val_decl name body = Val_bind (name, body)
end
