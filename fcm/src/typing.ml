(*

  [1] 1ML – Core and Modules United (F-ing First-Class Modules)
      https://people.mpi-sws.org/~rossberg/1ml/1ml-jfp-draft.pdf
*)
open Core

type row_label = string
[@@deriving show]

type kind =
  | KType
  | KArrow of kind * kind
[@@deriving show]

type var_name = string
[@@deriving show]

type var =
  | Uni of var_name * kind
  | Exi of var_name * kind
[@@deriving show]

type eff =
  | Pure
  | Impure
[@@deriving show]

type 'a row =
  | Fixed of (row_label * 'a) list
  | Open of { fields : (row_label * 'a) list
            ; var : 'a row option
            }
[@@deriving show]

type base_typ =
  | TUnit
  | TInt
  | TBool
[@@deriving show]

(* I'm not sure if this separation is right.

   TODO:  needs links to source AST (core.ml).  Maybe mark "regions" of types
          with core AST nodes.
 *)
type small_typ =
  (* Don't permit a variable to be inhabited by a large type.  Section 2 of [1],
     "Predicativity", page 14.
   *)
  | TVar of string
  | TBase of base_typ
  | TRecord of small_typ row
  | TArrow of small_typ * small_typ
[@@deriving show]

and large_typ =
  | TTyp of var_name
  (* Various f-omega AST nodes don't contain their types, they're enclosed by
     a type abstraction.  (a Λ rather than a λ)

     TODO:  should this maintain the mapping of original type names to
            synthesized existential names?
   *)
  | TAbs of var * large_typ
  | TSmol of small_typ
  | TApp of typ * typ
  (* To support applicative/pure functors:  *)
  | TSkol of var_name * large_typ
  | TRow of typ row
  | TL_arrow of eff * large_typ * large_typ
  (* A signature _should_ only abstract with existentials, whereas functors can
     abstract with both existential and universal variables.
   *)
  | TSig of typ row
[@@deriving show]

and typ =
  | TSmall of small_typ
  | TLarge of large_typ
[@@deriving show]

let perform_type_apply constructor args =
  let rec f c a =
    match c, a with
    | TL_arrow (Pure, _, b), h :: t -> TLarge (TApp (h, f b t))
    | TL_arrow _, [] -> failwith "Type application arity mismatch."
    | (TTyp _) as t, [] -> TLarge t
    | _other, _ -> failwith ("Invalid type application to " ^ ([%derive.show: large_typ] _other))
  in
  f constructor args

(* If the given type is a signature, bind its types in the environment given.  *)
let bind_from_sig t env =
  let rec lf e =
    match e with
    | TAbs (_, other) -> lf other
    | (TSig (Open { fields; _ }))->
       print_endline "Binding sig members.";
       List.fold_left (fun e (n, t) -> Env.bind (Local n) t e) env fields
    | _ -> env
  in
  match t with
  | TLarge l -> lf l
  | _other ->
     print_endline ([%derive.show: typ] _other);
     env

let rec elab_type_expr env te =
  let vs, res, env = internal_elab env te in
  match res with
  | TLarge l ->
     let res = List.fold_right (fun (_n, v) acc -> TAbs (Exi (v, KType), acc)) vs l in
     vs, TLarge res, env
  | TSmall s when List.length vs = 0 ->
     vs, TSmall s, env
  | TSmall s ->
     failwith ("Small types cannot introduce types/type variables:  " ^ ([%derive.show: small_typ] s))

(* Elaborate without enclosing in existential abstraction.  *)
and internal_elab env te =
  match te with
  | { n = Var v; _ } ->
     [], TSmall (TVar v), env
  | { n = TE_Apply ({ n; _ }, args); _ } ->
     let f = match Env.local n env with
       | Some (TLarge f) -> f
       | Some (TSmall _) -> failwith "Small types can't be type constructors."
       | None -> failwith (n ^ " not in scope")
     in
     (* Each argument must be expanded to a _small_ type (predicativity).
        Since only small types are allowed, we aren't expanding the environment's
        bindings, nor are we creating new universal or existential variables.
        As a result, only non-side-effecting elaborations are allowed, and we
        don't need to mutate the environment.
      *)
     let elab_and_check_small t_expr =
       match internal_elab env t_expr with
       | [], ((TSmall _) as x), e when e = env -> x
       | _ -> failwith "Type constructor predicativity violation."
     in
     let elab_args = List.map elab_and_check_small args in
     [], perform_type_apply f elab_args, env
  | { n = TE_Arrow (a, b); _ } ->
     let vs1, elab_a, env2 = internal_elab env a in
     (* Types explicit in elab_a should be available to b.  *)
     let env2 = bind_from_sig elab_a env2 in
     let vs2, elab_b, env3 = internal_elab env2 b in
     let arr = match elab_a, elab_b with
       (* Assume impure for now until syntax expands to allow pure.  *)
       | TLarge a, TLarge b -> TL_arrow (Impure, a, b)
       | TLarge a, TSmall b -> TL_arrow (Impure, a, TSmol b)
       | _ -> failwith "Unsupported arrow type expression."
     in
     vs1 @ vs2, (TLarge arr), env3
  | { n = Signature  decls; _ } ->
     elab_sig env decls
  | _ ->
     failwith "Cannot yet elaborate this type."
    
(* Any internal dependency between nested signature elements needs to have an
   existential hoisted out to the outer level.
 *)
and elab_sig env s =
  (* Not the best name for this function but basically does two things at the
     same time:
       1. Turn opaque types into existential variables for the signature.
       2. Elaborate type expressions inside type expressions.

     I'm still fuzzy on how I'll move these around for a function/functor but
     working through this is helping me to connect the 1ML paper and associated
     interpreter, gluing concepts together a bit better.
   *)
  let hoist_vars (acc_vs, acc_elabs, env) next =
    let (new_vs, after_elab, env2) = match next with
      (* TODO:  positions *)
      | Opaque_type ({ n = name; _ }, t_exprs) ->
         let exi_var, env2 = Env.next_var env in
         (* This throws away the environment after elaborating because the
            elaboration of type variables should have no side effect.
          *)
         let map_elab te f =
           match internal_elab env2 te with
           | [], TSmall (TVar v), e when e = env2 -> f v
           | _ -> failwith "Only type variables allowed as opaque type args"
         in
         (* t_exprs can contain references to other structure elements.  *)
         let f acc next =
           map_elab next (fun v -> TL_arrow (Pure, TSmol (TVar v), acc))
         in
         begin
           match (List.rev t_exprs) with
           | [] ->
              [name, exi_var], (name, TLarge (TTyp exi_var)), env2
           | xs ->
              let elab = TLarge (List.fold_left f (TTyp exi_var) xs) in
              (* TODO:  this is wrong, needs to be a map from synthesized var
                        name to `var` type, use name to link to that map.
               *)
              [name, exi_var], (name, elab), Env.bind (Local name) elab env2
         end

    | Transparent_type (_constr, _t_expr) ->
       failwith "No signature transparent type support yet."
    | Transparent_variants ((_name, _args), _vs) ->
       failwith "No signature variants typing support yet."
    | Val_bind ({ n; _}, t_expr) ->
       (* Value bindings can both describe functors and close over types defined
          in their enclosing module.  This means that they may introduce new
          existentials that depend on other existentials within the module.
          For the sake of simplicity, the existentials types introduced by a
          value binding will thus be lifted out.
        *)
       let vs, elab, env2 = internal_elab env t_expr in
       vs, (n, elab), env2
    in
    (acc_vs @ new_vs), (after_elab :: acc_elabs), env2
  in
  let all_vs, all_elabs, _env = List.fold_left hoist_vars ([], [], env) s in
  (* OLD:
     let vars = List.map (fun (n, v) -> (n, Exi (v, KType))) all_vs in
   *)
  (* A signature has an unspecified row variable.
     TODO:  this should probably be an existential?  Good enough
     to be empty, assume exi?
   *)
  
  let s = TSig (Open { fields = (List.rev all_elabs); var = None }) in
  all_vs, (TLarge s), env
