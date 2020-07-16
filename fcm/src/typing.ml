open Core

type row_label = string

type kind =
  | KType
  | KArrow of kind * kind

type var_name = string

type var =
  | Uni of var_name * kind
  | Exi of var_name * kind

type eff =
  | Pure
  | Impure

type 'a row =
  | Fixed of (row_label * 'a) list
  | Open of { fields : (row_label * 'a) list
            ; var : 'a row option
            }

type base_typ =
  | TUnit
  | TInt
  | TBool

(* I'm not sure if this separation is right.

   TODO:  needs links to source AST (core.ml).  Maybe mark "regions" of types
          with core AST nodes.
 *)
type small_typ =
  | TBase of base_typ
  | TRecord of small_typ row
  | TArrow of small_typ * small_typ

and large_typ =
  | TSmol of small_typ
  (* To support applicative/pure functors:  *)
  | TSkol of var_name * large_typ
  | TRow of typ row
  | TL_arrow of eff * large_typ * large_typ
  | TSig of { vars : var list; str : typ row }

and typ =
  | TTyp
  | TSmall of small_typ
  | TLarge of large_typ
            
let rec elab_type_expr _env te =
  match te with
  | { n = TE_Apply (_name, _args); _ } ->
     failwith "No type applications yet supported."
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
         (* t_exprs can contain references to other structure elements.  *)
         let all_vs, rev_elab_typs =
           List.fold_left
             (fun (acc, typs) te ->
               let new_vs, new_typ = elab_type_expr env2 te in
               (acc @ new_vs), (new_typ :: typs)
             )
             (acc_vs, [])
             t_exprs
         in
         let after_elab =
           match rev_elab_typs with
           | [] -> TTyp
           | h :: t-> TLarge (List.fold_left (fun acc n -> TL_arrow (Pure, n, acc)) h t)
         in
         (acc_vs @ (exi_var :: all_vs)), (name, after_elab), env2
    | Transparent_type (_constr, _t_expr) ->
       failwith "No signature transparent type support yet."
    | Val_bind (_name, _t_expr) ->
       failwith "No signature value binding yet."
    in
    (acc_vs @ new_vs), (after_elab :: acc_elabs), env2
  in
  let all_vs, all_elabs, env = List.fold_left hoist_vars ([], [], env) s in
  TSig { vars = List.map (fun v -> Exi (v, KType)) all_vs
       (* TODO:  this is wrong if we're elaborating a signature in a function!
                 Should be open in that case.
        *)
       ; str = Fixed (List.rev all_elabs)
    }
  , env
  
