(*

  [1] 1ML – Core and Modules United (F-ing First-Class Modules)
      https://people.mpi-sws.org/~rossberg/1ml/1ml-jfp-draft.pdf
*)
open Core

(* Raised when substitution of large types for small is attempted.
   E.g. when a signature/module is provided in place of a type variable.
 *)
exception Predicativity_violation of pos

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

let var_kind = function
  | Uni (_, k) -> k
  | Exi (_, k) -> k

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

type ('arg, 'arg_typ) abs = { arg : 'arg; arg_typ : 'arg_typ; body : fexp node }

and ident =
  | Dot of fexp node * fexp node
  | Flat of var_name

(* System F-Omega expressions.  *)
and fexp =
  | Ident_F of ident
  | Lam_F of (fexp node, ftyp option) abs
  | Abs_F of var * fexp node
  | App_F of fexp node * fexp node
  | Typ_F of ftyp
  | Record_F of fexp row
(* I'm not sure if this separation is right.

   TODO:  needs links to source AST (core.ml).  Maybe mark "regions" of types
          with core AST nodes.
 *)
and small_typ =
  | TRecord of small_typ row
  | TArrow of small_typ * small_typ
[@@deriving show]

and large_typ =
  | TTyp of var_name
  | TSmol of small_typ
  | TApp of ftyp * ftyp
  | TSkol of var_name * (fexp node list)
  | TRow of ftyp row
  | TL_arrow of eff * large_typ * large_typ
  | TSig of fexp node row
[@@deriving show]

and ftyp =
  | TVar of var_name
  | TBase of base_typ
  | TNamed of ident
  | Abs_FT of var * ftyp
  | Arrow_F of eff * fexp node * fexp node
  | TSmall of small_typ
  | TLarge of large_typ
[@@deriving show]

let rec elab_type_expr env te =
  (* `vs` must be `(string, var) list`  *)
  let vs, res, env = internal_elab env te in
  if List.length vs = 0 then
    res, env
  else
    let f (_name, var) acc =
      (* TODO:  I'm using the position for the whole type expression here but
                should be using the position for each argument.
       *)
      Abs_F (var, { n = acc; pos = te.pos })
    in
    match res with
    | { n = Typ_F res; _ } ->
       let res = List.fold_right f vs (Typ_F res) in
       { n = res; pos = te.pos }, env
    | _ ->
       failwith "Unreachable base case, elab_type_expr should have returned a ftyp"

(* Just trying this out.  *)
and (>>-) { n; pos } f = { n = f n; pos }

(* Elaborate without enclosing in existential abstraction.  *)
and internal_elab env te =
  match te with
  | { n = TE_Bool; pos } ->
     [], { n = Typ_F (TBase TBool); pos }, env
  | { n = TE_Unit; pos } ->
     [], { n = Typ_F (TBase TUnit); pos }, env
  | { n = TE_Var v; pos } ->
     (* This is a reference to a var, not an abstraction.  *)
     [], { n = Ident_F (Flat v); pos }, env
  | { n = TE_Apply ({ n; _ }, []); pos } ->
     [], { n = Typ_F (TNamed (Flat n)); pos }, env
  | { n = TE_Apply (n, args); pos } ->
     (* No checking here, just elaborate.  *)
     let base = n >>- (fun l -> Ident_F (Flat l)) in
     let rec f = function
       | [x] ->
          let _, x, _ = internal_elab env x in
          x
       | ({ pos; _ } as x) :: xs ->
          let _, x, _ = internal_elab env x in
          let rem = f xs in
          { n = App_F (x, rem); pos }
       | [] -> failwith "Unreachable base case, empty apply."
     in
     [], { n = App_F (base, f args); pos }, env
  | { n = TE_Arrow (a, b); pos } ->
     let vs1, elab_a, env2 = internal_elab env a in
     let vs2, elab_b, env3 = internal_elab env2 b in
     begin
       match elab_a, elab_b with
       | { n = Typ_F _; _ }, { n = Typ_F _; _ } ->
          vs1 @ vs2, { n = Typ_F (Arrow_F (Impure, elab_a, elab_b)); pos }, env3
       | { pos; _ }, _ ->
          failwith ("Could not elaborate to F-omega term:  " ^ ([%derive.show: pos] pos))
     end
  | { n = Signature  decls; pos } ->
     elab_sig env decls pos
  | _ ->
     failwith "Cannot yet elaborate this type."

(* Any internal dependency between nested signature elements needs to have an
   existential hoisted out to the outer level.
 *)
and elab_sig env s sig_pos =
  (* Not the best name for this function but basically does two things at the
     same time:
       1. Turn opaque types into existential variables for the signature.
       2. Elaborate type expressions inside type expressions.

     I'm still fuzzy on how I'll move these around for a function/functor but
     working through this is helping me to connect the 1ML paper and associated
     interpreter, gluing concepts together a bit better.
   *)
  let hoist_vars (acc_vs, acc_elabs, env) next =
    (* Transparent and Opaque type constructors both need to make type
       abstractions (`Abs_F`) that differ only in the "body" (implementation?)
       of the abstraction.
     *)
    let make_abstraction args unis body =
      let f n acc =
        (* TODO:  positions?  *)
        match n with
        (* TODO:  Ident_F instead.   *)
        | { n = Ident_F (Flat x); pos } ->
           (* TODO:  real failure, not from List.assoc.  *)
           let { n = v; _ } = List.assoc x unis in
           { n = Abs_F (v, acc); pos }
        | { n; pos } ->
           (* TODO:  be less lazy and make a real exception.  *)
           failwith ( "Can't make a type constructor argument with "
                      ^ ([%derive.show: fexp] n)
                      ^ " at position "
                      ^ ([%derive.show: pos] pos)
             )
      in
      List.fold_right f args body
    in

    (* Elaborate each of the constructor's parameters, collect all variable
       names for an enclosing type abstraction, return a tuple of name,
       constructor variable names, and the list of elaborated expressions.
     *)
    let elab_constructor ({ n = name; _ }, t_exprs) env =
      (* This checks that the environment before and after elaboration of a
         constructor parameter are equal because of type variables should have
         no side effects.

         Type variables become universals.
       *)
      let (vs, elabs) =
        List.fold_left
          (fun (vs, elabs) next ->
            match internal_elab env next with
            | [], ({ n = Ident_F (Flat v); pos } as x), e when e = env ->
               let vs = (v, { n = Uni (v, KType); pos }) :: vs in
               let elabs = x :: elabs in
               vs, elabs
            | _, { pos; _ }, _ ->
               (* TODO:  real exception.  *)
               failwith
                 ("Elaboration failed, Only type variables allowed as constructor args"
                  ^ ([%derive.show: pos] pos)
                 )
          )
          ([], [])
          t_exprs
      in
      name, vs, elabs
    in
    let (new_vs, after_elab, env2) = match next with
      (* Must be transparently equivalent to the existential qualified with
         (or applied to - skolem function?) the additional present arguments
         or variables.
       *)
      | Opaque_type c ->
         let exi_var, env2 = Env.next_var env in
         (* Make Abs_TF from `unis`, Lam_F from `args`.  *)
         let name, unis, args = elab_constructor c env2 in
         let elab = if List.length args = 0 then
                      let ({ pos; _ }, _) = c in
                      { n = Typ_F (TNamed (Flat exi_var)); pos }
                    else
                      let body =
                        TLarge
                          (TSkol
                             ( exi_var
                             , List.map
                                 (fun (x, { pos; _ }) ->
                                   { n = Typ_F (TNamed (Flat x)); pos }
                                 )
                                 unis
                             )
                          )
                      in
                      let ({ pos; _ }, _) = c in
                      make_abstraction args unis { n = Typ_F body; pos }
         in
         [name, Exi (exi_var, KType)], (name, elab), Env.bind (Local name) elab.n env2
      | Transparent_type (constr, t_expr) ->
         (* The definition of a type constructor can only have variables as
            arguments.

            FIXME:  elab_constructor will fail internally if an argument is not
                    a type variable.  This feels opaque and bad maybe?
          *)
         let name, unis, args = elab_constructor constr env in
         let vs, res, env2 = internal_elab env t_expr in
         begin
           let body = match res with
             | { n = Typ_F TNamed (Flat _); _ } as x -> x
             | { n = App_F _; _ } as x -> x
             | other ->
                (* TODO:  proper elaboration expression.  *)
                failwith ("Can't use " ^ ([%derive.show: fexp node] other) ^ " for type body")
           in
           let elab = make_abstraction args unis body in
            vs, (name, elab), Env.bind (Local name) elab.n env2
         end
      | Transparent_variants ((_name, _args), _vs) ->
         failwith "No signature variants typing support yet."
      | Val_bind ({ n; _}, t_expr) ->
         (* Value bindings can both describe functors and close over types defined
          in their enclosing module.  This means that they may introduce new
          existentials that depend on other existentials within the module.
          For the sake of simplicity, the existential types introduced by a
          value binding will thus be lifted out.
          *)
         begin
           match internal_elab env t_expr with
           | vs, ({ n = Typ_F _; _ } as elab), env2 ->
              vs, (n, elab), env2
           | _, other, _ ->
              failwith ("Can't use " ^ ([%derive.show: fexp node] other) ^ " for val binding.")
         end
    in
    (acc_vs @ new_vs), (after_elab :: acc_elabs), env2
  in
  let all_vs, all_elabs, _env = List.fold_left hoist_vars ([], [], env) s in
  (* A signature has an unspecified row variable.
     TODO:  this should probably be an existential?  Good enough
     to be empty, assume exi?
   *)

  let res = TSig (Open { fields = (List.rev all_elabs); var = None }) in
  all_vs, { n = Typ_F (TLarge res); pos = sig_pos }, env
