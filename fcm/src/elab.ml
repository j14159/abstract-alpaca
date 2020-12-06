(** Elaboration into System F terms, eventually System F-omega proper.

 *)
open Core
open Typing

let rec elab_type_expr env te =
  (* `vs` must be `(string, var) list`  *)
  let vs, res, env = internal_elab env te in
  if List.length vs = 0 then
    env, res
  else
    let f (_name, var) acc =
      (* TODO:  I'm using the position for the whole type expression here but
                should be using the position for each argument.
       *)
      Abs_FT (var, { n = acc; pos = te.pos })
    in
    let res' = List.fold_right f vs (res.n) in
    env, { n = res'; pos = te.pos }

(* Just trying this out.  *)
and (>>-) { n; pos } f = { n = f n; pos }

(* Elaborate without enclosing in existential abstraction.  *)
and internal_elab env te =
  match te with
  | { n = TE_Unit; pos } ->
     [], { n = TBase TUnit; pos }, env
  | { n = TE_Bool; pos } ->
     [], { n = TBase TBool; pos }, env
  | { n = TE_Int; pos } ->
     [], { n = TBase TInt; pos }, env
  | { n = Named n; pos } ->
     [], { n = TNamed  n; pos }, env
  | { n = TE_Var v; pos } ->
     (* This is a reference to a var, not an abstraction.  *)
     [], { n = TNamed v; pos }, env
  | { n = TE_Apply ({ n; _ }, []); pos } ->
     [], { n = TNamed n; pos }, env
  | { n = TE_Apply (n, args); pos } ->
     (* No checking here, just elaborate.  *)
     let base = n >>- (fun l -> TNamed l) in
     let rec f = function
       | [x] ->
          let _, x, _ = internal_elab env x in
          x
       | ({ pos; _ } as x) :: xs ->
          let _, x, _ = internal_elab env x in
          let rem = f xs in
          { n = TApp (x, rem); pos }
       | [] -> failwith "Unreachable base case, empty apply."
     in
     [], { n = TApp (base, f args); pos }, env
  | { n = TE_Arrow (a, b); pos } ->
     let vs1, elab_a, env2 = internal_elab env a in
     let vs2, elab_b, env3 = internal_elab env2 b in
     vs1 @ vs2, { n = Arrow_F (Impure, elab_a, elab_b); pos }, env3
  | { n = Signature  decls; pos } ->
     elab_sig env decls pos
  | { n; _ } ->
     failwith ("Cannot yet elaborate this type:  " ^ ([%derive.show: type_expr] n))

(* Elaborate each of a type constructor's parameters, collect all variable
   names for an enclosing type abstraction, return a tuple of name,
   constructor variable names, and the list of elaborated expressions.
 *)
and elab_constructor ({ n = name; _ }, t_exprs) env =
  (* This checks that the environment before and after elaboration of a
     constructor parameter are equal because type variables should have
     no side effects.

     Type variables become universals.
   *)
  let (vs, elabs) =
    List.fold_left
      (fun (vs, elabs) next ->
        match internal_elab env next with
        | [], ({ n = TNamed v; pos } as x), e when e = env ->
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
  name, (List.rev vs), elabs

(* Both signatures and modules can describe "transparent" types, where the
   implementation of the type is exposed to the user of it.  Signature and
   module declarations use different variants to describe these, but the same
   tuple of constructor and type expression body.  This function makes the
   elaboration of those common pieces a shared abstraction rather than buried in
   one elaboration method or the other.
 *)
and elab_transparent_type env constr t_expr =
  (* The definition of a type constructor can only have variables as
     arguments.

     FIXME:  elab_constructor will fail internally if an argument is not
     a type variable.  This feels opaque and bad maybe?
   *)
  let name, unis, args = elab_constructor constr env in
  let vs, res, env2 = internal_elab env t_expr in
  begin
    let body = match res with
      | { n = TApp _; _ } as x ->
         x
      | { n = TBase _; _ } as x ->
         x
      | other ->
         (* TODO:  proper elaboration expression.  *)
         failwith ("Can't use " ^ ([%derive.show: ftyp node] other) ^ " for type body")
    in
    let elab = make_abstraction args unis body in
    vs, (name, elab), env2
  end

(* Transparent and Opaque type constructors both need to make type
   abstractions (`Abs_FT`) that differ only in the "body" (implementation?)
   of the abstraction.  `Abs_FT` here is a "for all" or "for some" (universal
   and existential respectively) component of a type.
 *)
and make_abstraction args unis body =
  let f acc n =
    (* TODO:  positions?  *)
    match n with
    | { n = TNamed x; pos } ->
       (* TODO:  real failure, not from List.assoc.  *)
       let { n = v; _ } = List.assoc x unis in
       { n = Abs_FT (v, acc); pos }
    | { n; pos } ->
       (* TODO:  be less lazy and make a real exception.  *)
       failwith ( "Can't make a type constructor argument with "
                  ^ ([%derive.show: ftyp] n)
                  ^ " at position "
                  ^ ([%derive.show: pos] pos)
         )
  in
  List.fold_left f body args

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
                      { n = TNamed exi_var; pos }
                    else
                      let body =
                        TSkol
                          ( exi_var
                          , List.map
                              (fun (x, { pos; _ }) ->
                                { n = TNamed x; pos }
                              )
                              unis
                          )
                      in
                      let ({ pos; _ }, _) = c in
                      make_abstraction args unis { n = body; pos }
         in
         [name, Exi (exi_var, KType)], (name, elab), env2
      | Transparent_type (constr, t_expr) ->
         elab_transparent_type env constr t_expr
      | Transparent_variants ((_name, _args), _vs) ->
         failwith "No signature variants typing support yet."
      | Val_bind ({ n; _}, t_expr) ->
         (* Value bindings can both describe functors and close over types defined
          in their enclosing module.  This means that they may introduce new
          existentials that depend on other existentials within the module.
          For the sake of simplicity, the existential types introduced by a
          value binding will thus be "hoisted" out.
          *)
         begin
           let vs, elab, env2 = internal_elab env t_expr in
           vs, (n, elab), env2
         end
    in
    (acc_vs @ new_vs), (after_elab :: acc_elabs), env2
  in
  let all_vs, all_elabs, env = List.fold_left hoist_vars ([], [], env) s in
  (* A signature has an unspecified row variable that is filled in when sealing
     a module.

     TODO:  this should probably be an existential?  Good enough
     to be empty, assume exi?
   *)

  let res = TRow { fields = (List.rev all_elabs); var = Absent } in
  all_vs, { n = res; pos = sig_pos }, env

let rec elab_module env decls pos =
  let f (e, memo) = function
    | Type_decl (c, e) ->
       let _vs, (n, { n = te_elab; pos }), env2 = elab_transparent_type env c e in
       env2, ((n, { n = Typ_F te_elab; pos }) :: memo)
    | Let_bind ({ n; _ }, body) ->
       let e2 = Env.enter_level e in
       let e3, elab = elab e2 body in
       Env.leave_level e3, ((n, elab) :: memo)
    | Variant_decl _ ->
       failwith "No variant declarations in modules yet."
  in
  let env2, rev_decls = List.fold_left f (env, []) decls in
  env2, { n = Structure_F { fields = (List.rev rev_decls); var = Empty }; pos }

and elab_term env e =
  match e with
  | { n = Unit; pos } ->
     env, { n = Unit_F; pos }
  | { n = Label l; pos } ->
     env, { n = Ident_F l; pos }
  | { n = Core.Dot (x, { n; pos = lpos }); pos } ->
     let env2, x' = elab_term env x in
     let path = Path (x', { n = Ident_F n; pos = lpos }) in
     env2, { n = path; pos }
  | { n = Fun ( (arg, argt), body ); pos } ->
     let env2 = Env.enter_level env in
     let env3, arg_typ =
       Option.map (fun t -> elab_type_expr env t) argt
       |> Option.value ~default:(let e, v = new_var env2 in e, { n = v; pos })
     in
     let env4, arg = elab env3 arg in
     let env5, body = elab env4 body in
     Env.leave_level env5, { n = Lam_F { arg; arg_typ = arg_typ; body }; pos }
  | { n = Mod decls; pos } ->
     elab_module env decls pos
  | { n = Seal (e, t); pos } ->
     let env2, ee = elab_term env e in
     let env3, et = elab_type_expr env2 t in
     env3, { n = Seal_F (ee, et); pos }
  | { n = With (e, ts); pos } ->
     let env2, ee = elab env e in
     let f (env_m, memo) (k, v) =
       let env_m2, ek = elab_type_expr env_m k in
       let env_m3, ev = elab_type_expr env_m2 v in
       env_m3, (ek, ev) :: memo
     in
     let env3, rev_ets = List.fold_left f (env2, []) ts in
     env3, { n = With_F (ee, List.rev rev_ets); pos }
  | _other ->
     failwith ("Unsupported elab of expr:  " ^ ([%derive.show: term node] _other))

and elab env e =
  match e with
  | Type t ->
     let env2, { n = elab; pos } = elab_type_expr env t in
     env2, { n = Typ_F elab; pos }
  | Term t ->
     elab_term env t

