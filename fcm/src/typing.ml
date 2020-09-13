(*

  [1] 1ML – Core and Modules United (F-ing First-Class Modules)
      https://people.mpi-sws.org/~rossberg/1ml/1ml-jfp-draft.pdf

  Something like this needs to work, tested in the 1ML interpreter:

  X b (c : b) (Y : { type t; init : t }) (x : int) = { v = Y.init; type u = Y.t; bb = c ; xx = x};
  X (Y : { type t; init : t }) (b : type) (c : b) = { v = Y.init; type u = Y.t; bb = c };

  In both cases these are "just functions" that create modules.  For Alpaca, I'd
  like to be able to refer directly to `t` in the function body, rather than
  `Y.t`.

  Type `t` is a universal:
    G (x : { type t; init : t }) = x.init

    X = { type t = int; init = 0 }
    G X; -- should be `int`.

    -- Sealed with an abstract, existential type introduction:
    Y = { type t = int; init = 0; zero = 0 } :> { type t; init : t }
    G Y; -- should be exi[_]
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
  | Unit_F
  | Ident_F of ident
  | Lam_F of (fexp node, ftyp node) abs
  | Abs_F of var * fexp node
  | App_F of fexp node * fexp node
  | Typ_F of ftyp
  (* I'm currently overloading this to handle modules/structures as well.
     Might need to separate those.
   *)
  | Record_F of fexp node row
  (* Deferring signature checking to type checking rather than in elaboration.
   *)
  | Seal_F of fexp node * ftyp node
  (* Transparency/sharing and its validity is done during typing, not during
     elaboration.
   *)
  | With_F of fexp node * (ftyp node * ftyp node) list

(* I'm not sure if this separation between small and large here is right.

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
  | TSkol of var_name * (ftyp node list)
  | TRow of ftyp row
  | TL_arrow of eff * large_typ * large_typ
  | TSig of ftyp node row
[@@deriving show]

and ftyp =
  | TInfer
  | TApp of ftyp node * ftyp node
  | TVar of var_name
  | TBase of base_typ
  | TNamed of ident
  | Abs_FT of var * ftyp node
  | Arrow_F of eff * ftyp node * ftyp node
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
      Abs_FT (var, { n = acc; pos = te.pos })
    in
    let res' = List.fold_right f vs (res.n) in
    { n = res'; pos = te.pos }, env

(* Just trying this out.  *)
and (>>-) { n; pos } f = { n = f n; pos }

(* Elaborate without enclosing in existential abstraction.  *)
and internal_elab env te =
  match te with
  | { n = TE_Bool; pos } ->
     [], { n = TBase TBool; pos }, env
  | { n = TE_Unit; pos } ->
     [], { n = TBase TUnit; pos }, env
  | { n = TE_Var v; pos } ->
     (* This is a reference to a var, not an abstraction.  *)
     [], { n = TNamed (Flat v); pos }, env
  | { n = TE_Apply ({ n; _ }, []); pos } ->
     [], { n = TNamed (Flat n); pos }, env
  | { n = TE_Apply (n, args); pos } ->
     (* No checking here, just elaborate.  *)
     let base = n >>- (fun l -> TNamed (Flat l)) in
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
  | _ ->
     failwith "Cannot yet elaborate this type."

(* Elaborate each of a type constructor's parameters, collect all variable
   names for an enclosing type abstraction, return a tuple of name,
   constructor variable names, and the list of elaborated expressions.
 *)
and elab_constructor ({ n = name; _ }, t_exprs) env =
  (* This checks that the environment before and after elaboration of a
     constructor parameter are equal because of type variables should have
     no side effects.

     Type variables become universals.
   *)
  let (vs, elabs) =
    List.fold_left
      (fun (vs, elabs) next ->
        match internal_elab env next with
        | [], ({ n = TNamed (Flat v); pos } as x), e when e = env ->
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
  let f n acc =
    (* TODO:  positions?  *)
    match n with
    | { n = TNamed (Flat x); pos } ->
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
  List.fold_right f args body

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
                      { n = TNamed (Flat exi_var); pos }
                    else
                      let body =
                        TLarge
                          (TSkol
                             ( exi_var
                             , List.map
                                 (fun (x, { pos; _ }) ->
                                   { n = TNamed (Flat x); pos }
                                 )
                                 unis
                             )
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
  let all_vs, all_elabs, _env = List.fold_left hoist_vars ([], [], env) s in
  (* A signature has an unspecified row variable that is filled in when sealing
     a module.

     TODO:  this should probably be an existential?  Good enough
     to be empty, assume exi?
   *)

  let res = TSig (Open { fields = (List.rev all_elabs); var = None }) in
  all_vs, { n = TLarge res; pos = sig_pos }, env

let rec elab_module env decls pos =
  let f (e, memo) = function
    | Type_decl (c, e) ->
       let _vs, (n, { n = te_elab; pos }), env2 = elab_transparent_type env c e in
       env2, ((n, { n = Typ_F te_elab; pos }) :: memo)
    | Let_bind ({ n; _ }, body) ->
       let elab, e2 = elab e body in
       e2, ((n, elab) :: memo)
    | Variant_decl _ ->
       failwith "No variant declarations in modules yet."
  in
  let env2, rev_decls = List.fold_left f (env, []) decls in
  { n = Record_F (Fixed (List.rev rev_decls)); pos }, env2

and elab_term env e =
  match e with
  | { n = Unit; pos } ->
     { n = Unit_F; pos }, env
  | { n = Label l; pos } ->
     { n = Ident_F (Flat l); pos }, env
  | { n = Core.Dot (x, { n; pos = lpos }); pos } ->
     let x', env2 = elab_term env x in
     let dot = Dot (x', { n = Ident_F (Flat n); pos = lpos }) in
     { n = Ident_F dot; pos }, env2
  | { n = Fun ( (arg, argt), body ); pos } ->
     let arg_typ, env2 =
       Option.map (fun t -> elab_type_expr env t) argt
       |> Option.value ~default:({ n = TInfer; pos }, env)
     in
     let arg, env3 = elab env2 arg in
     let body, env4 = elab env3 body in
     { n = Lam_F { arg; arg_typ = arg_typ; body }; pos }, env4
  | { n = Mod decls; pos } ->
     elab_module env decls pos
  | { n = Seal (e, t); pos } ->
     let ee, env2 = elab_term env e in
     let et, env3 = elab_type_expr env2 t in
     { n = Seal_F (ee, et); pos }, env3
  | { n = With (e, ts); pos } ->
     (* TODO:  why am I using the opposite order of env and term?  FIXME.  *)
     let ee, env2 = elab env e in
     let f (env_m, memo) (k, v) =
       let ek, env_m2 = elab_type_expr env_m k in
       let ev, env_m3 = elab_type_expr env_m2 v in
       env_m3, (ek, ev) :: memo
     in
     let env2, rev_ets = List.fold_left f (env2, []) ts in
     { n = With_F (ee, List.rev rev_ets); pos }, env2
  | _other ->
     failwith ("Unsupported elab of expr:  " ^ ([%derive.show: term node] _other))

and elab env e =
  match e with
  | Type t ->
     let { n = elab; pos }, env2 = elab_type_expr env t in
     { n = Typ_F elab; pos }, env2
  | Term t ->
     elab_term env t
