(*

  [1] 1ML – Core and Modules United (F-ing First-Class Modules)
      https://people.mpi-sws.org/~rossberg/1ml/1ml-jfp-draft.pdf
  [2] F-ing Modules
      https://people.mpi-sws.org/~rossberg/f-ing/f-ing-jfp.pdf

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

(** Modules (structures) are typed as rows that are not extensible.

    More specifically:  an open (extensible) row can only be used as an argument
    to a function (functor).  This exception is thrown if an "open" module makes
    it to the typer.
 *)
exception Unexpected_open_structure of pos

type row_label = string
[@@deriving show]

exception Strict_row_size of (row_label list * pos)
(* If a row unification's lower bound already has a "Present" row variable.  *)
exception Extended_row_constraint of pos

(* Raised when a row tries to unify with a non-row.  *)
exception Invalid_row_match of (pos * pos)

exception Missing_row_field of pos * row_label

(* TODO:  bad name for "the variables in the constraint don't match those in the
          thing you're trying to match".
 *)
exception Sig_abstraction_fail of pos * pos

(* TODO:  bad name for "you're not actually matching signatures/structures."  *)
exception Not_signatures of pos * pos

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

let var_name = function
  | Uni (n, _) -> n
  | Exi (n, _) -> n

type eff =
  | Pure
  | Impure
[@@deriving show]

type 'a row = { fields : (row_label * 'a) list
              ; var : 'a row_var
              }
[@@deriving show]
and 'a row_var =
  | Absent
  | Empty
  | Present of 'a row
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
  | Bool_F of bool
  | Ident_F of ident
  | Lam_F of (fexp node, ftyp node) abs
  | Abs_F of var * fexp node
  | App_F of fexp node * fexp node
  | Typ_F of ftyp
  | Structure_F of fexp node row
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

and ftyp =
  | TInfer of infer_cell ref
  | TApp of ftyp node * ftyp node
  | TVar of var_name
  (* Track universals and existentials as legitimate types.  *)
  | TAbs_var of var
  | TBase of base_typ
  | TNamed of ident
  | Abs_FT of var * ftyp node
  | Arrow_F of eff * ftyp node * ftyp node
  | TSkol of var_name * (ftyp node list)
  | TSig of ftyp node row
  | TRow of ftyp row
[@@deriving show]

and level = int
[@@deriving show]
and infer_cell =
  | Unbound of string * level
  (* Tracking of the location where the `infer_cell` was first introduced should
     be handled by the `ftyp node` that encloses this cell.  The link variant
     here requires `ftyp node` as well so that we can track where the inferred
     type constraint was discovered during unification.
   *)
  | Link of ftyp node
[@@deriving show]

(** Raised during signature matching when an item from the constraint can't
    substitute for one in the candidate.  An example of this when sealing:

        {[ { type t 'a } :> { type t } ]}

    In the above example, the constraint's [t] is not structurally equivalent to
    the candidate's [t] since their arities differ.
 *)
exception Invalid_substitution of ftyp node * ftyp node
[@@deriving show]

let new_var env =
  let v, env2 = Env.next_var env in
  env2, TInfer (ref (Unbound (v, Env.level env2)))

let rec gen env = function
  | { n = TInfer { contents = Unbound (name, lvl) }; pos } when lvl > Env.level env ->
     { n = TVar name; pos }
  | { n = Arrow_F (eff, a, b); pos } ->
     { n = Arrow_F (eff, gen env a, gen env b); pos }
  | t -> t

let rec type_of env e =
  match e with
  | { n = Typ_F t; pos } ->
     (* let ret = { n = t; pos } in *)
     env, evaluate_type env { n = t; pos }
  | { n = Unit_F; pos } ->
     env, { n = TBase TUnit; pos }
  | { n = Bool_F _; pos } ->
     env, { n = TBase TBool; pos }
  | { n = Ident_F (Flat name); _ } ->
     env, Option.get (Env.local name env)
  | { n = Lam_F { arg = { n = Ident_F (Flat a); _ }; arg_typ; body }; pos } ->
     let arg_typ = evaluate_type env arg_typ in
     let env2 = Env.bind (Local a) arg_typ env in
     let env3, tb = type_of env2 body in
     env3, { n = Arrow_F (Impure, arg_typ, tb); pos }
  (* Only variables marked as "empty" can be typed for structures since as
     an expression, they're always literal and never a pattern or type.

     TODO:  module patterns in functors instead of `var : type`?  If this were
            permitted then the row variable would need to allow `Absent` as
            well.
   *)
  | { n = Structure_F ({ fields = decls; var = Empty }); pos } ->
     let f (env, memo) (name, next_decl) =
       let env2 = Env.enter_level env in
       let env3, typ = type_of env2 next_decl in
       let generalized = gen env3 typ in
       let env4 = Env.bind (Env.Local name) generalized env3 in
       (Env.leave_level env4, (name, generalized) :: memo)
     in
     let env2, rev_types = List.fold_left f (env, []) decls in
     env2, { n = TSig { fields = List.rev rev_types; var = Absent }; pos }
  | { n = Structure_F { var = Absent; _ }; pos } ->
     raise (Unexpected_open_structure pos)
  | { n = Seal_F (expr, seal_with); pos } ->
     let env2, term_typ = type_of env expr in
     let _ = signature_match env seal_with term_typ in
     let { n; _ } = seal_with in
     env2, { n; pos }
  | { n = other; _ } ->
     failwith ("Can't type this yet:  " ^ ([%derive.show: fexp] other))

and unify env t_constraint t_to_check =
  if t_constraint = t_to_check then ()
  else match t_constraint, t_to_check with
       | { n = TNamed (Flat a); _ }, b ->
         unify env (Option.get (Env.local a env)) b
       | a, { n = TNamed (Flat b); _ } ->
          unify env a (Option.get (Env.local b env))
       | { n = TAbs_var (Exi _); _ }, { n = TAbs_var (Exi _); _ } ->
          failwith "Can't unify existentials."
       | _ -> raise (Failure ("Can't unify this yet:  "
                              ^ ([%derive.show: ftyp node] t_constraint)
                              ^ " and "
                              ^ ([%derive.show: ftyp node] t_to_check))
                )

(* TODO:  missing, valid signature check for internal consistency and
          correctness.

   If the candidate correctly matches the constraint, the returned signature's
   row will contain the extra members from the candidate.  It is up to the
   caller whether or not this information is "forgotten".  Sealing needs to
   forget, while functors do not.

   Order of operations:
     - Recursively match type abstractions (existentials).
     - Add existentials from the constraint to the environment.
     - Substitute bindings from the constraint (abstract signature) for the
       other argument (_potentially_ a concrete signature, but not
       necessarily).
     - Unify rows.
     - Return the constraint with a populated row variable if successful.

   The signature constraint can be more _existentially_ specific than the
   supplied expression type (more variables, abstractions).

   The candidate might have more abstractions because signature matching and
   sealing might "forget" items.


 *)
and signature_match env sig_constraint candidate =
  (* Unwrap each Abs_FT.
       - Looking for matching _structure_, so different existential names are
         ok.
       - Existentials are "subtypes" of universals, but not the other way
         around, so the constraint can be Uni with the other arg Exi but not
         the reverse.  (TODO:  "subtype" here feels wrong, different way to
         describe).

     Return:
       - Environment populated with the constraint's abstraction variables.
       - Unwrapped constraint
       - Unwrapped candidate
       - Mapping from candidate to constraint's abstraction variables.

     var_memo is tuples mapping the argument's ("to match") abstraction
     variables to the constraint's variables.  It's used to rename variable
     references in the to-match arg before matching rows.
   *)
  let rec match_abstractions env sig_c cand var_memo=
    match sig_c, cand with
      | { n = Abs_FT (Exi _, _); pos = p1 }, { n = Abs_FT (Uni _, _); pos = p2 } ->
         raise (Sig_abstraction_fail (p1, p2))
      | { n = Abs_FT(a, con_body); pos }, { n = Abs_FT (b, arg_body); _ } ->
         (* TODO:  maybe kind check on a and b?  *)
         let env2 = Env.bind (Local (var_name a)) { n = TAbs_var a; pos } env in
         match_abstractions env2 con_body arg_body ((var_name b, a) :: var_memo)
    | ({ pos; _ } as remaining_constraint), ({ n = TSig _; _ } as base_arg) ->
       (* Collect the variables from the rest of the constraint:  *)
       let rec collect_abst memo = function
         | { n = Abs_FT (v, body); _ } ->
            collect_abst (v :: memo) body
         | { n = TSig _; _ } as base ->
            memo, base
         | _other ->
            (* TODO:  usable error.  *)
            failwith "Not matching signature at base case."
       in
       let rem_vars, base_constraint = collect_abst [] remaining_constraint in
       let env2 =
         List.fold_left
           (fun e v -> Env.bind (Local (var_name v)) { n = TAbs_var v; pos } e)
           env
           rem_vars
       in
       env2, base_constraint, base_arg, var_memo
    | ({ n = TSig _; _ } as base_constraint), { n = Abs_FT (_, body); _ } ->
       (* Discard remaining abstractions in the candidate since we don't need
          to substitute anything for them:

          FIXME:  remaining abstractions need to be abstractions for the row
                  variable.
        *)
       match_abstractions env base_constraint body var_memo
    | { pos = p1; _ }, { pos = p2; _ } ->
       raise (Not_signatures (p1, p2))
  in
  (*
    TODO:  for each member in the constraint, check if there is a
    structurally equivalent member in the to-match argument.
    "Structurally equivalent" for types is "type constructors have
    the same same kind", and for values is basically renaming
    types to match the constraint's abstraction variables.

    PROBLEM:  F-ing modules (expanded) talks about this only as
    substitutions.  Signature matching (depth-wise) is the search
    for types that can be substituted for the abstraction
    variables.  How far from { t : [=a : O] } is my current
    implementation below using (name, type) tuples?
   *)

  (* This is (at least at first) based on section 5.2 of [2], "F-ing
     Modules".  Basically, for each member of the signature that
     is the typing constraint:
     1. Make sure there is a member in the other signature with the same
     name.
     2. Try to substitute the "implementation" from the constraint for
     the implementation we're trying to match.  Fail if this is not
     possible.

     Constraint fields and to-check fields:
   *)
  let rec substitution var_map c_fs check_fs memo =
    match c_fs with
    | [] ->
       (List.rev check_fs) @ memo
    | (name, c_type) :: t ->
       (* Structurally equivalent?  Same arity of abstraction? *)
       let rec eq_check univ_map = function
         (* Exact same types mean substition is OK of course :D  *)
         | { n = a; _ }, { n = b; _ } when a = b->
            ()

         (* Can't introduce new existentials in type constructors so this
            only checks that both sides introduce universals.
          *)
         | { n = Abs_FT (Uni (v, KType), b1); _ }, { n = Abs_FT (Uni (k, KType), b2); _ } ->
            eq_check ((k, v) :: univ_map) (b1, b2)

         (* Type abstractions in the constraint and candidate must have the same
            arity.  This and the following pattern check both sides for arity
            match.
          *)
         | { n = Abs_FT (Uni (_, KType), _); _ } as a, ({ n = _; _ } as b)->
            raise (Invalid_substitution (a, b))
         | { n = _; _ } as a, ({ n = Abs_FT ((Uni _, _)); _ } as b) ->
            raise (Invalid_substitution (a, b))

         | { n = TSkol (vn, vs); _ }, { n = TSkol (kn, vs2); _ } ->
            (* Check that the constrained existential's name matches the
               right one from the constraint:
             *)
            let must_be_vn = List.assoc kn var_map in
            if (var_name must_be_vn) != vn then
              (* TODO:  real error.  *)
              failwith "Mismatched existentials."
            else
              begin
                (* Make sure the universals match.
                   FIXME:  /gross/ imperativeness.
                 *)
                let _ = List.map2
                          (fun a b -> if a != b then failwith "Mismatched universals" else ())
                          vs
                          vs2
                in
                ()
              end
         | { n = TNamed (Flat _vn); _ }, _ ->
            (* TODO:  make sure the above variable or type name is valid!  *)
            ()

         (* Abstract types that are skolemizations can be substituted for base
            types.

            FIXME:  there must be a nicer way, avoid itemizing every combination.
          *)
         | { n = TSkol _; _ }, { n = TBase _; _ } ->
            ()
         | a, b ->
            raise (Invalid_substitution (a, b))
       in
       (* Lookup `name` in check_fs *)
       let _ = eq_check [] (c_type, (List.assoc name check_fs)) in
       (* If appropriate, substitute, if not, error.  *)
       substitution var_map t (List.remove_assoc name check_fs) ((name, c_type) :: memo)
  in
  let env, base_constraint, base_candidate, var_map =
    match_abstractions env sig_constraint candidate []
  in
  let updated_candidate =
    match base_constraint, base_candidate with
    | { n = TSig { fields = cfs; var = Absent }; _ }, { n = TSig { fields = afs; var }; pos } ->
       { n = TSig { fields = substitution var_map cfs afs []; var }; pos }
    | _, { pos; _ } ->
       (* TODO:  useful error.  *)
       failwith ("Need rows to match signatures at " ^ ([%derive.show: pos] pos))
  in

  match base_constraint, updated_candidate with
  | { n = TSig c_row; pos = p1 }, { n = TSig e_row; pos = p2 } ->
     (* Update the environment with all variables as legitimate KType kinds
        before unification.
      *)
     unify_row env { n = c_row; pos = p1 } { n = e_row; pos = p2 }
  | { pos = p1; _ }, { pos = p2; _ } ->
     print_endline ([%derive.show: ftyp node] sig_constraint);
     raise (Invalid_row_match (p1, p2) )

and unify_row env lower_bound to_determine =
  (* Make sure a lower-bound row variable is empty, merge the remaining fields
     from a row that's trying to match the lower bound into a new "present" row
     variable when appropriate.
   *)
  let merge_row_vars lb_var remaining_fields remaining_var =
    match lb_var with
    (* TODO:  positioned error, should be unreachable.
              Also duplicating error reporting from below.
     *)
    | Present _ ->
       raise (Extended_row_constraint to_determine.pos)
    | Empty ->
       raise (Strict_row_size (List.map (fun (x, _) -> x) remaining_fields, to_determine.pos))
    | Absent ->
       begin
         match remaining_var with
         | Present { fields = xs; var } -> Present { fields = remaining_fields @ xs; var }
         | _ ->
            if List.length remaining_fields > 0 then
              Present { fields = remaining_fields; var = Absent }
            else
              Absent
       end
  in
  (* Field-wise checking and unification.  *)
  let rec ur lfs lvar tfs tvar memo =
    match lfs, tfs with
    | [], xs ->
       merge_row_vars lvar xs tvar
    | (k, v) :: t, xs ->
       begin
         match List.assoc_opt k xs with
         | None ->
            raise (Missing_row_field (to_determine.pos, k))
         | Some target_type ->
            let _ = unify env v target_type in
            ur t lvar (List.remove_assoc k xs) tvar ((k, v) :: memo)
       end
  in
  match lower_bound, to_determine with
  | { n = { fields = lfs; var = lvar }; _ }, { n = { fields = tfs; var = tvar }; _ } ->
     ur lfs lvar tfs tvar []

(* TODO:  do I actually want `kind_of` here, to match `type_of`?
          Why:  this is mostly making sure a type expression is actually valid.
          To do that, I'm expecting every type expression to reduce to "*".
 *)
and evaluate_type env t =
  match t with
  | { n = TInfer _; _ } -> t
  | { n = Abs_FT ((Uni (n, KType)) as abs_t, body); pos } ->
     let env2 = Env.bind (Local n) { n = TAbs_var abs_t; pos } env
                |> Env.bind_type (Local n) KType
     in
     let body2 = evaluate_type env2 body in
     { n = Abs_FT(abs_t, body2); pos }
  | { n = TBase _; _ } -> t
  | { n = TNamed Flat x; _ } -> evaluate_type env (Option.get (Env.local x env))
  | other ->
     failwith ("Can't evaluate this type expression:  " ^ ([%derive.show: ftyp node] other))
and validate_type _env t =
  match t with
  | { n = TBase _; _ } ->
     ()
  | { n = TInfer _; _ } ->
     ()
  | { n; _ } ->
     failwith ("Can't validate this type yet:  " ^ ([%derive.show: ftyp] n))
