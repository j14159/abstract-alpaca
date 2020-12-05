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
(* "Empty" means "someone specifically wants this limited".
   Otherwise there's an optionally quanitified row in the variable.
 *)
and 'a row_var =
  | Absent
  | Empty
  | Present of var list * 'a row
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
  (* Problem:  this is a weak syntactic distinction from structures (modules).
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
  (* Records and signatures type to rows.  There's a semantic difference in that
     records must not contain types, that needs a syntactic restriction I think?
     Aside from this, the exact same operations should be permitted for both
     types of values (extension, copying, limiting, etc).
   *)
  | TRow of ftyp node row
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


type substitution_error =
  | Missing_member of row_label * pos
  | Mismatched_abstractions of var_name * var_name * pos
  (** Raised during signature matching when an item from the constraint can't
    substitute for one in the candidate.  An example of this when sealing:

        {[ { type t 'a } :> { type t } ]}

    In the above example, the constraint's [t] is not structurally equivalent to
    the candidate's [t] since their arities differ.
   *)
  | Invalid_substitution_arity of ftyp node * ftyp node
  | Invalid_substitution of ftyp node * ftyp node
  (* TODO:  should just be mismatched abstractions I think.  *)
  | Mismatched_universals of ftyp node * ftyp node
[@@deriving show]

type typing_error =
  (* TODO:  this should probably take position and label?  *)
  | Binding_not_found of ftyp node
  (* Raised when an abstraction variable (universal or existential) does not have
     the kind [KType].

     TODO:  kinding errors separately.
   *)
  | Bad_abstraction_kind of pos
  (* Raised when a KArrow turns up where it shouldn't.

     TODO:  This is a terrible description, and probably a hard-to-use error.
   *)
  | Bad_higher_kind of ftyp node * kind

  | Signature_match_error of substitution_error
   (** Modules (structures) are typed as rows that are not extensible.

       More specifically:  an open (extensible) row can only be used as an argument
       to a function (functor).  This exception is thrown if an "open" module makes
       it to the typer.
    *)
   | Unexpected_open_structure of pos
[@@deriving show]

let invalid_substitution a b = Signature_match_error (Invalid_substitution (a, b))
let missing_member name pos = Signature_match_error (Missing_member (name, pos))
let invalid_substitution_arity a b = Signature_match_error (Invalid_substitution_arity (a, b))
let mismatched_abstractions a b pos = Signature_match_error (Mismatched_abstractions (a, b, pos))
let mismatched_universals a b = Signature_match_error (Mismatched_universals (a, b))

type ('a, 'b) error_tracer =
  ('a, 'b) Env.t ->
  typing_error ->
  ((('a, 'b) Env.t * ftyp node), typing_error) Result.t
type ('a, 'b) success_tracer =
  ('a, 'b) Env.t ->
  ftyp node ->
  ((('a, 'b) Env.t * ftyp node), typing_error) Result.t

let new_var env =
  let v, env2 = Env.next_var env in
  env2, TInfer (ref (Unbound (v, Env.level env2)))

(* TODO:  should generalization actually add universal abstractions?  *)
let rec gen env = function
  | { n = TInfer { contents = Unbound (name, lvl) }; pos } when lvl > Env.level env ->
     [name], { n = TVar name; pos }
  | { n = Arrow_F (eff, a, b); pos } ->
     (* Collect variable names for abstraction later:  *)
     let vs1, ga = gen env a in
     let vs2, gb = gen env b in
     (vs1 @ vs2), { n = Arrow_F (eff, ga, gb); pos }
  | t -> [], t

(** Makes sure that k is KType, not a KArrow.  *)
let constrain_kind k ret =
  Result.bind
    k
    (function
     | KType -> Result.ok ret
     | arrow -> Result.error (Bad_higher_kind (ret, arrow))
    )

let default_trace x = x

(* TODO:  it would be maybe very interesting to optionally inject a trace ID
          here that could be used for optional logging of typing decisions.
          "Logging" could be replaced with "instrumentation", "output",
          "streaming", etc.

          Maybe this can wrap `Result`?
 *)
let rec type_of ?trace:(trace = default_trace) env e =
  match e with
  | { n = Typ_F t; pos } ->
     kind_of env { n = t; pos }
     |> Result.map (fun _ -> (env, { n = t; pos}))
     |> trace
  | { n = Unit_F; pos } ->
     trace @@ Result.ok (env, { n = TBase TUnit; pos })
  | { n = Bool_F _; pos } ->
     trace @@ Result.ok (env, { n = TBase TBool; pos })
  | { n = Ident_F (Flat name); _ } ->
     trace @@ Result.ok (env, Option.get (Env.local name env))
  | { n = Lam_F { arg = { n = Ident_F (Flat a); _ }; arg_typ; body }; pos } ->
     let _ = constrain_kind (kind_of env arg_typ) arg_typ in
     let env2 = Env.bind (Local a) arg_typ env in
     trace @@ type_of env2 body
     |> Result.map
          (fun (env3, tb) -> (env3, { n = Arrow_F (Impure, arg_typ, tb); pos }))
     |> trace

  (* Only variables marked as "empty" can be typed for structures since as
     an expression, they're always literal and never a pattern or type.

     TODO:  module patterns in functors instead of `var : type`?  If this were
            permitted then the row variable would need to allow `Absent` as
            well.
   *)
  | { n = Structure_F ({ fields = decls; var = Empty }); pos } ->
     let f acc (name, next_decl) =
       Result.bind
         acc
         (fun (env, memo) ->
           let env2 = Env.enter_level env in
           trace @@ type_of env2 next_decl
           |> Result.map (fun (env3, typ) ->
                  let to_abstract, generalized = gen env3 typ in
                  (* TODO:  efficiency, or just find something off-the-shelf.
                     Maybe Batteries or Janestreet Core?
                   *)
                  let rec dedupe = function
                    | [] -> []
                    | [x] -> [x]
                    | x :: (y :: tl) ->
                       if x = y then x :: (dedupe tl)
                       else x :: y :: (dedupe tl)
                  in
                  let abs = List.sort String.compare to_abstract
                            |> dedupe
                  in
                  let abs_gen =
                    List.fold_right
                      (fun n acc -> { n = Abs_FT (Uni (n, KType), acc); pos = generalized.pos })
                      abs
                      generalized
                  in
                  let env4 = Env.bind (Env.Local name) abs_gen env3 in
                  (Env.leave_level env4, (name, abs_gen) :: memo)
                )
         )
     in
     List.fold_left f (Result.ok (env, [])) decls
     |> Result.map
          (fun (env2, rev_types) ->
            let typ = { n = TRow { fields = List.rev rev_types; var = Absent }; pos } in
            (* TODO:  I'd love to optionally log typing decisions somewhere.  *)
            env2, typ
          )
     |> trace
  | { n = Structure_F { var = Absent; _ }; pos } ->
     trace @@ Result.error (Unexpected_open_structure pos)
  | { n = Seal_F (expr, seal_with); pos } ->
     let match_pass (env2, term_typ) =
       signature_match env2 seal_with term_typ
       |> Result.map
            (* Discard the row variable because we're sealing:  *)
            ( fun _ ->
              let { n; _ } = seal_with in
              env2, { n; pos }
            )
       |> trace
     in
     trace @@ Result.bind (type_of env expr) match_pass

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

   There are three functions contained inside of this:
   {ol {- [match_abstractions] which checks that the existentials surrounding
          the two signatures match each other.}
       {- [eq_check] which is used for checking that members with the same name
          between the two signatures are structurally equivalent.  This is
          basically depth-matching.}
       {- [substitution] which attempts to lookup names in the candidate taken
          from the constraint, which are then submitted to [eq_check].  This is
          width-matching.}
   }
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
  let rec match_abstractions env sig_c cand var_memo row_abs =
    match sig_c, cand with
    | { n = Abs_FT (Exi _, _); pos = p1 }, { n = Abs_FT (Uni _, _); pos = p2 } ->
       (* TODO:  Result.t  *)
       raise (Sig_abstraction_fail (p1, p2))
    | { n = Abs_FT(a, con_body); pos }, { n = Abs_FT (b, arg_body); _ } ->
       (* TODO:  maybe kind check on a and b?  *)
       let env2 = Env.bind (Local (var_name a)) { n = TAbs_var a; pos } env in
       match_abstractions env2 con_body arg_body ((var_name b, a) :: var_memo) row_abs
    | ({ pos; _ } as remaining_constraint), ({ n = TRow _; _ } as base_arg) ->
       (* Collect the variables from the rest of the constraint:  *)
       let rec collect_abst memo = function
         | { n = Abs_FT (v, body); _ } ->
            collect_abst (v :: memo) body
         | { n = TRow _; _ } as base ->
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
       env2, base_constraint, base_arg, var_memo, row_abs
    | ({ n = TRow _; _ } as base_constraint), { n = Abs_FT (v, body); _ } ->
       (* Keep the remaining abstraction(s) from the candidate to later add to
          the row variable:
        *)
       match_abstractions env base_constraint body var_memo (v :: row_abs)
    | { pos = p1; _ }, { pos = p2; _ } ->
       raise (Not_signatures (p1, p2))
  in
  let rec eq_check univ_map var_map a b =
    match a, b with
    (* Exact same types mean substition is OK of course :D  *)
    | { n = a; _ }, { n = b; _ } when a = b->
       Result.ok ()
    (* Can't introduce new existentials in type constructors so this
       only checks that both sides introduce universals.
     *)
    | { n = Abs_FT (Uni (v, KType), b1); _ }, { n = Abs_FT (Uni (k, KType), b2); _ } ->
       eq_check ((k, v) :: univ_map) var_map b1 b2

    | { n = TSkol (vn, vs); _ } as a, ({ n = TSkol (kn, vs2); pos } as b) ->
       (* Check that the constrained existential's name matches the
          right one from the constraint:
        *)
       let must_be_vn = List.assoc kn var_map in
       if (var_name must_be_vn) != vn then
         (* TODO:  real error.  *)
         Result.error (mismatched_abstractions vn (var_name must_be_vn) pos)
       else
         begin
           if List.length vs != List.length vs then
             Result.error (invalid_substitution_arity a b)
           else
             (* Make sure the universals match.  *)
             List.fold_left2
               (fun c a b ->
                 Result.bind
                   c
                   (fun _ ->
                     if a != b then Result.error (mismatched_universals a b)
                     else (Result.ok ())
                   )
               )
               (Result.ok ())
               vs
               vs2

         end
    | { n = TNamed (Flat _vn); _ }, _ ->
       (* TODO:  make sure the above variable or type name is valid!  *)
       Result.ok ()

    (* Abstract types that are skolemizations can be substituted for base
       types.  Sort of allowing the sealing of something using a phantom
       type.

       FIXME:  there must be a nicer way, avoid itemizing every combination.
     *)
    | { n = TSkol _; _ }, { n = TBase _; _ } ->
       Result.ok ()

    (* A polymorphic function in the candidate (one with universal abstractions)
       can be restricted by the constraint.
     *)
    | { n = Arrow_F _; _ } as a, { n = Abs_FT ((Uni (_vn, KType), b)); _ } ->
       (* TODO:  should the universal go into the map?  *)
       eq_check univ_map var_map a b
    | ({ n = Arrow_F (Pure, _, _); _ } as a), ({ n = Arrow_F (Impure, _, _ ); _ } as b) ->
       Result.error (invalid_substitution a b)
    | { n = Arrow_F (_, arg1, body1); _ }, { n = Arrow_F (_, arg2, body2); _ } ->
       let arg_ok = eq_check univ_map var_map arg1 arg2 in
       Result.bind arg_ok (fun _ -> eq_check univ_map var_map body1 body2)

    (* Type abstractions in the constraint and candidate must have the same
       arity.  This and the following pattern check both sides for arity
       match.
     *)
    | { n = Abs_FT (Uni (_, KType), _); _ } as a, ({ n = _; _ } as b) ->
       Result.error (invalid_substitution_arity a b)
    | { n = _; _ } as a,  ({ n = Abs_FT (Uni (_, KType), _); _ } as b) ->
       Result.error (invalid_substitution_arity a b)

    | a, b ->
       Result.error (invalid_substitution a b)
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
       Result.ok ((List.rev check_fs) @ memo)
    | (name, c_type) :: t ->
       (* Structurally equivalent?  Same arity of abstraction? *)
       (* Lookup `name` in check_fs
          TODO:  thread this result through.
        *)
       let lookup = List.assoc_opt name check_fs
                    |> Option.map
                         (fun candidate_field -> eq_check [] var_map c_type candidate_field)
                    |> Option.value ~default:(Result.error (missing_member name candidate.pos))
       in
       (* If appropriate, substitute, if not, error.  *)
       Result.bind lookup
            (fun _ ->
              substitution var_map t (List.remove_assoc name check_fs) ((name, c_type) :: memo)
            )
  in
  (* First make sure that both the constraint and candidate are valid signatures
     and have kind KType.  `kind_of` is doing double-duty here underneath
     TODO:  wrap the rest in results.
   *)
  let k_sig = kind_of env sig_constraint in
  let k_can = kind_of env candidate in
  (* TODO:  naming, structure *)
  Result.bind k_can (fun c -> Result.map (fun s -> s, c) k_sig)
  |> Result.map
       (function
        | (KType, KType) as k -> Result.ok k
        | KType, x -> Result.error (Bad_higher_kind (candidate, x))
        | x, _ -> Result.error (Bad_higher_kind (sig_constraint, x))
       )
  |> Result.join
  |> Result.map
       (fun _ ->
         (* rev_row_abstractions is the reverse-order unmatched *candidate*
            abstractions.  They need to be attached to the returned row variable after
            row unification.
          *)
         let env, base_constraint, base_candidate, var_map, rev_row_abstractions =
           match_abstractions env sig_constraint candidate [] []
         in
         match base_constraint, base_candidate with
         | { n = TRow ({ fields = cfs; var = Absent } as con_row); pos = p1 }, { n = TRow { fields = afs; var }; pos = p2 } ->
            substitution var_map cfs afs []
            |> Result.map
                 (fun fields ->
                   let cand_row = { fields; var } in
                   let v = unify_row env { n = con_row; pos = p1 } { n = cand_row; pos = p2 } in
                   let with_abs = match v with
                     | Present (existing, row) ->
                        Present (List.rev rev_row_abstractions @ existing, row)
                     | other ->
                        other
                   in
                   { n = TRow ({ con_row with var = with_abs }); pos = p1 }
                 )
         | _, { pos; _ } ->
            (* TODO:  useful error.  *)
            failwith ("Need rows to match signatures at " ^ ([%derive.show: pos] pos))
       )
  |> Result.join

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
         | Present (vs, { fields = xs; var }) ->
            Present (vs, { fields = remaining_fields @ xs; var })
         | _ ->
            if List.length remaining_fields > 0 then
              Present ([], { fields = remaining_fields; var = Absent })
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

(* TODO:  return Result.t  *)
and kind_of env t =
  match t with
  | { n = TInfer _; _ } ->
     Result.ok KType
  | { n = TVar v; _ } ->
     begin
       match Env.local_type v env with
       | Some x -> Result.ok x
       | None -> Result.error (Binding_not_found t)
     end
  | { n = Arrow_F (_, a, b); _ } ->
     let check_result = function
       | (KType, KType) -> Result.ok KType
       | KType, x -> Result.error (Bad_higher_kind (b, x))
       | x, _ -> Result.error (Bad_higher_kind (a, x))
     in

     (* Fetch the kinds of `a` and `b`, then make sure they're both KType.  *)
     Result.bind (kind_of env a) (fun a -> Result.map (fun b -> a, b) (kind_of env b))
     |> Result.map check_result
     |> Result.join

  | { n = Abs_FT (v, body); pos } ->
     if var_kind v != KType then
       Result.error (Bad_abstraction_kind pos)
     else
       let binding_name = Env.Local (var_name v) in
       let env2 = Env.bind binding_name { n = TAbs_var v; pos } env
                  |> Env.bind_type binding_name KType
       in
       kind_of env2 body
       |> Result.map
            (fun body_kind ->
              match v with
              | Exi _ -> body_kind
              | Uni _ -> KArrow (KType, body_kind)
            )
  | { n = TAbs_var v; _ } -> Result.ok (var_kind v)
  | { n = TBase _; _ } -> Result.ok KType
  | { n = TNamed Flat x; _ } ->
     let res = Env.local x env
               |> Option.to_result ~none:()
               |> Result.map_error (fun _ -> Binding_not_found t)
     in
     (* TODO:  naming *)
     Result.bind res (fun res -> kind_of env res)

  | { n = TRow { fields; var = Absent }; _ } ->
     (* TODO:  handle the row variable.  *)
     List.fold_left
       (fun e next ->
         Result.bind
           e
           (fun e ->
             let (name, not_abs) = next in
             kind_of e not_abs
             |> Result.map (fun res -> Env.bind_type (Local name) res e)
           )
       )
       (Result.ok env)
       fields
     |> Result.map (fun _ -> KType)
  | { n = TSkol (exi_v, other_vs); pos } ->
     let none = Binding_not_found { n = TVar exi_v; pos } in
     let k_exi = Env.local_type exi_v env
                 |> Option.to_result ~none
     in
     (* Kind arrows (higher kinds) are treated as arrows in the compound types
        resulting from "skolemization".
      *)
     let fold_f acc next =
       Result.bind
           acc
           (fun prev_result ->
             let k_next = kind_of env next in
             Result.bind
               k_next
               (function
                | KType -> Result.ok prev_result
                | (KArrow _ ) as a -> Result.error (Bad_higher_kind (t, a))
               )
           )
     in
     List.fold_left fold_f k_exi other_vs

  | other ->
     failwith ("Can't evaluate this type expression:  " ^ ([%derive.show: ftyp node] other))

