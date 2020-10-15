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
  | TInfer of infer_cell ref
  | TApp of ftyp node * ftyp node
  | TVar of var_name
  | TBase of base_typ
  | TNamed of ident
  | Abs_FT of var * ftyp node
  | Arrow_F of eff * ftyp node * ftyp node
  | TSmall of small_typ
  | TLarge of large_typ
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
     (* TODO:  generalization.  *)
     let f (env, memo) (name, next_decl) =
       let env2 = Env.enter_level env in
       let env3, typ = type_of env2 next_decl in
       let generalized = gen env3 typ in
       let env4 = Env.bind (Env.Local name) generalized env3 in
       (Env.leave_level env4, (name, generalized) :: memo)
     in
     let env2, rev_types = List.fold_left f (env, []) decls in
     env2, { n = TLarge (TSig { fields = List.rev rev_types; var = Absent }); pos }
  | { n = Structure_F { var = Absent; _ }; pos } ->
     raise (Unexpected_open_structure pos)
  | { n = Seal_F (expr, seal_with); pos } ->
     let env2, term_typ = type_of env expr in
     let _ = signature_match env seal_with term_typ in
     let { n; _ } = seal_with in
     env2, { n; pos }
  | { n = other; _ } ->
     failwith ("Can't type this yet:  " ^ ([%derive.show: fexp] other))

and unify _env _a _b =
  failwith "No unification implementation yet."

and signature_match env sig_constraint expr_type =
  (* Is this actually row matching?  (Shouldn't it be?)

     Signatures with open rows must only occur in functions/functors.
     *OR*, sealing explicitly drops the row variable.
     *)
  (* Order of operations:
       - Recursively match type abstractions (existentials).
       - Add existentials from the constraint to the environment.
       - Unify rows.

     The signature constraint can be more _existentially_ specific than the
     supplied expression type (more variables, abstractions).
   *)
  let match_abstractions _ _ =
    (* Unwrap each TAbs.  *)
    failwith "No abstraction matching yet."
  in
  let _vars, bare_sc, bare_et = match_abstractions sig_constraint expr_type in
  match bare_sc, bare_et with
  | { n = TLarge (TSig c_row); pos = p1 }, { n = TLarge (TSig e_row); pos = p2 } ->
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
         | None -> raise (Missing_row_field (to_determine.pos, k))
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
