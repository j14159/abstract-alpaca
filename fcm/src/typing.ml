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

