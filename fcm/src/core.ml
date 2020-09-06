(* Core syntax, not the elaboration.  *)

type pos = { uri : string; col : int; line : int }
[@@deriving show]

let null_pos = { uri = "file://dev/null"; col = 0; line = 0 }

(* Allow for expression vs type expression nodes.
 *)
type 'n node = { n : 'n
               ; pos : pos
               }
[@@deriving show]

type label = string node
[@@deriving show]

(* Starting with a label introduces a syntactic restriction to avoid
   higher-order kinds.
 *)
and type_constructor = label * type_expr node list
[@@deriving show]

and type_expr =
  | TE_Unit
  | TE_Bool
  | TE_Arrow of type_expr node * type_expr node
  | TE_Var of string
  | Named of string
  (* e.g. applying `type list 'x` (a functor) in `list int`

     TODO:  dotted application.

   *)
  | TE_Apply of label * type_expr node list
  | TDot of type_expr node * label
  | Signature of decl list
[@@deriving show]

(* Elements of a signature type declaration (a structure type to a module's
   structure expression).
 *)
and decl =
  | Opaque_type of type_constructor
  | Transparent_type of type_constructor * type_expr node
  (* Variants on their own are not a valid type expression so they're treated
     separately here.
   *)
  | Transparent_variants of type_constructor * ((string node * type_expr node) list)
  (* TODO:  this doesn't admit type variables:  *)
  | Val_bind of label * type_expr node
[@@deriving show]

type term =
  | Unit
  | Label of string
  | Variant of label * term node
  | Fun of (expr * type_expr node option) * expr
  (* Field access, could be for a module, signature, or record:  *)
  | Dot of term node * label
  | Mod of bind list
  | Let of  { name : term node
            ; ret_typ : type_expr node
            ; body : term node
            }
[@@deriving show]

(* Elements of a module expression (structure literal/expression).  *)
and bind =
  | Type_decl of type_constructor * type_expr node
  | Variant_decl of type_constructor * ((string node * type_expr node) list)
  | Let_bind of label * expr node
[@@deriving show]

and expr =
  | Term of term node
  | Type of type_expr node
[@@deriving show]

(* Ensure a type expression is well constructed but does *not* check if it is
   well-kinded nor typed.  Maybe wasted effort in future?
 *)
let rec check_type_expr e =
  match e with
  | {n = TE_Unit; _ } | { n = TE_Bool; _ } ->
     Result.ok ()
  | { n = TE_Arrow (a, b); _ } ->
     Result.bind (check_type_expr a) (fun _ -> check_type_expr b)
  | { n = TE_Var _; _ } ->
     Result.ok ()
  | { n = Named _; _ } ->
     Result.ok ()
  | { n = TE_Apply (_, exprs); _ } ->
     check_list exprs
  | { n = TDot ({ n = Signature _; _ }, _); _ } | { n = TDot ({ n = Named _; _ }, _); _ } ->
     Result.ok ()
  | { n = TDot _; pos } ->
     Result.error (pos, "Field access type expressions only permitted on labels and signatures.")
  | { n = Signature ds; _ } ->
     List.fold_left
       (fun prev next -> Result.bind prev (fun _ -> check_sig_declaration next))
       (Result.ok ())
       ds

and check_sig_declaration d =
  let check_for_vars prev next =
    Result.bind
      prev
      (fun _ ->
        match next with
        | { n = TE_Var _; _ } ->
           Result.ok ()
        | { pos; _ } ->
           Result.error (pos, "Only variables allowed in an opaque type.")
      )
  in
  match d with
  (* An opaque type should have a name and variables, nothing more.  *)
  | Opaque_type (_, c_args) ->
     List.fold_left check_for_vars (Result.ok ()) c_args
  | Transparent_type ((_, c_args), te) ->
     Result.bind
       (List.fold_left check_for_vars (Result.ok ()) c_args)
       (fun _ -> check_type_expr te)
  | Transparent_variants ((_, c_args), xs) ->
     let var_check = List.fold_left check_for_vars (Result.ok ()) c_args in
     let f prev (_, next) = Result.bind prev (fun _ -> check_type_expr next) in
     List.fold_left f var_check xs
  | Val_bind (_, te) ->
     check_type_expr te

(* Reusing in a few places to check a list of type constructor arguments.  *)
and check_list xs =
  let f prev next = Result.bind prev (fun _ -> check_type_expr next) in
  List.fold_left f (Result.ok ()) xs

let label txt pos =
  { n = txt; pos }
let te_arrow a b pos =
  { n = TE_Arrow (a, b); pos }
let te_bool pos =
  { n = TE_Bool; pos }
let te_unit pos =
  { n = TE_Unit; pos }

let te_sig decls pos =
  { n = Signature decls; pos }

let type_const l xs =
  (l, xs)
let type_apply l args pos =
  { n = TE_Apply (l, args); pos }
