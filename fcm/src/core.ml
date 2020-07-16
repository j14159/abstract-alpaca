(* Core syntax, not the elaboration.  *)

type pos = { uri : string; col : int; line : int }

let null_pos = { uri = "file://dev/null"; col = 0; line = 0 }

(* Allow for expression vs type expression nodes.
 *)
type 'n node = { n : 'n; pos : pos }

type label = string node

(* Starting with a label introduces a syntactic restriction to avoid
   higher-order kinds.
 *)
and type_constructor = label * type_expr node list

and type_expr =
  | TE_Unit
  | TE_Bool
  | TE_Arrow of type_expr node * type_expr node
  | Var of string
  | Lab of label
  (* e.g. `type list 'x` *)
  | TE_Apply of label * type_expr node list
  | TDot of type_expr node * label
  | Variants of (string node * type_expr node) list
  | Signature of decl list

(* Elements of a signature type declaration (a structure type to a module's
   structure expression).
 *)
and decl =
  | Opaque_type of type_constructor
  | Transparent_type of type_constructor * type_expr node
  | Val_bind of label * type_expr node

type term =
  | Unit
  | Label of label
  | Variant of label * term node
  | Fun of term node * term node
  (* Field access, could be for a module, signature, or record:  *)
  | Dot of term node * label
  | Mod of bind list
  | Pack of term node * term node

(* Elements of a module expression (structure literal/expression).  *)
and bind =
  | Type_decl of type_constructor * type_expr node
  | Let_bind of label * expr node

and expr =
  | Term of term node
  (* Allows for annotation with variants, not good:  *)
  | Ann_term of (term * type_expr) node
  | Type of type_expr node

(* Ensure a type expression is well constructed but does *not* check if it is
   well-kinded nor typed.  Maybe wasted effort in future?
 *)
let rec check_type_expr e =
  match e with
  | {n = TE_Unit; _ } | { n = TE_Bool; _ } ->
     Result.ok ()
  | { n = TE_Arrow ({n = Variants _; _ }, _); pos }
    | { n = TE_Arrow (_, {n = Variants _; _ }); pos } ->
     Result.error (pos, "Arrow type expressions cannot specify variants.")
  | { n = TE_Arrow (a, b); _ } ->
     Result.bind (check_type_expr a) (fun _ -> check_type_expr b)
  | { n = Var _; _ } ->
     Result.ok ()
  | { n = Lab _; _ } ->
     Result.ok ()
  | { n = TE_Apply (_, exprs); _ } ->
     check_list exprs
  | { n = Variants xs; _ } ->
     let f prev (_, next) = Result.bind prev (fun _ -> check_type_expr next) in
     List.fold_left f (Result.ok ()) xs
  | { n = TDot ({ n = Signature _; _ }, _); _ } | { n = TDot ({ n = Lab _; _ }, _); _ } ->
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
        | { n = Var _; _ } ->
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
  | Val_bind (_, te) ->
     check_type_expr te

(* Reusing in a few places to check a list of type constructor arguments.  *)
and check_list xs =
  let f prev next = Result.bind prev (fun _ -> check_type_expr next) in
  List.fold_left f (Result.ok ()) xs
