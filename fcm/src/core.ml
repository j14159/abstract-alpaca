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
  | Wildcard
  | TE_Unit
  | TE_Int
  | TE_Bool
  | TE_Arrow of type_expr node * type_expr node
  | Var of string
  | Lab of label
  (* e.g. `type list 'x` *)
  | Constructor of type_constructor
  | Variants of (string node * type_expr node) list

type declaration =
  (* An abstract type declaration may not have an associated definition. *)
  | Type_bind of type_constructor * type_expr node option
  | Val_bind of label * type_expr node

and term =
  | Unit
  | Variant of label * term node
  | Fun of term node * term node

type expr =
  | Term of term node
  (* Allows for annotation with variants, not good:  *)
  | Ann_term of (term * type_expr) node
  | Type of type_expr node

(* Ensure a type expression is well constructed but does *not* check if it is
   well-kinded nor typed.  Maybe wasted effort in future?
 *)
let rec check_type_expr e =
  match e with
  | { n = Wildcard; _ } ->
     Result.ok ()
  | {n = TE_Unit; _ } | { n = TE_Int; _ } | { n = TE_Bool; _ } ->
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
  | { n = Constructor (_, args); _ } ->
     (* TODO:  check for dupe variables.  *)
     check_list args
  | { n = Variants xs; _ } ->
     let f prev (_, next) = Result.bind prev (fun _ -> check_type_expr next) in
     List.fold_left f (Result.ok ()) xs
and check_declaration d =
  match d with
  | { n = Type_bind ((_, c_args), te); _ } ->
     Result.bind
       (check_list c_args)
       (fun _ ->
         Option.map (fun te -> check_type_expr te) te
         |> Option.value ~default:(Result.ok ())
       )
  | { n = Val_bind (_, te); _ } ->
     check_type_expr te
and check_list xs =
  let f prev next = Result.bind prev (fun _ -> check_type_expr next) in
  List.fold_left f (Result.ok ()) xs
