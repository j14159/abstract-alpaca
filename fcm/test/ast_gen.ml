(* Generation of AST fragments.
 *)
open QCheck

(* For formatting output.
   TODO:  probably should be using some of the stuff from stdlib using boxes,
   etc.
 *)
let width = 80

let first_valid =
  Gen.oneof [Gen.char_range 'A' 'Z'; Gen.char_range 'a' 'z']

let rem_valid =
  Gen.small_list (Gen.oneof  [first_valid; Gen.numeral])

(* The included base/primitive types.  *)
let base_type =
  let open Fcm.Core in
  [TE_Unit; TE_Bool]

let label =
  let chars = Gen.pair first_valid rem_valid in
  Gen.map (fun (a, b) -> Core.String.of_char_list (a :: b)) chars

let var_gen =
  Gen.map (fun l -> Fcm.Core.Var ("'" ^ l) ) label

(* Generate a label, e.g. a function name or type constructor name, followed
   by a list of nodes like type variables, types, etc.
 *)
let gen_label_and_nodes node_gen =
  let open Fcm.Core in
  let f (name, nodes) =
    let label = { n = name; pos = null_pos } in
    let init_offset = (String.length name) + 1 in
    (* TODO:  This is trying to be cute about positions and getting it wrong.

       Does not account for multiline returns from formatting, nor line numbers
       at all.
     *)
    let _, nodes' = List.fold_right
                      (fun t_expr (offset, vs) ->
                        let node = Type { n = t_expr; pos = null_pos} in
                        let len = String.length (snd @@ Fcm.Format.format node width) in
                        len + offset + 1, (* +1 for whitespace *)
                        { n = t_expr
                        ; pos = { null_pos with col = offset }
                        } :: vs
                      )
                      nodes
                      (init_offset, [])
    in
    label, nodes'
  in
  Gen.map f (Gen.pair label node_gen)

(* TODO:  how to feed in known types?

   This could take input from a signature's preceding declarations or
   environment.
 *)
let type_apply_gen =
  (* Not quite correct, could have access to more types from the preceding
     definitions or import/open statements.
   *)
  let arg_list = Gen.small_list (Gen.oneof [var_gen; Gen.oneofl base_type]) in
  let open Fcm.Core in
  Gen.map (fun (name, args) -> TE_Apply (name, args)) (gen_label_and_nodes arg_list)

(* TODO:
   - Transparent gen.  Feed vars into definition.
   - Variant gen.
 *)
let type_decl_gen available_types =
  let open Fcm.Core in
  let open Gen in
  (* TODO:  generator based on in-scope generated types.  *)
  let available_gen = oneofl (available_types @ base_type) in
  let arg_list = small_list var_gen in
  let opaque_gen =
    map (fun (name, args) -> Opaque_type (name, args)) (gen_label_and_nodes arg_list)
  in
  let variant_gen vars =
    (* TODO:  variants that take unit stand in for nullary variants here but
              I'm not sure that's good enough.
     *)
    let available_type_nodes = map (fun x -> { n = x; pos = null_pos }) available_gen in
    let arg = if (List.length vars > 0) then
                oneof [oneofl vars; available_type_nodes]
              else
                available_type_nodes
    in
    (* TODO:  real positions?  *)
    let variant =
      map
        (fun (l, t) -> ({ n = l; pos = null_pos }, t))
        (pair label arg)
    in
    small_list variant
  in
  (* TODO:  use in-scope types, not just variants and base types.  *)
  let transparent_gen =
    (* Re-use arg_list to synthesize a list of type variables.  *)
    (gen_label_and_nodes arg_list)
    >>=
      (fun (name, args) ->
      map
        (fun vs -> Transparent_variants ((name, args), vs))
        (variant_gen args))
  in
  oneof [opaque_gen; transparent_gen]

let sig_gen =
  let open Fcm.Core in
  (* TODO:  real position, and type declarations should have correct positions
     relative to each other.
   *)
  (* Roughly:
       - Small int for number of types.
       - List.init to allocate.
       - fold_left, using previously defined types as inputs to type_apply_gen
   *)
  Gen.map
    (fun ds -> Type ({ n = Signature ds; pos = null_pos }))
    (Gen.small_list (type_decl_gen []))
