(* Generation of labels, need to expand to full unicode for later experiments.
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

let base_type =
  let open Fcm.Core in
  Gen.oneofl [TE_Unit; TE_Bool]

(* TODO:  make "syntactically valid" variables with a leading apostrophe.  This
   will be necessary for formatter/parser tests.
 *)
let label =
  let chars = Gen.pair first_valid rem_valid in
  Gen.map (fun (a, b) -> Core.String.of_char_list (a :: b)) chars

let var_gen = Gen.map (fun l -> Fcm.Core.Var ("'" ^ l) ) label

let gen_label_and_nodes node_gen =
  let open Fcm.Core in
  let f (name, nodes) =
    let label = { n = name; pos = null_pos } in
    let init_offset = (String.length name) + 1 in
    let nodes' = snd @@ List.fold_right
             (fun t_expr (offset, vs) ->
               let len = String.length (snd @@ Fcm.Format.format (Type { n = t_expr; pos = null_pos}) width) in
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
  let arg_list = Gen.small_list (Gen.oneof [var_gen; base_type]) in
  let open Fcm.Core in
  Gen.map (fun (name, args) -> TE_Apply (name, args)) (gen_label_and_nodes arg_list)

let type_decl_gen =
  let arg_list = Gen.small_list var_gen in
  let open Fcm.Core in
  Gen.map (fun (name, args) -> Opaque_type (name, args)) (gen_label_and_nodes arg_list)

let sig_gen =
  let open Fcm.Core in
  (* TODO:  real position, and type declarations should have correct positions
     relative to each other.
   *)
  Gen.map (fun ds -> Type ({ n = Signature ds; pos = null_pos })) (Gen.small_list type_decl_gen)
