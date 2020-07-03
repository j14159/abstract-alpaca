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
  Gen.oneofl [TE_Unit; TE_Int; TE_Bool]

(* TODO:  make "syntactically valid" variables with a leading apostrophe.  This
   will be necessary for formatter/parser tests.
 *)
let label =
  let chars = Gen.pair first_valid rem_valid in
  Gen.map (fun (a, b) -> Core.String.of_char_list (a :: b)) chars

let var_gen = Gen.map (fun l -> Fcm.Core.Var ("'" ^ l) ) label

let constructor_gen =
  (* Not quite correct, could have access to more types from the preceding
     definitions or import/open statements.
   *)
  let constructor_arg_list = Gen.small_list (Gen.oneof [var_gen; base_type]) in

  let open Fcm.Core in
  let arg_gen init_offset xs =
    snd @@ List.fold_right
             (fun t_expr (offset, vs) ->
               let len = String.length (snd @@ Fcm.Format.format (Type { n = t_expr; pos = null_pos}) width) in
               len + offset + 1, (* +1 for whitespace *)
               { n = t_expr
               ; pos = { null_pos with col = offset }
               } :: vs
             )
             xs
             (init_offset, [])
  in

  let xs = Gen.pair label constructor_arg_list in
  Gen.map (fun (cname, args) ->
      Type { n = Constructor
                   ( { n = cname
                     ; pos = null_pos
                     }
                   , arg_gen ((String.length cname) + 1) args
                   )
           ; pos = null_pos
    })
    xs

