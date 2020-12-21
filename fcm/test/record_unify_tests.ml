open OUnit2
open Fcm.Core
open Fcm.Typing

open Ast.F_ast

let lit_row ~pos fields = { n = { fields; var = Absent }; pos }
let np_lit_row = lit_row ~pos:null_pos

let suite =
  "Basic record unification tests" >:::
    ["Empty records" >::
       (fun _ ->
         let expr = np_lit_row [] in
         let bound = np_lit_row [] in
         let res = unify_row (Fcm.Env.make ()) bound expr in
         let expected = Absent in
         assert_equal expected res ~printer:([%derive.show: ftyp node row_var])
       )
    ; "Single-field record and empty bound." >::
        (fun _ ->
          (* Checking that the "extra" field in `expr` gets included in the row
             variable returned by `unify_row`.

             This stands in for a test covering something like:

                 let row_identity (r : {}) = r in
                 row_identity { x = true }
           *)
          let member = ("x", tbase TBool) in
          let expr = np_lit_row [member] in
          let bound = np_lit_row [] in
          let res = unify_row (Fcm.Env.make ()) bound expr in
          let expected = Present ([], { fields = [member]; var = Absent }) in
          assert_equal expected res ~printer:([%derive.show: ftyp node row_var])
        )
    ; "Exact match single field" >::
        (fun _ ->
          (*
            Checking something that fits inside:

                let get_x { x } = x in
                get_x { x = 1 }
           *)

          let member = ("x", tbase TBool) in
          let expr = np_lit_row [member] in
          let bound = np_lit_row [member] in
          let res = unify_row (Fcm.Env.make ()) bound expr in
          let expected = Absent in
          assert_equal expected res ~printer:([%derive.show: ftyp node row_var])
        )
    ; "Fail on bound larger than expression" >::
        (fun _ ->
          (* Something like this should fail:

                 let get_x { x } = x in
                 get_x { y = true, z = false }
           *)
          let bound = np_lit_row [("x", tbase TBool)] in
          let expr = np_lit_row [ ("y", tbase TBool)
                                ; ("z", tbase TBool) ]
          in
          assert_raises
            (Missing_row_field (null_pos, "x"))
            (fun _ -> unify_row (Fcm.Env.make ()) bound expr)
        )
    ]

let _ =
  run_test_tt_main suite
