open OUnit2
open Fcm.Core
open Fcm.Render

let null_pos = { uri = "/dev/null"; col = 0; line = 0 }

let assert_str_eq = assert_equal ~printer:(fun x -> "\n" ^ x)

let test_type_apply _ =
  let e = Type { n = TE_Apply ( { n = "test_type"; pos = null_pos}
                              , [{n = TE_Unit; pos = null_pos}])
               ; pos = null_pos
            }
  in
  assert_str_eq "test_type unit" (render e);
  assert_str_eq "test_type\n  unit" (render ~width:5 e)
  
let test_nested_type_apply _ =
  let e = Type { n = TE_Apply ( { n = "arity2"; pos = null_pos }
                              , [ { n = TE_Apply ( { n = "test_type"; pos = null_pos}
                                                 , [{n = TE_Unit; pos = null_pos}])
                                  ; pos = null_pos
                                  }
                                ; { n = TE_Unit; pos = null_pos }
                                ]
                       )
                              
               ; pos = null_pos
            }
  in
  assert_str_eq "arity2 (test_type unit) unit" (render e);
  assert_str_eq "arity2\n  ( test_type\n    unit\n  )\n  unit" (render ~width:5 e);
  assert_str_eq "arity2\n  (test_type unit)\n  unit" (render ~width:20 e)

let test_sig_with_opaque_type _ =
  let e = Type
            { n = Signature
                    [Opaque_type ( { n = "t"; pos = null_pos }
                                 , [{ n = Var "'a"; pos = null_pos }])
                    ]
            ; pos = null_pos
            }
  in
  assert_str_eq "{ type t 'a }" (render e);
  assert_str_eq "" (render ~width:4 e)

let suite =
  "AST rendering suite" >:::
    [ "Type application" >:: test_type_apply
    ; "Nested type application." >:: test_nested_type_apply
    ; "Signature with one opaque type" >:: test_sig_with_opaque_type
    ]

let _ =
  run_test_tt_main suite
