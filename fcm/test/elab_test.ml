open Fcm.Core
open Fcm.Typing

open OUnit2

let test_simple_sig_elab =
  [ "Empty sig" >::
      (fun _ ->
        let s1 = { n = Signature []; pos = null_pos } in
        let res1_vars, _res1_type, _env = elab_type_expr (Fcm.Env.make ()) s1 in
        assert_equal [] res1_vars
      )
  ; "Single abstract type" >::
      (fun _ ->
        let t = Opaque_type ({ n = "t"; pos = null_pos }, []) in
        let s = { n = Signature [t]; pos = null_pos } in
        let vars, typ, _env = elab_type_expr (Fcm.Env.make ()) s in
        assert_equal ["t", "v_0"] vars;
        assert_equal
          (TLarge (TAbs ( Exi ("v_0", KType)
                        , TSig
                            (Open
                               { fields = [("t", TLarge (TTyp "v_0"))]
                               ; var = None
                               }
                     ))
             )
          )
          typ
          ~printer:[%derive.show: Fcm.Typing.typ]
      )
  ; "Two abstract types, one elaborates to a function." >::
      (fun _ ->
        (* { type t
             type u 'v
           }

           Should elaborate to:

           abs[v_0].abs[v_1].{ t : [=v_0]; u : 'v -> [=v_1] }

           TODO:  since type definitions are pure (applicative) functors,
                  should `u1 _actually_ elaborate to the following?
                  
                  u : 'v -> [='v.v_1]  -- skolemize?
         *)
        (* Reusing from the previous test:  *)
        let t = Opaque_type ({ n = "t"; pos = null_pos }, []) in
        (* This should elaborate to exi[v_1].type -> type *)
        let u = Opaque_type
                  ( { n = "u"; pos = null_pos }
                  , [{n = Var "v"; pos = null_pos }]
                  )
        in
        let s = { n = Signature [t; u]; pos = null_pos } in
        let vars, typ, _ = elab_type_expr (Fcm.Env.make ()) s in
        assert_equal
          ([("t", "v_0"); ("u", "v_1")])
          vars
          ~printer:[%derive.show: (string * string) list];

        assert_equal
          (TLarge
             (TAbs ( Exi ("v_0", KType)
                   , TAbs ( Exi ("v_1", KType)
                          , TSig
                              (Open
                                 { fields = [ ("t", TLarge (TTyp "v_0"))
                                            ; ("u"
                                              ,  TLarge
                                                   (TL_arrow ( Pure
                                                             , TSmol (TVar "v")
                                                             , (TTyp "v_1")))
                                              )
                                            ]
                                 ; var = None
                                 }
                              )
                       )
                )
             )
          )
          typ
          ~printer:[%derive.show: Fcm.Typing.typ]
      )
  ]

let null_node x = { n = x; pos = null_pos }

let test_functor _ =
  (* { type t } -> { val f : t -> t }
     
     Should elaborate to:
       exi[X].{ t : [=X]} -> exi[X].{ f : [=X] -> [=X\ }
   *)
  let arg = { n = Signature [Opaque_type ({ n = "t"; pos = null_pos }, [])]
            ; pos = null_pos
            }
  in
  let t_node = null_node "t" in
  let arrow_arg = { n = TE_Apply (t_node, []); pos = null_pos } in
  let body = { n = Signature
                     [Val_bind
                        ( { n = "f"; pos = null_pos }
                        , null_node
                            (TE_Arrow (arrow_arg, arrow_arg))
                        )
                     ]
             ; pos = null_pos
             }
  in
  let f = TE_Arrow (arg, body) in
  let d1 = Val_bind ({ n = "f"; pos = null_pos }, { n = f; pos = null_pos }) in
  let vs, res, _ = elab_type_expr (Fcm.Env.make ()) { n = Signature [d1]; pos = null_pos } in
  let expected_vs = ["t", "v_0"] in
  assert_equal expected_vs vs;

  let sig1 = TSig (Open { var = None; fields = [("t", TLarge (TTyp "v_0"))] }) in
  let sig2 = TSig (Open { var = None; fields = [("f", TLarge (TL_arrow (Impure, TTyp "v_0", TTyp "v_0")))] }) in
  let expected_res =
    TLarge
      ( TAbs
          ( Exi ("v_0", KType)
          , TSig
              ( Open
                  { fields = [("f", TLarge
                                      (TL_arrow ( Impure, sig1, sig2)))
                             ]

                  ; var = None
                  }
              )
          )
      )
  in
  assert_equal expected_res res ~printer:[%derive.show: Fcm.Typing.typ]

(* Mix a functor and regular function in the same signature.

   Reuses the functor from `test_functor`.

   { val f : { type t } -> { val f : t -> t }
     val g : bool -> unit
   }

   Should elaborate to:

   abs[exi(v_0)].{ val f : { t : [=v_0] } -> { val f : [=v_0] -> [=v_0] }
                   val g : [=bool] -> [=unit]
                 }

 *)
let test_functor_and_function _ =
  let expected_f =
    let sig1 = TSig (Open
                       { var = None
                       ; fields = [("t", TLarge (TTyp "v_0"))]
                       }
                 )
    in
    let sig2 = TSig (Open
                       { var = None
                       ; fields = [( "f"
                                   , TLarge (TL_arrow ( Impure
                                                      , TTyp "v_0"
                                                      , TTyp "v_0"))
                                   )]
                       }
                 )
    in
    TL_arrow (Impure, sig1, sig2)
  in
  let expected_g = TArrow (TBase TBool, TBase TUnit) in
  let expected_sig = TSig (Open { var = None
                                ; fields = [ "f", TLarge expected_f
                                           ; "g", TSmall expected_g] })
  in
  let expected = TLarge (TAbs (Exi ("v_0", KType), expected_sig)) in

  let np_sig ds = te_sig ds null_pos in
  let core_sig =
    let f =
      let app = type_apply (label "t" null_pos) [] null_pos in
      te_arrow
              (np_sig [Opaque_type (null_node "t", [])])
              (np_sig [Val_bind (null_node "f", te_arrow app app null_pos)])
    in
    let g = te_arrow (te_bool null_pos) (te_unit null_pos) in
    te_sig
      [ Val_bind (null_node "f", f null_pos)
      ; Val_bind (null_node "g", g null_pos)
      ]
      null_pos
  in

  let _, res, _ = elab_type_expr (Fcm.Env.make ()) core_sig in
  assert_equal expected res ~printer:[%derive.show: typ]

let suite =
  "Basic elaboration tests" >:::
    test_simple_sig_elab @
      [ "Simple functor type" >:: test_functor
      ; "Functor and function in signature" >:: test_functor_and_function
      ]

let _ =
  run_test_tt_main suite
