open Fcm.Core
open Fcm.Elab
open Fcm.Typing

open OUnit2

open Ast
open Ast.Null_pos_core
open Ast.F_ast

open Elab_test

let elab_and_type ?trace:(trace = default_trace) env term =
  let env2, et = elab env term in
  type_of ~trace env2 et


let debug_elab_and_type =
  let trace label x =
    let _ = match x with
      | Result.Ok (_, x) ->
         print_endline (label ^ "\n" ^ ([%derive.show: ftyp node] x))
      | Result.Error e ->
         print_endline (label ^ "\n" ^ ([%derive.show: typing_error] e))
    in
    x
  in
  elab_and_type ~trace

let basic_module_tests =
  [ "An empty module types as a fixed signature" >::
      (fun _ ->
        let m = np_str [] in
        let env, elab_m = elab (Fcm.Env.make ()) (Term m) in
        let _, mt = Result.get_ok @@ type_of env elab_m in
        assert_ftyp_eq
          ({ n = TRow {fields = []; var = Empty}; pos = null_pos })
          mt
      )
  (*

      { let f x = x }
   *)
  ; "A module with one function, inferred correctly" >::
      (fun _ ->
        let m =
          let f = np_v_fun (np_v_label "x") (None) (np_v_label "x") in
          np_str
            [ np_bind "f" f
            ]
        in
        let env, elab_m = elab (Fcm.Env.make ()) (Term m) in
        let _, mt = Result.get_ok @@ type_of env elab_m in
        let expected =
          { n = TRow { fields = [ "f"
                                , tabs
                                    (uni "v_0" KType)
                                    (tarrow Impure (tvar "v_0") (tvar "v_0"))
                                ]
                     ; var = Empty
                  }
          ; pos = null_pos
          }
        in
        assert_ftyp_eq expected mt
      )
  ; "A module with one type and one function using it" >::
      (fun _ ->
        (*
          { type t = bool
            let f (b : t) = b
          }

         *)
        let m =
          let f = np_v_fun
                    (np_v_label "b")
                    (Some { n = TE_Named "t"; pos = null_pos })
                    (np_v_label "b")
          in
          np_str
            [ type_decl (np_constr "t" []) np_t_bool
            ; np_bind "f" f
            ]
        in
        let env, elab_m = elab (Fcm.Env.make ()) (Term m) in
        let _, mt = Result.get_ok @@ type_of env elab_m in
        let expected =
          { n = TRow { fields = [ "t", tbase TBool
                                ; "f", tarrow Impure (tnamed "t") (tnamed "t")
                                ]
                     ; var = Empty
                  }
          ; pos = null_pos
          }
        in
        assert_ftyp_eq expected mt
      )
  ]

let sealing_tests =
  [ "Make a single transparent type abstract by sealing." >::
       (fun _ ->
        (*
          { type t = bool } :> { type t }
         *)

        let m = { n = Mod [type_decl (np_constr "t" []) np_t_bool]; pos = null_pos } in
        let s = { n = Signature [opaque_decl (np_constr "t" [])]; pos = null_pos } in
        let sealed = Term { n = Seal (m, s); pos = null_pos } in
        let env, elab_sealed = elab (Fcm.Env.make ()) sealed in
        let _env, st = Result.get_ok @@ type_of env elab_sealed in
        let expected =
          { n = Abs_FT
                  ( Exi ("v_0", KType)
                  , { n = TRow
                            { fields = [("t", { n = TNamed "v_0"; pos = null_pos })]
                            ; var = Empty
                            }
                    ; pos = null_pos
                    }
                  )
          ; pos = null_pos
          }
        in
        assert_ftyp_eq expected st
      )
  ; "Make a single-parameter type abstract by sealing." >::
      (fun _ ->
        (*
          { type 'a t = bool } :> { type 'a t }
         *)

        let m = { n = Mod [type_decl (np_constr "t" [np_t_var "a"]) np_t_bool]
                ; pos = null_pos
                }
        in
        let s = { n = Signature [opaque_decl (np_constr "t" [np_t_var "a"])]
                ; pos = null_pos
                }
        in
        let sealed = Term { n = Seal (m, s); pos = null_pos } in
        let env, elab_sealed = elab (Fcm.Env.make ()) sealed in
        let _env, st = Result.get_ok @@ type_of env elab_sealed in
        let expected =
          { n = Abs_FT
                  ( Exi ("v_0", KType)
                  , { n = TRow
                            { fields = [("t",
                                         tabs
                                           (uni "a" KType)
                                           { n = TSkol ("v_0", [tnamed "a"] )
                                           ; pos = null_pos
                                           }
                                       )]
                            ; var = Empty
                            }
                    ; pos = null_pos
                    }
                  )
          ; pos = null_pos
          }
        in
        assert_ftyp_eq expected st
      )
  (*
    This should fail because the constraint (the latter signature) has an arity
    smaller than the candidate (the former signature).

    { type t a b } :> { type t a }

    The reverse should fail for the same reason:

        { type t a } :> { type t a b }
   *)
  ; "Different arity type constructors should fail signature matching." >::
      (fun _ ->
        let s_con = Type (np_str_sig [opaque_decl (np_constr "t" [np_t_var "a"])]) in
        let candidate =
          np_str_sig [opaque_decl (np_constr "t" [np_t_var "a"; np_t_var "b"])]
        in
        let env, elab_s_con = elab (Fcm.Env.make ()) s_con in
        let env, s_con_type = Result.get_ok @@ type_of env elab_s_con in
        let env, elab_candidate = elab env (Type candidate) in

        let env, candidate_type = Result.get_ok @@ type_of env elab_candidate in
        let expected_exn =
          invalid_substitution_arity
                (tskol "v_0" [tnamed "a"])
                (tabs (uni "b" KType) (tskol "v_1" [tnamed "a"; tnamed "b"]))
        in
        assert_equal
          expected_exn
          (Result.get_error @@ signature_match env s_con_type candidate_type)
          ~printer:[%derive.show: typing_error];

        (* Now check the reverse, which should fail with the reverse order of
           arguments to the exception, but still an arity problem.
         *)
        let expected_exn =
          invalid_substitution_arity
            (tabs (uni "b" KType) (tskol "v_1" [tnamed "a"; tnamed "b"]))
            (tskol "v_0" [tnamed "a"])
        in

        assert_equal
          expected_exn
          (Result.get_error @@ signature_match env candidate_type s_con_type)
          ~printer:[%derive.show: typing_error]
      )
  (*
      { type t = bool
        let f (x : t) = x
        let g y = y
      } :> { type t; val f : t -> t }
   *)
  ; "Sealing an empty module with a non-empty signature should fail." >::
      (fun _ ->
        let s_con = np_str_sig
                      [ opaque_decl (np_constr "t" [])
                      ]
        in
        let m = np_str [] in
        let sealed = Term { n = Seal (m, s_con); pos = null_pos } in
        let err = Result.get_error @@ elab_and_type (Fcm.Env.make ()) sealed in
        let expected_error = missing_member "t" null_pos in
        assert_equal expected_error err ~printer:[%derive.show: typing_error]
      )
  (*
      { type t = bool
        let id x = x
        let f y z = y
      } :> { type t; val id : t -> t }
   *)
  ; "Sealing a 3-member module with a 2-member signature should forget one member" >::
      (fun _ ->
        let s_con = np_str_sig
                      [ opaque_decl (np_constr "t" [])
                      ; val_decl
                          (null_node "id")
                          (np_te_arrow (np_te_named "t") (np_te_named "t"))
                      ]
        in
        let m = np_str
                  [ type_decl (np_constr "t" []) np_t_int
                  ; let_bind
                      (null_node "id")
                      (np_v_fun (np_v_label "x") (Option.some (np_te_named "t")) (np_v_label "x"))
                  ; let_bind
                      (null_node "f")
                      (np_v_fun
                         (np_v_label "y")
                         Option.None
                         (np_v_fun (np_v_label "z") Option.None (np_v_label "y"))
                      )
                  ]
        in
        let sealed = Term { n = Seal (m, s_con); pos = null_pos } in
        let _, res = Result.get_ok @@ elab_and_type (Fcm.Env.make ()) sealed in
        let expected =
          tabs
            (exi "v_2" KType)
            (tsig
               ~row:Empty
               [ "t", tnamed "v_2"
               ; "id", tarrow Impure (tnamed "t") (tnamed "t")
               ]
            )
        in
        assert_ftyp_eq expected res
      )
  (* When writing the previous test, the substitution check /without/ type
     annotations on the argument to `id` would fail because the arrows weren't
     identical.  I added equality/substitution checks and am keeping this test
     for regressions.

      { type t = bool
        let id x = x
      } :> { type t; val id : t -> t }
   *)
  ; "Sealing a module with an abstract signature and no annotations." >::
      (fun _ ->
        let s_con = np_str_sig
                      [ opaque_decl (np_constr "t" [])
                      ; val_decl
                          (null_node "id")
                          (np_te_arrow (np_te_named "t") (np_te_named "t"))
                      ]
        in
        let m = np_str
                  [ type_decl (np_constr "t" []) np_t_int
                  ; let_bind
                      (null_node "id")
                      (* TODO:  test with dropped annotation.  *)
                      (np_v_fun (np_v_label "x") Option.None (np_v_label "x"))
                  ]
        in
        let sealed = Term { n = Seal (m, s_con); pos = null_pos } in
        let res = elab_and_type (Fcm.Env.make ()) sealed in
        let _, res = Result.get_ok @@ res in
        let expected =
          tabs
            (exi "v_1" KType)
            (tsig
               ~row:Empty
               [ "t", tnamed "v_1"
               ; "id", tarrow Impure (tnamed "t") (tnamed "t")
               ]
            )
        in
        assert_ftyp_eq expected res
      )
  ; "Sealing a valid module with an invalid signature." >::
      (fun _ ->
        let m = np_str
                  [ type_decl (np_constr "u" []) np_t_int
                  ; let_bind
                      (null_node "id")
                      (np_v_fun (np_v_label "x") Option.None (np_v_label "x"))
                  ]
        in
        (*
          Use of undefined type in `id`:

              { type u; val id : q -> q }
         *)
        let invalid_sig = np_str_sig
                            [ opaque_decl (np_constr "u" [])
                            ; val_decl
                                (null_node "id")
                                (np_te_arrow (np_te_named "q") (np_te_named "q"))
                            ]
        in
        let sealed = Term { n = Seal (m, invalid_sig); pos = null_pos } in

        let res = elab_and_type (Fcm.Env.make ()) sealed in
        assert_equal true (Result.is_error res);
        let res = Result.get_error @@ res in
        let expected = Invalid_type (tnamed "q") in
        assert_equal expected res ~printer:[%derive.show: typing_error]
      )
  ; "Sealing a 2-type function including a universal" >::
      (fun _ ->
        (*
          I was initially concerned that this should be an error, but then
          realized that there's nothing wrong with further restricting the
          type of `f` in the module.  I suspect I need to treat this more
          correctly with instantiation of the arrow, though.

            { type t = int
              -- for_all 'a: int -> 'a -> int
              let f (x : int) y = x
            } :> { type t; val f : t -> t -> t }
         *)
        let s_t = np_te_named "t" in
        let s = np_str_sig
                  [ opaque_decl (np_constr "t" [])
                  ; val_decl
                      (null_node "f")
                      (np_te_arrow s_t (np_te_arrow s_t s_t))
                  ]
        in
        let m = np_str
                  [ type_decl (np_constr "t" []) np_t_int
                  ; let_bind
                      (null_node "f")
                      (np_v_fun
                         (np_v_label "x")
                         (Option.some np_t_int)
                         (np_v_fun (np_v_label "y") Option.none (np_v_label "x"))
                      )
                  ]
        in
        let sealed = Term { n = Seal (m, s); pos = null_pos } in
        let _, res = Result.get_ok @@ elab_and_type (Fcm.Env.make ()) sealed in
        let expected = tabs
                         (exi "v_1" KType)
                         (tsig
                            ~row:Empty
                            [ "t", tnamed "v_1"
                            ; "f", tarrow
                                     Impure
                                     (tnamed "t")
                                     (tarrow Impure (tnamed "t") (tnamed "t"))
                         ])
        in
        assert_ftyp_eq expected res
      )
  ]

(* Testing success and error cases for paths, projecting types and values out of
   rows.

   I'm aiming more for the F-ing functors/modules approach here which permits
   more than the projection only of fully formed signatures.
 *)
let path_tests =
  [ "Projection of an existential inside its enclosing module." >::
      (fun _ ->
        (* This should fail because `a.t` is not a real type, can't project
           a type out of a signature, only a module.

             { type a = { type t }
               type b = a.t
             }
         *)
        let m = np_str
          [ type_decl
              (np_constr "a" [])
              (np_str_sig [opaque_decl (np_constr "t" [])])
          ; type_decl
              (np_constr "b" [])
              { n = TE_Path (np_te_named "a", null_node "t"); pos = null_pos }
          ]
        in
        let res = elab_and_type (Fcm.Env.make ()) (Term m) in
        (* TODO:  check error.  *)
        assert_equal true (Result.is_error res)
      )
  ; "Projection of an internal module's type within its enclosing module" >::
      (fun _ ->
        (*
          { type s = { type t }
            let m = { type t = int } :> s
            type u = m.t
         *)
        let m = np_str
                  [ type_decl
                      (constr ~pos:(pseudo_pos 20) "s" [])
                      (str_sig ~pos:(pseudo_pos 21) [opaque_decl (constr ~pos:(pseudo_pos 22) "t" [])])
                  ; let_bind
                      (null_node "m")
                      (Term { n = Seal
                                    ( (np_str [type_decl
                                                 (constr ~pos:(pseudo_pos 12) "t" [])
                                                 (np_t_int)]
                                      )
                                    , te_named ~pos:(pseudo_pos 8)"s"
                                    )
                            ; pos = pseudo_pos 1
                      })
                  ; type_decl
                      (np_constr "u" [])
                      { n = TE_Path (np_te_named "m", { n = "t"; pos = pseudo_pos 2 })
                      ; pos = pseudo_pos 3
                      }

                  ]
        in
        let res = elab_and_type (Fcm.Env.make ()) (Term m) in
        assert_equal true (Result.is_ok res)
      (* TODO:  check actual type coming back. *)
      )
  ; "Projection from an unbound signature, which should fail." >::
      (fun _ ->
        (*
          This should fail because the existential from the signature is not
          bound anywhere.

          { type a = { type t }.t }
         *)
        let m =
          np_str
            [ type_decl
                (np_constr "a" [])
                { n = TE_Path
                        ( np_str_sig [opaque_decl (np_constr "t" [])]
                        , null_node "t"
                        )
                ; pos = null_pos
                }
            ]
        in
        let res = elab_and_type (Fcm.Env.make ()) (Term m) in
        let _ = Result.map
                  (fun (env, _) -> print_endline ([%derive.show: (ftyp node, kind) Fcm.Env.t] env))
                  res
        in
        assert_equal true (Result.is_error res);
        let expected = Invalid_type (tnamed "v_0") in
        assert_equal expected (Result.get_error res) ~printer:[%derive.show: typing_error]
      )

  ]
let suite =
  "Basic typing tests" >:::
    basic_module_tests
    @ sealing_tests
    @ path_tests
    @ []

let _ =
  run_test_tt_main suite
