open Fcm.Core
open Fcm.Elab
open Fcm.Typing

open OUnit2

open Elab_test

let str ~pos decls = { n = Mod decls; pos }
let np_str = str ~pos:null_pos

let type_decl constr t_expr = Type_decl (constr, t_expr)

let t_unit ~pos = { n = TE_Unit; pos }
let np_t_unit = t_unit ~pos:null_pos
let t_bool ~pos = { n = TE_Bool; pos }
let np_t_bool = t_bool ~pos:null_pos
let t_int ~pos = { n = TE_Int; pos }
let np_t_int = t_int ~pos:null_pos

let bind ~pos name expr = Let_bind ({ n = name; pos }, expr)
let np_bind = bind ~pos:null_pos

let v_bool ~pos b = Term { n = b; pos }
let np_v_bool = v_bool ~pos:null_pos
let v_fun ~pos arg arg_t body = Term { n = Fun ((arg, arg_t), body); pos }
let np_v_fun = v_fun ~pos:null_pos
let v_label ~pos l = Term { n = Label l; pos }
let np_v_label = v_label ~pos:null_pos

let te_arrow ~pos a b = { n = TE_Arrow (a, b); pos }
let np_te_arrow = te_arrow ~pos:null_pos

let te_named ~pos n = { n = Named n; pos }
let np_te_named = te_named ~pos:null_pos

let let_bind name expr = Let_bind (name, expr)
let v_fun ~pos a a_typ b = { n = Fun ((a, a_typ), b); pos }
let np_t_fun = v_fun ~pos:null_pos

let elab_and_type ?trace:(trace = default_trace) env term =
  let env2, et = elab env term in
  type_of ~trace env2 et

let debug_elab_and_type =
  let trace x =
    let _ = match x with
      | Result.Ok (_, x) -> print_endline ([%derive.show: ftyp node] x)
      | Result.Error e -> print_endline ([%derive.show: typing_error] e)
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
          ({ n = TRow {fields = []; var = Absent}; pos = null_pos })
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
          { n = TRow { fields = ["f", tabs (uni "v_0" KType) (tarrow Impure (tvar "v_0") (tvar "v_0")) ]
                     ; var = Absent
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
                    (Some { n = Named "t"; pos = null_pos })
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
                     ; var = Absent
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
                            ; var = Absent
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
                            ; var = Absent
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
        let expected = Binding_not_found (tnamed "q") in
        assert_equal expected res ~printer:[%derive.show: typing_error]
      )
  ; "Invalid sealing of a module with a polymorphic function" >::
      (fun _ ->
        (*
          Hrm.../is/ this invalid?  `f` in the module could be instantiated
          with `int`.  What's the case I'm actually worried about?

            { type t = int
              -- for_all 'a: int -> 'a -> int
              let f (x : int) y = x
            } :> { type t; val f : t -> t -> t }
         *)
        ()
      )
  ]

let suite =
  "Basic typing tests" >:::
    basic_module_tests
    @ sealing_tests
    @ []

let _ =
  run_test_tt_main suite
