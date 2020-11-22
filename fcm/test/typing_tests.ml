open Fcm.Core
open Fcm.Elab
open Fcm.Typing

open OUnit2

open Elab_test

let str ~pos decls = Term { n = Mod decls; pos }
let np_str = str ~pos:null_pos

let type_decl constr t_expr = Type_decl (constr, t_expr)

let t_unit ~pos = { n = TE_Unit; pos }
let np_t_unit = t_unit ~pos:null_pos
let t_bool ~pos = { n = TE_Bool; pos }
let np_t_bool = t_bool ~pos:null_pos

let bind ~pos name expr = Let_bind ({ n = name; pos }, expr)
let np_bind = bind ~pos:null_pos

let v_bool ~pos b = Term { n = b; pos }
let np_v_bool = v_bool ~pos:null_pos
let v_fun ~pos arg arg_t body = Term { n = Fun ((arg, arg_t), body); pos }
let np_v_fun = v_fun ~pos:null_pos
let v_label ~pos l = Term { n = Label l; pos }
let np_v_label = v_label ~pos:null_pos

let basic_module_tests =
  [ "An empty module types as a fixed signature" >::
      (fun _ ->
        let m = np_str [] in
        let env, elab_m = elab (Fcm.Env.make ()) m in
        let _, mt = type_of env elab_m in
        assert_ftyp_eq
          ({ n = TSig {fields = []; var = Absent}; pos = null_pos })
          mt
      )
  ; "A module with one function, inferred correctly" >::
      (fun _ ->
        let m =
          let f = np_v_fun (np_v_label "x") (None) (np_v_label "x") in
          np_str
            [ np_bind "f" f
            ]
        in
        let env, elab_m = elab (Fcm.Env.make ()) m in
        let _, mt = type_of env elab_m in
        let expected =
          { n = TSig { fields = ["f", tarrow Impure (tvar "v_0") (tvar "v_0") ]
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

          Because `t` is transparently equivalent to `bool`, the test currently
          expects `f` to type to `bool -> bool`.  Not sure that this is best.

          In OCaml via utop:

            module M = struct
              type t = bool
              let f : t -> t = fun x -> x
            end;;

          Types as:
            module M : sig type t = bool val f : t -> t end

          But `M.f;;` returns ` - : bool -> bool = <fun>` so I'll stick with
          what follows for now.
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
        let env, elab_m = elab (Fcm.Env.make ()) m in
        let _, mt = type_of env elab_m in
        let expected =
          { n = TSig { fields = [ "t", tbase TBool
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
        let _env, st = type_of env elab_sealed in
        let expected =
          { n = Abs_FT
                  ( Exi ("v_0", KType)
                  , { n = TSig
                            { fields = [("t", { n = TNamed (Flat "v_0"); pos = null_pos })]
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
        let _env, st = type_of env elab_sealed in
        let expected =
          { n = Abs_FT
                  ( Exi ("v_0", KType)
                  , { n = TSig
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
        let s_con = np_str_sig [opaque_decl (np_constr "t" [np_t_var "a"])] in
        let candidate =
          np_str_sig [opaque_decl (np_constr "t" [np_t_var "a"; np_t_var "b"])]
        in
        let env, elab_s_con = elab (Fcm.Env.make ()) s_con in
        let env, s_con_type = type_of env elab_s_con in
        let env, elab_candidate = elab env candidate in

        let env, candidate_type = type_of env elab_candidate in
        let expected_exn =
          Invalid_substitution_arity
            ( tskol "v_0" [tnamed "a"]
            , tabs (uni "b" KType) (tskol "v_1" [tnamed "a"; tnamed "b"])
            )
        in
        assert_raises
          expected_exn
          (fun _ -> signature_match env s_con_type candidate_type);

        (* Now check the reverse, which should fail with the reverse order of
           arguments to the exception, but still an arity problem.
         *)
        let expected_exn =
          Invalid_substitution_arity
            ( tabs (uni "b" KType) (tskol "v_1" [tnamed "a"; tnamed "b"])
            , tskol "v_0" [tnamed "a"]
            )
        in

        assert_raises
          expected_exn
          (fun _ -> signature_match env candidate_type s_con_type)
      )
  ]

let suite =
  "Basic typing tests" >:::
    basic_module_tests
    @ sealing_tests
    @ []

let _ =
  run_test_tt_main suite
