(* TODOs:

     - Property tests to generate valid and invalid functions and elaborate them.
 *)

open Fcm.Core
open Fcm.Elab
open Fcm.Typing

open OUnit2

let fexp_node_printer = [%derive.show: fexp node]
let assert_fexp_eq = assert_equal ~printer:fexp_node_printer
let assert_ftyp_eq = assert_equal ~printer:([%derive.show: ftyp node])

(* Convenience methods for the System F AST.  They're here as a sort of
   prototyping/staging area and will move somewhere like src/typing.ml
   later.
 *)
let null_node x = { n = x; pos = null_pos }
let tbase b = null_node (TBase b)
let tvar n = null_node (TVar n)
let tnamed n = null_node (TNamed n)
let tarrow eff x y = null_node (Arrow_F (eff, x, y))
let tsig fs = null_node (TRow { fields = fs; var = Absent })
let tabs v e = null_node (Abs_FT (v, e))
let tapp x y = null_node (TApp (x, y))
let tskol a vs = null_node (TSkol (a, vs))
let uni n k = Uni (n, k)
let exi n k = Exi (n, k)

let abs var body = { n = Abs_F (var, body); pos = null_pos }
let ident n = null_node (Ident_F n)
let app a b = null_node (App_F (a, b))

let str_sig ~pos decls = { n = Signature decls; pos }
let np_str_sig = str_sig ~pos:null_pos

let constr ~pos name args = ({ n = name; pos }, args)
let np_constr = constr ~pos:null_pos

let t_var ~pos name = { n = TE_Var name; pos }
let np_t_var = t_var ~pos:null_pos

let opaque_decl constr = Opaque_type constr
let val_decl name body = Val_bind (name, body)

(* The very basic elaboration tests.  *)
let test_simple_sig_elab =
  [ "Empty sig" >::
      (fun _ ->
        let s1 = { n = Signature []; pos = null_pos } in
        let _env, res1_type = elab_type_expr (Fcm.Env.make ()) s1 in
        assert_ftyp_eq
          ({ n = TRow { var = Absent; fields = [] }; pos = null_pos })
          res1_type
      )
  ; "Single abstract type" >::
      (*
          { type t }
       *)
      (fun _ ->
        let t = Opaque_type ({ n = "t"; pos = null_pos }, []) in
        let s = { n = Signature [t]; pos = null_pos } in
        let _env, typ = elab_type_expr (Fcm.Env.make ()) s in
        let expected =
          tabs
            (exi "v_0" KType)
            (tsig [("t", tnamed "v_0")])
        in
        assert_ftyp_eq (expected) typ
      )
  ; "Two abstract types, one elaborates to a function." >::
      (fun _ ->
        (* { type t
             type u 'v
           }

           Should elaborate to:

           exi[v_0].exi[v_1]{ t : [=v_0]; u : v -> [=v_1(v)] }
         *)
        (* Reusing from the previous test:  *)
        let t = Opaque_type ({ n = "t"; pos = null_pos }, []) in
        (* This should elaborate to uni[v].v_1(v) *)
        let u = Opaque_type
                  ( { n = "u"; pos = null_pos }
                  , [{n = TE_Var "v"; pos = null_pos }]
                  )
        in
        let s = { n = Signature [t; u]; pos = null_pos } in
        let _, typ = elab_type_expr (Fcm.Env.make ()) s in

        assert_ftyp_eq
          (tabs
             (exi "v_0" KType)
             (tabs
                (exi "v_1" KType)
                (tsig
                   [ ("t", tnamed "v_0")
                   ; ("u", tabs (uni "v" KType) (tskol "v_1" [tnamed "v"]))
                   ]
                )
             )
          )
          typ
      )
  (* I found some abstraction and variable ordering bugs when testing signature
     matching.  This should help prevent regression.
   *)
  ; "One abstract type with more than one variable." >::
      (fun _ ->
        let s = np_str_sig [opaque_decl (np_constr "u" [ np_t_var "a"
                                                       ; np_t_var "b"
                                                       ; np_t_var "c"])]
        in
        let _, elab_s = elab (Fcm.Env.make ()) (Type s) in
        let uk n = uni n KType in
        let { n = expected; _ } =
          tabs
            (exi "v_0" KType)
            (tsig
               [ ("u", tabs (uk "a")
                         (tabs (uk "b")
                            (tabs (uk "c") (tskol "v_0" [ tnamed "a"
                                                        ; tnamed "b"
                                                        ; tnamed "c"
                 ]))))
               ]
            )
        in
        assert_fexp_eq { n = Typ_F expected; pos = null_pos } elab_s
      )
  ]

(*
   { f : { type t } -> { val g : t -> t } }

   Should elaborate to:
   exi[v_0].{ f : { t : [=v_0]} -> { f : [=v_0] -> [=v_0] } }
 *)
let test_functor _ =
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
  let g = TE_Arrow (arg, body) in
  let d1 = Val_bind ({ n = "g"; pos = null_pos }, { n = g; pos = null_pos }) in
  let _, res = elab_type_expr (Fcm.Env.make ()) { n = Signature [d1]; pos = null_pos } in

  let sig1 = tsig [("t", tnamed "v_0")] in
  let sig2 = tsig [("f", tarrow Impure (tnamed "t") (tnamed "t"))] in
  let expected_res =
    tabs
      (exi "v_0" KType)
      (tsig [("g", tarrow Impure sig1 sig2)])
  in
  assert_ftyp_eq expected_res res

(* Mix a functor and regular function in the same signature.

   Reuses the functor from `test_functor`.

   { val f : { type t } -> { val f : t -> t }
     val g : bool -> unit
   }

   Should elaborate to:

   exi[v_0].{ val f : { t : [=v_0] } -> { val f : [=v_0] -> [=v_0] }
              val g : [=bool] -> [=unit]
            }
 *)
let test_functor_and_function _ =
  let expected_f =
    let sig1 = tsig [("t", tnamed "v_0")] in
    let sig2 = tsig [( "f", tarrow Impure (tnamed "t") (tnamed "t"))] in
    tarrow Impure sig1 sig2
  in
  let expected_g = tarrow Impure (tbase TBool) (tbase TUnit) in
  let expected_sig = tsig [ "f", expected_f; "g", expected_g] in
  let expected =
    tabs
      (Exi ("v_0", KType))
      expected_sig
  in

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

  let _, res = elab_type_expr (Fcm.Env.make ()) core_sig in
  assert_ftyp_eq expected res

(*

    type t a
    type u = t { type v }
 *)
let test_large_type_apply _ =
  let typ = Opaque_type (null_node "t", [null_node (TE_Var "a")]) in
  let fail1 = Transparent_type
                ( type_const (null_node "u") []
                , null_node
                    (TE_Apply
                       ( null_node "t"
                       , [te_sig [Opaque_type (null_node "v", [])] null_pos])))
  in
  let fail_sig_1 = te_sig [typ; fail1] null_pos in
  assert_raises
    (Predicativity_violation null_pos)
    (fun _ -> elab_type_expr (Fcm.Env.make ()) fail_sig_1)

(* Test a transparent type's usage of an opaque type, within the same signature.

   { type t a
     type u b = t b
   }

   Should elaborate to:

   exi[v_0].{ t : uni[a].[=v_0(a)]
              u : uni[b].[=t(b)]
            }

 *)
let test_transparent_and_opaque_type _ =
  let to_elab =
    let t = Opaque_type (null_node "t", [null_node (TE_Var "a")]) in
    let u = Transparent_type
              ( (null_node "u", [null_node (TE_Var "b")])
              , null_node (TE_Apply ((null_node "t"), [null_node (TE_Var "b")]))
              )
    in
    te_sig [t; u] null_pos
  in
  let expected =
    tabs
      (exi "v_0" KType)
      (tsig [ "t", tabs (uni "a" KType) (tskol "v_0" [tnamed "a"])
            ; "u", tabs (uni "b" KType) (tapp (tnamed "t") (tnamed "b"))
      ])
  in
  let _, res = elab_type_expr (Fcm.Env.make ()) to_elab in
  assert_ftyp_eq expected res

let property_sig_elab_test =
  let open QCheck in
  QCheck.Test.make
    ~count:100
    ~name:"Property-based signature elaborations"
    (make ~print:[%derive.show: expr] Ast_gen.sig_gen)
    (fun x ->
      match x with
      | Type t ->
         let _, _ = elab_type_expr (Fcm.Env.make ()) t in true
      | _ -> false
    )

let valid_fun_gen_test =
  let open QCheck in
  QCheck.Test.make
    ~count:100
    ~name:"Property-based valid function elaborations"
    (make ~print:[%derive.show: term node] (Ast_gen.valid_fun_gen ()))
    (fun x ->
      match elab_term (Fcm.Env.make ()) x with
      | _, { n = Lam_F _; _ } -> true
      | _ -> false
    )

(* Only checks anonymous functions, Fcm.Core.Fun.  *)
let valid_functor_gen_test =
  let open QCheck in
  QCheck.Test.make
    ~count:1000
    ~name:"Property-based valid functor elaborations"
    (make ~print:[%derive.show: term node] (Ast_gen.valid_functor_gen ()))
    (fun x ->
      match elab_term (Fcm.Env.make ()) x with
      | _, { n = Lam_F { arg_typ = { n = TRow _; _ }; _ }; _ } -> true
      | _, { n = Lam_F { arg_typ = { n = Abs_FT _; _ }; _ }; _ } -> true
      | _, other ->
         print_endline ([%derive.show: fexp node] other);
         false
    )

let valid_module_gen_test =
  let open QCheck in
  QCheck.Test.make
    ~count:1000
    ~name:"Property-based valid module elaborations"
    (make ~print:[%derive.show: term node] (Ast_gen.module_gen ()))
    (fun x ->
      match elab_term (Fcm.Env.make ()) x with
      | _, { n = Structure_F _; _ } -> true
      | _, other ->
         print_endline ([%derive.show: fexp node] other);
         false
    )


let term_gen_tests =
  [ QCheck_ounit.to_ounit2_test valid_fun_gen_test
  ; QCheck_ounit.to_ounit2_test valid_functor_gen_test
  ; QCheck_ounit.to_ounit2_test valid_module_gen_test
  ]

let suite =
  "Basic elaboration tests" >:::
    term_gen_tests @ test_simple_sig_elab @
      [ "Simple functor type" >:: test_functor
      ; "Functor and function in signature" >:: test_functor_and_function
      (* Disabling since predicativity checks are no longer part of elaboration.
         Later this will be re-enabled after actual type checking is underway.

      ; "Type application with large types must fail" >:: test_large_type_apply
       *)
      ; "Transparent type using a local opaque type." >:: test_transparent_and_opaque_type
      ; QCheck_ounit.to_ounit2_test property_sig_elab_test
      ]

let _ =
  run_test_tt_main suite
