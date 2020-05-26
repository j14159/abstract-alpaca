open OUnit2
open Sysf.Core

let test_abs_typ _ =
  let abs = Type_abs ("X", Abs ("x", TVar "X", Var "x")) in
  let res = typ_of (Env.create ()) abs in
  assert_equal (Uni ("X", Arrow (TVar "X", TVar "X"))) res ~printer:string_of_typ;
  let res2 = typ_of (Env.create ()) (Type_app (abs, TUnit)) in
  assert_equal (Arrow (TUnit, TUnit)) res2 ~printer:string_of_typ

let test_arrow_typing _ =
  let abs = Type_abs ("X", Abs ("x", TVar "X", Var "x")) in
  let of_arrow = Type_app (abs, Arrow (TUnit, TUnit)) in
  let t_of_arrow = typ_of (Env.create ()) of_arrow in
  assert_equal (Arrow (Arrow (TUnit, TUnit), Arrow (TUnit, TUnit))) t_of_arrow ~printer:string_of_typ;
  assert_equal (TUnit) (typ_of (Env.create ()) (App (of_arrow, Unit))) ~printer:string_of_typ

let suite =
  "Base test suite (iterating in the beginning)" >:::
    [ "Basic abstraction typing" >:: test_abs_typ
    ; "Arrow typing" >:: test_arrow_typing
    ]

let _ =
  run_test_tt_main suite
