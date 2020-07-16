open QCheck
open OUnit2

let variable_list_test =
  let open Fcm.Core in
  QCheck.Test.make
    ~count:100
    ~name:"Variable lists"
    (make ~print:(fun expr -> snd @@ Fcm.Format.format expr 80) Label_gen.sig_gen)
    (fun c -> match c with
              | Type c -> Result.is_ok (Fcm.Core.check_type_expr c)
              | _ -> false
    )

let suite =
  "Core language test suite" >:::
    [QCheck_ounit.to_ounit2_test variable_list_test ]

let _ =
  run_test_tt_main suite
