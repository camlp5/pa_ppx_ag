open OUnit2

open Pa_ppx_testutils
open Test2_pa
open Test2_ag

let matches ?rex ?pattern text =
  let regexp = match (rex, pattern) with
      (Some rex, None) -> Pcre.regexp ~flags:[`DOTALL] rex
    | (None, Some pattern) -> Pcre.regexp (Pcre.quote pattern)
    | _ -> failwith "test2.matches: internal error in test setup" in
       
  Pcre.pmatch ~rex:regexp text

let assert_raises_exn_pattern ?msg ?rex ?pattern f =
  Testutil.assert_raises_exn_pred ?msg
    (function
        Failure msg when matches ?rex ?pattern msg -> true
      | Ploc.Exc(_, Stdlib.Stream.Error msg) when matches ?rex ?pattern msg -> true
      | Stdlib.Stream.Error msg when matches ?rex ?pattern msg -> true
      | Ploc.Exc(_, Failure msg) when matches ?rex ?pattern msg -> true
      | Invalid_argument msg when matches ?rex ?pattern msg -> true
      | _ -> false
    )
    f

let pa_prog_attributed s =
  s
  |> Stream.of_string
  |> Grammar.Entry.parse Test2_pa.prog_attributed_eoi

let test_records ctxt =
  let printer = [%show: string list * string list * int] in
  ()
; assert_equal ~printer (["x"; "y"], ["x"; "y"; "+"], 3) ({| x + y |} |> pa_prog_attributed |> AG.Topological.evaluate)
; assert_equal ~printer (["w"], ["1"; "w"; "+"], 5) ({| 1 + w |} |> pa_prog_attributed |> AG.Topological.evaluate)
; assert_equal ~printer ([], ["6"; "bind z"; "1"; "z"; "+"], 7) ({| let z = 6 in 1 + z |} |> pa_prog_attributed |> AG.Topological.evaluate)
; assert_equal ~printer (["w"], ["w"; "bind z"; "1"; "z"; "+"], 5) ({| let z = w in 1 + z |} |> pa_prog_attributed |> AG.Topological.evaluate)
; assert_equal ~printer (["x"; "y"], ["x"; "y"; "+"], 3) ({| x + y |} |> pa_prog_attributed |> AG.Ordered.evaluate)
; assert_equal ~printer (["w"], ["1"; "w"; "+"], 5) ({| 1 + w |} |> pa_prog_attributed |> AG.Ordered.evaluate)
; assert_equal ~printer ([], ["6"; "bind z"; "1"; "z"; "+"], 7) ({| let z = 6 in 1 + z |} |> pa_prog_attributed |> AG.Ordered.evaluate)
; assert_equal ~printer (["w"], ["w"; "bind z"; "1"; "z"; "+"], 5) ({| let z = w in 1 + z |} |> pa_prog_attributed |> AG.Ordered.evaluate)

let test_records_failure ctxt =
  assert_raises_exn_pattern ~rex:{|File.*characters.*rhs must be nonzero|}
    (fun () -> {foo| let y = 0 in x / y |foo} |> pa_prog_attributed |> AG.Topological.evaluate)
; assert_raises_exn_pattern ~rex:{|File.*characters.*rhs must be nonzero|}
    (fun () -> {foo| let y = 0 in x / y |foo} |> pa_prog_attributed |> AG.Ordered.evaluate)

let test_side_effect_topological ctxt =
  let printer = [%show: string list * string list * int] in begin
    Test2_ag.global_ref := [] ;
    assert_equal ~printer (["x"; "y"], ["x"; "y"; "+"], 3) ({| x + y |} |> pa_prog_attributed |> AG.Topological.evaluate) ;
    assert_equal ~printer:[%show: string list] ["after"; "before"] !Test2_ag.global_ref
  end

let test_side_effect_ordered ctxt =
  let printer = [%show: string list * string list * int] in begin
    Test2_ag.global_ref := [] ;
    assert_equal ~printer (["x"; "y"], ["x"; "y"; "+"], 3) ({| x + y |} |> pa_prog_attributed |> AG.Ordered.evaluate) ;
    assert_equal ~printer:[%show: string list] ["after"; "before"] !Test2_ag.global_ref
  end

let suite = "test2" >::: [
    "test_records"           >:: test_records
  ; "test_records_failure"           >:: test_records_failure
  ; "test_side_effect_topological"           >:: test_side_effect_topological
  ; "test_side_effect_ordered"           >:: test_side_effect_ordered
  ]


if not !Sys.interactive then
  run_test_tt_main suite
else ()
