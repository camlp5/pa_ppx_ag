open OUnit2

open Test2_pa
open Test2_ag

let pa_prog_attributed s =
  s
  |> Stream.of_string
  |> Grammar.Entry.parse Test2_pa.prog_attributed_eoi

let test_records ctxt =
  let printer = [%show: string list * string list * int] in
  assert_equal ~printer (["x"; "y"], ["x"; "y"; "+"], 3) ({| x + y |} |> pa_prog_attributed |> AG.evaluate)
; assert_equal ~printer (["w"], ["1"; "w"; "+"], 5) ({| 1 + w |} |> pa_prog_attributed |> AG.evaluate)
; assert_equal ~printer ([], ["6"; "bind z"; "1"; "z"; "+"], 7) ({| let z = 6 in 1 + z |} |> pa_prog_attributed |> AG.evaluate)

let test_side_effect ctxt =
  let printer = [%show: string list * string list * int] in begin
    Test2_ag.global_ref := [] ;
    assert_equal ~printer (["x"; "y"], ["x"; "y"; "+"], 3) ({| x + y |} |> pa_prog_attributed |> AG.evaluate) ;
    assert_equal ~printer:[%show: string list] ["after"; "before"] !Test2_ag.global_ref
  end

let suite = "test2" >::: [
    "test_records"           >:: test_records
  ; "test_side_effect"           >:: test_side_effect
  ]


if not !Sys.interactive then
  run_test_tt_main suite
else ()
