open OUnit2

open Test2_pa
open Test2_ag

let pa_prog_attributed s =
  s
  |> Stream.of_string
  |> Grammar.Entry.parse Test2_pa.prog_attributed_eoi

let test_records ctxt =
  assert_equal 3 ({| x + y |} |> pa_prog_attributed |> AG.evaluate)
; assert_equal 5 ({| 1 + w |} |> pa_prog_attributed |> AG.evaluate)

let suite = "test2" >::: [
    "test_records"           >:: test_records
  ]


if not !Sys.interactive then
  run_test_tt_main suite
else ()
