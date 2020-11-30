open OUnit2

open Test2_pa
open Test2_ag

let pa_prog_attributed s =
  s
  |> Stream.of_string
  |> Grammar.Entry.parse Test2_pa.prog_attributed_eoi

let test_records ctxt =
  let printer = [%show: int * string list * string list] in
  assert_equal ~printer (3, ["x"; "y"; "+"], ["x"; "y"]) ({| x + y |} |> pa_prog_attributed |> AG.evaluate)
; assert_equal ~printer (5, ["1"; "w"; "+"], ["w"]) ({| 1 + w |} |> pa_prog_attributed |> AG.evaluate)
; assert_equal ~printer (7, ["6"; "bind z"; "1"; "z"; "+"], []) ({| let z = 6 in 1 + z |} |> pa_prog_attributed |> AG.evaluate)

let suite = "test2" >::: [
    "test_records"           >:: test_records
  ]


if not !Sys.interactive then
  run_test_tt_main suite
else ()
