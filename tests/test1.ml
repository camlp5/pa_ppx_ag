open OUnit2

open Test1_pa
open Test1_ag

let pa_prog_unique s =
  s
  |> Stream.of_string
  |> Grammar.Entry.parse Test1_pa.prog_unique_eoi

let pa_prog_attributed s =
  s
  |> Stream.of_string
  |> Grammar.Entry.parse Test1_pa.prog_attributed_eoi

let test_hashtables ctxt =
  assert_equal 3 ({| x := 1 ; x ; y := 2 ; x + y |} |> pa_prog_unique |> HT.AG.evaluate)
; assert_equal 0 ({| x := 1 ; y := 2 ; x / y |} |> pa_prog_unique |> HT.AG.evaluate)

let test_records ctxt =
  assert_equal 3 ({| x := 1 ; x ; y := 2 ; x + y |} |> pa_prog_attributed |> REC.AG.evaluate)
; assert_equal 0 ({| x := 1 ; y := 2 ; x / y |} |> pa_prog_attributed |> REC.AG.evaluate)
 

let suite = "test1" >::: [
    "test_hashtables"           >:: test_hashtables
  ; "test_records"           >:: test_records
  ]


if not !Sys.interactive then
  run_test_tt_main suite
else ()
