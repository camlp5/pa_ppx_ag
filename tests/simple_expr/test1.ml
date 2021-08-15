open OUnit2

open Test1_pa
open Test1_ag

let pa_prog_attributed s =
  s
  |> Stream.of_string
  |> Grammar.Entry.parse Test1_pa.prog_attributed_eoi

let test_records ctxt =
  let printer = [%show: string list * int] in
  ()
; assert_equal ~printer (["1"; "x"; ":="; "x"; ";"; "2"; "y"; ":="; ";"; "x"; "y"; "+"; ";"],3)
    ({| x := 1 ; x ; y := 2 ; x + y |} |> pa_prog_attributed |> REC.AG.Topological.evaluate)
; assert_equal ~printer (["1"; "x"; ":="; "2"; "y"; ":="; ";"; "x"; "y"; "/"; ";"],0)
    ({| x := 1 ; y := 2 ; x / y |} |> pa_prog_attributed |> REC.AG.Topological.evaluate)
; assert_raises (Failure "rhs must be nonzero")
    (fun () -> {| x := 1 ; y := 0 ; x / y |} |> pa_prog_attributed |> REC.AG.Topological.evaluate)
; assert_equal ~printer (["1"; "x"; ":="; "x"; ";"; "2"; "y"; ":="; ";"; "x"; "y"; "+"; ";"],3)
    ({| x := 1 ; x ; y := 2 ; x + y |} |> pa_prog_attributed |> REC.AG.Ordered.evaluate)
; assert_equal ~printer (["1"; "x"; ":="; "2"; "y"; ":="; ";"; "x"; "y"; "/"; ";"],0)
    ({| x := 1 ; y := 2 ; x / y |} |> pa_prog_attributed |> REC.AG.Ordered.evaluate)
; assert_raises (Failure "rhs must be nonzero")
    (fun () -> {| x := 1 ; y := 0 ; x / y |} |> pa_prog_attributed |> REC.AG.Ordered.evaluate)
 

let suite = "test1" >::: [
    "test_records"           >:: test_records
  ]


if not !Sys.interactive then
  run_test_tt_main suite
else ()
