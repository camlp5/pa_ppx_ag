
open OUnit2 ;
open Pa_ppx_testutils ;
open Papr_util ;
open Pa_ag ;

value pa_ag s =
  s |> Stream.of_string |> Grammar.Entry.parse attribute_grammar_body ;

value pa_ag_element s =
  s |> Stream.of_string |> Grammar.Entry.parse attribute_grammar_element ;

value test_simple _ =
  let loc = Ploc.dummy in
  assert_equal ~{cmp=equal_ag_element_t}
    (pa_ag_element "ATTRIBUTE x : int ;")
    (ATTRIBUTES [("x", <:ctyp< int >>, False)])
;


value suite = "AG Syntax Test" >::: [
    "test_simple"           >:: test_simple
  ]
;

value _ = 
if not Sys.interactive.val then
  run_test_tt_main suite
else ()
;
