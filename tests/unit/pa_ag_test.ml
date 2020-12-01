
open OUnit2 ;
open Pa_ppx_testutils ;
open Papr_util ;

value pa_ag s =
  s |> Stream.of_string |> Grammar.Entry.parse Pa_ag.attribute_grammar_body ;

value pa_ag_element s =
  s |> Stream.of_string |> Grammar.Entry.parse Pa_ag.attribute_grammar_element ;

value test_simple _ =
  ignore(pa_ag_element "ATTRIBUTE x : int ;")
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
