
open OUnit2 ;
open Pa_ppx_testutils ;
open Papr_util ;
open Pa_ag ;

value pa_ag s =
  s |> Stream.of_string |> Grammar.Entry.parse attribute_grammar_body ;

value pa_ag_element s =
  s |> Stream.of_string |> Grammar.Entry.parse attribute_grammar_element ;

value test_simple _ = do {
  let loc = Ploc.dummy in
  assert_equal ~{cmp=equal_ag_element_t} ~{printer=show_ag_element_t}
    (ATTRIBUTES [("x", <:ctyp< int >>, False)])
    (pa_ag_element "ATTRIBUTE x : int ;")
;   assert_equal ~{cmp=equal_ag_element_t} ~{printer=show_ag_element_t}
    (ATTRIBUTES [("rpn", <:ctyp< list string >>, True)])
    (pa_ag_element "CHAIN rpn : list string ;")
;   assert_equal ~{cmp=equal_ag_element_t} ~{printer=show_ag_element_t}
    (ATTRIBUTES [
        ("bin_oper", <:ctyp< int -> int -> int >>, False)
      ; ("env", <:ctyp< list (string * int) >>, False)
      ])
    (pa_ag_element {foo| ATTRIBUTES
  bin_oper : int -> int -> int ;
  env : list (string * int) ;
END ; |foo})
;   assert_equal ~{cmp=equal_ag_element_t} ~{printer=show_ag_element_t}
    (pa_ag_element {foo|
RULE INT : expr := int
COMPUTE
  $[0].value_ := $[1] ;
  $[0].rpn := [(string_of_int $[1]) :: $[0].rpn] ;
END ;
 |foo})
    (Pa_ag.RULE "INT" "expr" [<:ctyp< int >>]
       [ <:expr< [%nterm 0;].value_ := [%child 1;] >>
       ; <:expr< [%nterm 0;].rpn := [(string_of_int [%child 1;]) :: [%nterm 0;].rpn] >> ]
    )
;   assert_equal ~{cmp=equal_ag_element_t} ~{printer=show_ag_element_t}
    (pa_ag_element {foo|
RULE PROG : prog := block1
COMPUTE
  $[0].value_ := $[1].value_ ;
  CHAINSTART $[1].rpn := [] ;
  $[0].rpn_notation := List.rev $[1].rpn ;
END ;
 |foo})
    (Pa_ag.RULE "PROG" "prog" [<:ctyp< block1 >>]
       [
         <:expr< [%nterm 0;].value_ := [%child 1;].value_ >>
           ; <:expr< (CHAINSTART ([%child 1;].rpn)) := [] >>
           ; <:expr< [%nterm 0;].rpn_notation := List.rev [%child 1;].rpn >>
       ]
    )
; ()
}
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
