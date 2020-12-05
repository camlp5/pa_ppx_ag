
open OUnit2 ;
open Pa_ppx_testutils ;
open Pa_ppx_base ;
open Papr_util ;
open Pa_ag ;

value file_contents fname =
  fname
  |> Fpath.v
  |> Bos.OS.File.read
  |> Rresult.R.get_ok
;

value show_str_item si =
  Fmt.(str "#<str_item< %s >>" (Eprinter.apply Pcaml.pr_str_item Pprintf.empty_pc si));

value pa_str_item s =
  s |> Stream.of_string |> Grammar.Entry.parse Pcaml.str_item ;

value pa_ag_body s =
  s |> Stream.of_string |> Grammar.Entry.parse attribute_grammar_body ;

value pa_ag_element s =
  s |> Stream.of_string |> Grammar.Entry.parse attribute_grammar_element ;

value test_ag_elements _ = do {
  ()
; let loc = Ploc.dummy in
  assert_equal ~{cmp=equal_ag_element_t} ~{printer=show_ag_element_t}
    (ATTRIBUTES Ploc.dummy [("x", <:ctyp< int >>, False)])
    (pa_ag_element "ATTRIBUTE x : int ;")
; assert_equal ~{cmp=equal_ag_element_t} ~{printer=show_ag_element_t}
    (ATTRIBUTES Ploc.dummy [("rpn", <:ctyp< list string >>, True)])
    (pa_ag_element "CHAIN rpn : list string ;")
; assert_equal ~{cmp=equal_ag_element_t} ~{printer=show_ag_element_t}
    (ATTRIBUTES Ploc.dummy [
        ("bin_oper", <:ctyp< int -> int -> int >>, False)
      ; ("env", <:ctyp< list (string * int) >>, False)
      ])
    (pa_ag_element {foo| ATTRIBUTES
  bin_oper : int -> int -> int ;
  env : list (string * int) ;
END ; |foo})
; assert_equal ~{cmp=equal_ag_element_t} ~{printer=show_ag_element_t}
    (pa_ag_element {foo|
RULE INT : expr := int
COMPUTE
  $[0].value_ := $[1] ;
  $[0].rpn := [(string_of_int $[1]) :: $[0].rpn] ;
END ;
 |foo})
    (Pa_ag.RULE Ploc.dummy "INT" "expr" [<:ctyp< int >>]
       [ <:expr< [%nterm 0;].value_ := [%child 1;] >>
       ; <:expr< [%nterm 0;].rpn := [(string_of_int [%child 1;]) :: [%nterm 0;].rpn] >> ]
    )
; assert_equal ~{cmp=equal_ag_element_t} ~{printer=show_ag_element_t}
    (pa_ag_element {foo|
RULE PROG : prog := block1
COMPUTE
  $[0].value_ := $[1].value_ ;
  CHAINSTART $[1].rpn := [] ;
  $[0].rpn_notation := List.rev $[1].rpn ;
END ;
 |foo})
    (Pa_ag.RULE Ploc.dummy "PROG" "prog" [<:ctyp< block1 >>]
       [
         <:expr< [%nterm 0;].value_ := [%child 1;].value_ >>
           ; <:expr< (([%chainstart 1;].rpn)) := [] >>
           ; <:expr< [%nterm 0;].rpn_notation := List.rev [%child 1;].rpn >>
       ]
    )
; assert_equal ~{cmp=equal_ag_element_t} ~{printer=show_ag_element_t}
    (rule_replace_child (pa_ag_element {foo|
RULE LET_BINDING : let_expr := string and expr and expr
COMPUTE
  $[0].value_ := $[3].value_ ;
  $[3].rpn := [(Printf.sprintf "bind %s" $[1]) :: $[2].rpn] ;
  $[0].env := [($[1], $[2].value_) :: INCLUDING ( block1.env, let_expr.env )] ;
  $[0].freevars :=
    Std.union
      (CONCAT (ref_expr.freevars, let_expr.freevars) IN $[2])
      (Std.except $[1] (CONCAT (ref_expr.freevars, let_expr.freevars) IN $[3])) ;
END ;
 |foo}))
    (Pa_ag.RULE Ploc.dummy "LET_BINDING" "let_expr" [<:ctyp< string >>; <:ctyp< expr >>; <:ctyp< expr >>]
       [
         <:expr< [%nterm 0;].value_ := [%nterm 3;].value_ >>
       ; <:expr< [%nterm 3;].rpn := [(Printf.sprintf "bind %s" [%prim 1;]) :: [%nterm 2;].rpn] >>
       ; <:expr< [%nterm 0;].env := [([%prim 1;], [%nterm 2;].value_) :: [%"remote" (block1.env, let_expr.env);]] >>
       ; <:expr< [%nterm 0;].freevars :=
    Std.union
      [%"constituents" {attributes = (ref_expr.freevars, let_expr.freevars); nodes = [%"nterm" 2;]};]
      (Std.except [%prim 1;] [%"constituents" {attributes = (ref_expr.freevars, let_expr.freevars); nodes = [%"nterm" 3;]};]) >>
       ]
    )
; assert_equal ~{cmp=[%eq: list (string * string)]} ~{printer=[%show: list (string * string)]}
    (rule_to_node_attributes (rule_replace_child (pa_ag_element {foo|
RULE LET_BINDING : let_expr := string and expr and expr
COMPUTE
  $[0].value_ := $[3].value_ ;
  $[3].rpn := [(Printf.sprintf "bind %s" $[1]) :: $[2].rpn] ;
  $[0].env := [($[1], $[2].value_) :: INCLUDING ( block1.env, let_expr.env )] ;
  $[0].freevars :=
    Std.union
      (CONCAT (ref_expr.freevars, let_expr.freevars) IN $[2])
      (Std.except $[1] (CONCAT (ref_expr.freevars, let_expr.freevars) IN $[3])) ;
END ;
 |foo})))
    [("expr", "rpn"); ("expr", "value_"); ("let_expr", "env");
     ("let_expr", "freevars"); ("let_expr", "value_")]
; assert_equal ~{cmp=[%eq: list ((string * string) * string)]} ~{printer=[%show: list ((string * string) * string)]}
    (rule_to_prod_attributes (rule_replace_child (pa_ag_element {foo|
RULE BINOP : expr := binop and expr and expr
COMPUTE
  $[0].value_ := $result ;
  $result := $[1].bin_oper $[2].value_ $[3].value_ ;
  $[0].rpn := [$[1].operator_text :: $[3].rpn] ;
  condition "rhs must be nonzero"
    (if $[1].rhs_must_be_nonzero then
       0 <> $[3].value_
     else true) ;
END ;
 |foo})))
    [(("expr", "BINOP"), "result")]
; assert_equal ~{cmp=equal_ag_element_t} ~{printer=show_ag_element_t}
    (pa_ag_element {foo|
RULE R : x
COMPUTE
  $[0].b := $[0].a ;
END ;
 |foo})
    (Pa_ag.RULE Ploc.dummy "R" "x" []
       [ <:expr< [%nterm 0;].b := [%nterm 0;].a >> ]
    )
}
;

value test_ag _ = do {
  ()
; let loc = Ploc.dummy in
  assert_equal ~{cmp=Reloc.eq_str_item} ~{printer=show_str_item}
  <:str_item< type x = [ R ][@@deriving ag { optional = True ; module_name = AG;
              attribution_model = Attributed { attributed_module_name = AT };
              storage_mode = Records ; axiom = x; attribute_types = ();
              node_attributes = {x = [a; b]};
              production_attributes = ();
              attribution = {
                x__R = ([%"nterm" 0;].b := [%"nterm" 0;].a)
              }
              };] >>
    ({foo|
ATTRIBUTE_GRAMMAR
  DEBUG True ;
  MODULE AG ;
  ATTRIBUTION_MODEL Attributed {
    attributed_module_name = AT
  } ;

  AXIOM x ;
RULE R : x
COMPUTE
  $[0].b := $[0].a ;
END ;

END ;

|foo} |> pa_str_item)
; let loc = Ploc.dummy in
  assert_equal ~{cmp=Reloc.eq_str_item} ~{printer=show_str_item}
  <:str_item< type x = [ Q of x and x | R ]
              and z = [ P of x ][@@deriving ag { optional = False ; module_name = AG;
              attribution_model = Attributed { attributed_module_name = AT };
              storage_mode = Records; axiom = z;
              attribute_types =
              {a = [%"typ": int]; b = [%"typ": int]; c = [%"typ": int];
              d = [%"typ": int]};
              node_attributes = {x = [a; b; c; d]};
              production_attributes = ();
              attribution = {
              x__Q = do {
              [%"nterm" 0;].b := g [%"nterm" 0;].a;
              [%"nterm" 1;].a := g [%"nterm" 0;].c;
              [%"nterm" 2;].a := g [%"nterm" 0;].c;
              [%"nterm" 1;].c := g [%"nterm" 1;].b;
              [%"nterm" 2;].c := g [%"nterm" 2;].b;
              [%"nterm" 0;].d := s ([%"nterm" 1;].d, [%"nterm" 2;].d)
              };
              x__R = do {
              [%"nterm" 0;].b := g [%"nterm" 0;].a;
              [%"nterm" 0;].d := g [%"nterm" 0;].c
              };
              z__P = do {
              [%"nterm" 1;].a := f ();
              [%"nterm" 1;].c := g [%"nterm" 1;].b;
              h [%"nterm" 1;].d
              }
              }
              };] >>
    ("kastens116.ag" |> file_contents |> pa_str_item)
; let loc = Ploc.dummy in
  assert_equal ~{cmp=Reloc.eq_str_item} ~{printer=show_str_item}
  <:str_item< type binop = [ MINUS | PERCENT | PLUS | SLASH | STAR ]
and block1 =
  [ BLOCK1 of block2 ]
and block2 =
  [ BLOCK2 of expr ]
and expr =
  [ BINOP of binop and expr and expr
  | INT of int
  | LET of let_expr
  | REF of ref_expr
  | SEQ of expr and expr
  | UNOP of unop and expr ]
and let_expr =
  [ LET_BINDING of string and expr and expr ]
and prog =
  [ PROG of block1 ]
and ref_expr =
  [ REF_EXPR of string ]
and unop = [ UMINUS | UPLUS ][@@deriving ag {
              optional = False ; module_name = AG ;
              attribution_model = Attributed { attributed_module_name = AT } ;
              storage_mode = Records;
              axiom = prog;
              attribute_types = {
              value_ = [%"typ": int];
              rpn = [%"typ": (list string [@chain])];
              bin_oper = [%"typ": int → int → int];
              env = [%"typ": (string * int) list];
              result = [%"typ": int];
              rhs_must_be_nonzero = [%"typ": bool];
              un_oper = [%"typ": int → int];
              rpn_notation = [%"typ": string list];
              operator_text = [%"typ": string];
              freevars = [%"typ": string list]
              };
              node_attributes = {
              binop = [bin_oper; operator_text; rhs_must_be_nonzero];
              block1 = [value_];
              block2 = [value_];
              expr = [rpn; value_];
              let_expr = [env; freevars; value_];
              prog = [freevars; rpn_notation; value_];
              ref_expr = [freevars; rpn; value_];
              unop = [operator_text; un_oper]
              };
              production_attributes = {expr__BINOP = [result]};
              attribution =
              {binop__MINUS = do {
              [%"nterm" 0;].bin_oper := ( - );
              [%"nterm" 0;].rhs_must_be_nonzero := false;
              [%"nterm" 0;].operator_text := "-"
              };
              binop__PERCENT = do {
              [%"nterm" 0;].bin_oper := ( mod );
              [%"nterm" 0;].rhs_must_be_nonzero := true;
              [%"nterm" 0;].operator_text := "%"
              };
              binop__PLUS = do {
              [%"nterm" 0;].bin_oper := ( + );
              [%"nterm" 0;].rhs_must_be_nonzero := false;
              [%"nterm" 0;].operator_text := "+"
              };
              binop__SLASH = do {
              [%"nterm" 0;].bin_oper := fun a b → if b = 0 then 0 else a / b;
              [%"nterm" 0;].rhs_must_be_nonzero := true;
              [%"nterm" 0;].operator_text := "/"
              };
              binop__STAR = do {
              [%"nterm" 0;].bin_oper := fun a b → a * b;
              [%"nterm" 0;].rhs_must_be_nonzero := false;
              [%"nterm" 0;].operator_text := "*"
              };
              block1__BLOCK1 = [%"nterm" 0;].value_ := [%"nterm" 1;].value_;
              block2__BLOCK2 = [%"nterm" 0;].value_ := [%"nterm" 1;].value_;
              expr__BINOP = do {
              [%"nterm" 0;].value_ := [%"local" result;];
              [%"local" result;] :=
              [%"nterm" 1;].bin_oper [%"nterm" 2;].value_ [%"nterm" 3;].value_;
              [%"nterm" 0;].rpn :=
              [[%"nterm" 1;].operator_text :: [%"nterm" 3;].rpn];
              condition "rhs must be nonzero"
              (if [%"nterm" 1;].rhs_must_be_nonzero then
               0 <> [%"nterm" 3;].value_
              else true)
              };
              expr__INT = do {
              [%"nterm" 0;].value_ := [%"prim" 1;];
              [%"nterm" 0;].rpn :=
              [string_of_int [%"prim" 1;] :: [%"nterm" 0;].rpn]
              };
              expr__LET = do {
              [%"nterm" 0;].value_ := [%"nterm" 1;].value_;
              [%"nterm" 0;].rpn := [%"nterm" 1;].rpn
              };
              expr__REF = [%"nterm" 0;].value_ := [%"nterm" 1;].value_;
              expr__SEQ = do {
              [%"nterm" 0;].value_ := [%"nterm" 2;].value_;
              [%"nterm" 0;].rpn := [";" :: [%"nterm" 2;].rpn]
              };
              expr__UNOP = do {
              [%"nterm" 0;].value_ := [%"nterm" 1;].un_oper [%"nterm" 2;].value_;
              [%"nterm" 0;].rpn :=
              [[%"nterm" 1;].operator_text :: [%"nterm" 2;].rpn]
              };
              let_expr__LET_BINDING = do {
              [%"nterm" 0;].value_ := [%"nterm" 3;].value_;
              [%"nterm" 3;].rpn :=
              [Printf.sprintf "bind %s" [%"prim" 1;] :: [%"nterm" 2;].rpn];
              [%"nterm" 0;].env :=
              [([%"prim" 1;], [%"nterm" 2;].value_) ::
              [%"remote" (block1.env, let_expr.env);]];
              [%"nterm" 0;].freevars :=
              Std.union
              [%"constituents" {attributes = (ref_expr.freevars, let_expr.freevars); nodes = [%"nterm" 2;]};]
              (Std.except [%"prim" 1;]
                 [%"constituents" {attributes = (ref_expr.freevars, let_expr.freevars); nodes = [%"nterm" 3;]};])
              };
              prog__PROG = do {
              [%"nterm" 1;].env := [("x", 1); ("y", 2); ("z", 3); ("w", 4)];
              [%"nterm" 0;].value_ := [%"nterm" 1;].value_;
              [%"chainstart" 1;].rpn := [];
              [%"nterm" 0;].rpn_notation := List.rev [%"nterm" 1;].rpn;
              [%"nterm" 0;].freevars :=
              [%"constituents" {attributes = (ref_expr.freevars, let_expr.freevars); nodes = [%"nterm" 1;]};]
              };
              ref_expr__REF_EXPR = do {
              [%"nterm" 0;].value_ :=
              List.assoc [%"prim" 1;] [%"remote" (block1.env, let_expr.env);];
              [%"nterm" 0;].rpn := [[%"prim" 1;] :: [%"nterm" 0;].rpn];
              [%"nterm" 0;].freevars := [[%"prim" 1;]]
              };
              unop__UMINUS = do {
              [%"nterm" 0;].un_oper := fun x → -x;
              [%"nterm" 0;].operator_text := "unary-"
              };
              unop__UPLUS = do {
              [%"nterm" 0;].un_oper := fun x → x;
              [%"nterm" 0;].operator_text := "unary+"
              }}
              };] >>
    ("../simple_expr/test2.ag" |> file_contents |> pa_str_item)
}
;

value suite = "AG Syntax Test" >::: [
  "test_ag_elements"           >:: test_ag_elements
; "test_ag"           >:: test_ag
  ]
;

value _ = 
if not Sys.interactive.val then
  run_test_tt_main suite
else ()
;
