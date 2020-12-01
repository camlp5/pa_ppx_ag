
open Pcaml ;
open Pa_ppx_utils ;
open Pa_ppx_base ;

type ag_element_t = [
  ATTRIBUTES of list (string * (MLast.ctyp [@equal Reloc.eq_ctyp;][@printer Pp_MLast.pp_ctyp;]) * bool)
| RULE of string and string and list (MLast.ctyp [@equal Reloc.eq_ctyp;][@printer Pp_MLast.pp_ctyp;]) and list (MLast.expr [@equal Reloc.eq_expr;][@printer Pp_MLast.pp_expr;])
] [@@deriving (show,eq);]
;

value make_attribute_types loc el = do {
  let attribute_types =
    el
    |> List.concat_map (fun [
        ATTRIBUTES l -> l
      | RULE _ _ _ _ -> []
      ])
    |> List.map (fun (aname, aty, is_chain) ->
        let ty = if is_chain then <:ctyp< $aty$ [@chain] >> else aty in
        (<:patt< $lid:aname$ >>, <:expr< [%typ: $type:aty$] >>)) in
  assert (Std.distinct (List.map fst attribute_types)) ;
  attribute_types
}
;

value make_ag_str_item loc modname amodel axiom l = do {
  let attribute_types = make_attribute_types loc l in
  <:str_item< declare end >>
}
;

value attribute_grammar_body = Grammar.Entry.create gram "attribute_grammar_body";
value attribute_grammar_element = Grammar.Entry.create gram "attribute_grammar_element";

EXTEND
  GLOBAL: attribute_grammar_body attribute_grammar_element expr str_item ;

  str_item: [ [
      "ATTRIBUTE_GRAMMAR" ;
      ag = attribute_grammar_body ;
      "END" -> ag
    ] ] ;

  attribute_grammar_body: [ [
      "MODULE" ; modname = UIDENT ; ";" ;
      "ATTRIBUTION_MODEL" ; amodel = expr ; ";" ;
      "AXIOM" ; axiom = LIDENT ; ";" ;
      l = LIST1 attribute_grammar_element
      -> make_ag_str_item loc modname amodel axiom l
    ] ] ;

  attribute_grammar_element: [ [
      "ATTRIBUTE" ; aname = LIDENT ; ":" ; ty = ctyp ; ";" ->
      ATTRIBUTES [(aname, ty, False)]
    | "ATTRIBUTES" ; l = LIST1 [ aname = LIDENT ; ":" ; ty = ctyp ; ";" -> (aname, ty, False) ] ; "END" ; ";" ->
      ATTRIBUTES l
    | "CHAIN" ; aname = LIDENT ; ":" ; ty = ctyp ; ";" ->
      ATTRIBUTES [(aname, ty, True)]
    | "RULE" ; cid = UIDENT ; ":" ; tyna = LIDENT ; ":=" ; tl = LIST0 ctyp SEP "and" ;
      "COMPUTE" ;
      comps = LIST1 [ e = expr LEVEL ":=" ; ";" -> e] ;
      "END" ; ";" ->
      RULE cid tyna tl comps
    ] ] ;

  expr: LEVEL "simple" [
    [
      "$" ; "[" ; n = INT ; "]" ->
      if 0 = int_of_string n then 
        <:expr< [%nterm $int:n$;] >>
      else <:expr< [%child $int:n$;] >>

    | "$" ; id = LIDENT -> <:expr< [%local $lid:id$;] >>
    | "INCLUDING" ; e = arefs -> <:expr< [%remote $exp:e$ ;] >>
    | "CONCAT" ; e1 = arefs ; "IN" ; e2 = nodes -> 
      <:expr< [%constituents { attributes = $e1$ ; nodes = $e2$ } ;] >>
    | "CONCAT" ; e1 = arefs ; "IN" ; e2 = nodes ; "SHIELD" ; e3 = nonterminals -> 
      <:expr< [%constituents { attributes = $e1$ ; nodes = $e2$ ; shield = $e3$ } ;] >>
    ]
  ] ;

  arefs: [ [ (nt, a) = aref -> <:expr< $lid:nt$ . $lid:a$ >>
           | "(" ; h = aref ; "," ; l = LIST1 aref SEP ","; ")" ->
             let l = [h::l] |> List.map (fun (nt,a) -> <:expr< $lid:nt$ . $lid:a$ >>) in
             <:expr< ( $list:l$ ) >>
           ] ] ;

  aref: [ [ nt = LIDENT ; "." ; a = LIDENT -> (nt, a) ] ] ;

  node: [ [ "$" ; n = INT -> <:expr< [%child $int:n$ ;] >> ] ] ; 
  nodes: [ [ e = node -> e
           | "(" ; h = node ; "," ; l = LIST1 node SEP "," ; ")" ->
             <:expr< ( $list:[h::l]$ ) >>
           ] ] ;
  nonterminal: [ [ n = LIDENT -> <:expr< $lid:n$ >> ] ] ; 
  nonterminals: [ [ e = nonterminal -> e
           | "(" ; h = nonterminal ; "," ; l = LIST1 nonterminal SEP "," ; ")" ->
             <:expr< ( $list:[h::l]$ ) >>
           ] ] ;
END;
