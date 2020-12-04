
open Pcaml ;
open Pa_ppx_utils ;
open Pa_ppx_base ;
open Ag_types ;

value fake_eq_loc (l1 : MLast.loc) l2 = True ;

type ag_element_t = [
    ATTRIBUTES of (MLast.loc[@equal fake_eq_loc;][@printer Pp_MLast.Ploc.pp;]) and list (string * (MLast.ctyp [@equal Reloc.eq_ctyp;][@printer Pp_MLast.pp_ctyp;]) * bool)
| RULE of (MLast.loc[@equal fake_eq_loc;][@printer Pp_MLast.Ploc.pp;]) and string and string and list (MLast.ctyp [@equal Reloc.eq_ctyp;][@printer Pp_MLast.pp_ctyp;]) and list (MLast.expr [@equal Reloc.eq_expr;][@printer Pp_MLast.pp_expr;])
] [@@deriving (show,eq);]
;

value make_attribute_types loc el = do {
  let attribute_types =
    el
    |> List.concat_map (fun [
        ATTRIBUTES _ l -> l
      | RULE _ _ _ _ _ -> []
      ])
    |> List.map (fun (aname, aty, is_chain) ->
        let ty = if is_chain then <:ctyp< $aty$ [@chain] >> else aty in
        (<:patt< $lid:aname$ >>, <:expr< [%typ: $type:aty$] >>)) in
  assert (Std.distinct (List.map fst attribute_types)) ;
  attribute_types
}
;

value child_to_ar rule =
  let types = match rule with [ RULE _ _ _ l _  -> l | _ -> assert False ] in
  fun [
    <:expr:< [%child $int:n$;] >> ->
      let i = int_of_string n in
      if is_builtin_ctyp (List.nth types (i-1)) then
        <:expr< [%prim $int:n$;] >>
      else
        <:expr< [%nterm $int:n$;] >>
    | _ -> failwith "caught"
  ]
;

value rewrite_expr f e =
  let dt = Camlp5_migrate.make_dt () in
  let fallback_migrate_expr = dt.migrate_expr in
  let migrate_expr dt e = match f e with [
    x -> x
  | exception Failure _ -> fallback_migrate_expr dt e
  ] in
  let dt = { (dt) with Camlp5_migrate.migrate_expr = migrate_expr } in
  dt.migrate_expr dt e
;

value rewrite_eqn rule e =
  rewrite_expr (child_to_ar rule) e
;

value rule_replace_child age = match age with [
  RULE loc prodna tyna tyl eqns ->
  let new_eqns = List.map (rewrite_eqn age) eqns in
  RULE loc prodna tyna tyl new_eqns
  | _ -> assert False
]
;

value equation_to_node_attributes rule e = match rule with [
  RULE _ prodna tyna tyl eqns ->
  let acc = ref [] in
  let collect_expr e = match e with [
    <:expr:< [%nterm $int:n$;] . $lid:attrna$ >> -> do {
      let n = int_of_string n in
      if 0 = n then Std.push acc (tyna, attrna)
      else if n > List.length tyl then
        Ploc.raise loc (Failure Fmt.(str "rule_to_node_attributes: node-number %d out-of-bounds" n))
      else
        let tyid = match List.nth tyl (n-1) with [
          <:ctyp< $lid:id$ >> -> id
        | ty ->
          Ploc.raise (MLast.loc_of_ctyp ty)
            (Failure Fmt.(str "rule_to_node_attributes: unrecognized nonterminal type %a"
                         Pp_MLast.pp_ctyp ty))
        ] in
          Std.push acc (tyid, attrna) ;
      e
    }

  | e -> failwith "caught"
  ] in do {
    ignore(rewrite_expr collect_expr e) ;
    acc.val
  }
| _ -> assert False
]
;

value rule_to_node_attributes rule = match rule with [
  RULE _ prodna tyna tyl eqns ->
    eqns
    |> List.concat_map (equation_to_node_attributes rule)
    |> List.sort_uniq Stdlib.compare

| _ -> assert False
]
;

value equation_to_prod_attributes rule e = match rule with [
  RULE _ prodna tyna tyl eqns ->
  let acc = ref [] in
  let collect_expr e = match e with [
    <:expr:< [%local $lid:attrna$;] >> -> do {
      Std.push acc ((tyna,prodna), attrna) ;
      e
    }

  | e -> failwith "caught"
  ] in do {
    ignore(rewrite_expr collect_expr e) ;
    acc.val
  }
| _ -> assert False
]
;

value rule_to_prod_attributes rule = match rule with [
  RULE _ prodna tyna tyl eqns ->
    eqns
    |> List.concat_map (equation_to_prod_attributes rule)
    |> List.sort_uniq Stdlib.compare

| _ -> assert False
]
;

value make_typedecls loc rules =
  rules
  |> List.filter_map (fun [
    ATTRIBUTES _ _ -> None
  | RULE _ prodna tyna tyl _ ->
    Some (tyna, (loc, prodna, tyl))
  ])
  |> List.sort Stdlib.compare
  |> Std.nway_partition (fun (ty1, _) (ty2, _) -> ty1=ty2)
  |> List.sort Stdlib.compare
  |> List.map (fun l ->
      let tyna = fst (List.hd l) in
      let branches =
        l
        |> List.map snd
        |> List.stable_sort Stdlib.compare
        |> List.map (fun (loc, cid, tyl) ->
          <:constructor< $uid:cid$ of $list:tyl$ >>) in
      <:type_decl< $lid:tyna$ = [ $list:branches$ ] >>
    )
;

value make_ag_str_item loc modname amodel axiom l = do {
  let attribute_types = make_attribute_types loc l in
  let tdl = make_typedecls loc l in
  <:str_item< type $list:tdl$ >>
}
;

value attribute_grammar_body = Grammar.Entry.create gram "attribute_grammar_body";
value attribute_grammar_element = Grammar.Entry.create gram "attribute_grammar_element";

EXTEND
  GLOBAL: attribute_grammar_body attribute_grammar_element expr str_item ;

  str_item: [ [
      "ATTRIBUTE_GRAMMAR" ;
      (modname, amodel, axiom, l) = attribute_grammar_body ;
      "END" -> make_ag_str_item loc modname amodel axiom l
    ] ] ;

  attribute_grammar_body: [ [
      "MODULE" ; modname = UIDENT ; ";" ;
      "ATTRIBUTION_MODEL" ; amodel = expr ; ";" ;
      "AXIOM" ; axiom = LIDENT ; ";" ;
      l = LIST1 attribute_grammar_element
      -> (modname, amodel, axiom, l)
    ] ] ;

  attribute_grammar_element: [ [
      "ATTRIBUTE" ; aname = LIDENT ; ":" ; ty = ctyp ; ";" ->
      ATTRIBUTES loc [(aname, ty, False)]
    | "ATTRIBUTES" ; l = LIST1 [ aname = LIDENT ; ":" ; ty = ctyp ; ";" -> (aname, ty, False) ] ; "END" ; ";" ->
      ATTRIBUTES loc l
    | "CHAIN" ; aname = LIDENT ; ":" ; ty = ctyp ; ";" ->
      ATTRIBUTES loc [(aname, ty, True)]
    | "RULE" ; cid = UIDENT ; ":" ; tyna = LIDENT ;
      tl = [ ":=" ; tl = LIST0 ctyp SEP "and" -> tl | -> [] ];
      "COMPUTE" ;
      comps = LIST1 [ e = expr LEVEL ":=" ; ";" -> e] ;
      "END" ; ";" ->
      RULE loc cid tyna tl comps
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

  node: [ [ "$" ; "[" ; n = INT ; "]" -> <:expr< [%child $int:n$ ;] >> ] ] ; 
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
