
open Pcaml ;
open Pa_ppx_utils ;
open Pa_ppx_base ;
open Ag_types ;
open Ppxutil ;

value rec find_mapi i f = fun [
    [] -> None
  | [x :: l] ->
     match f i x with [
         Some _ as result -> result
       | None -> find_mapi (i+1) f l
       ]
  ]
;
value find_mapi f l = find_mapi 0 f l ;

value fake_eq_loc (l1 : MLast.loc) l2 = True ;

type ag_element_t = [
    ATTRIBUTES of (MLast.loc[@equal fake_eq_loc;][@printer Pp_MLast.Ploc.pp;]) and list (string * (MLast.ctyp [@equal Reloc.eq_ctyp;][@printer Pp_MLast.pp_ctyp;]) * bool)
| RULE of
    (MLast.loc[@equal fake_eq_loc;][@printer Pp_MLast.Ploc.pp;]) and
  string and
  (option string * string) and
  list (option string * (MLast.ctyp [@equal Reloc.eq_ctyp;][@printer Pp_MLast.pp_ctyp;])) and
  list (MLast.expr [@equal Reloc.eq_expr;][@printer Pp_MLast.pp_expr;])
] [@@deriving (show,eq);]
;

value make_attribute_types loc el = do {
  let attribute_decls =
    el
    |> List.concat_map (fun [
        ATTRIBUTES _ l -> l
      | RULE _ _ _ _ _ -> []
      ])
    |> List.stable_sort Stdlib.compare in

  let attribute_types =
    attribute_decls
    |> List.map (fun (aname, aty, is_chain) ->
        let ty = if is_chain then <:ctyp< $aty$ [@chain] >> else aty in
        (<:patt< $lid:aname$ >>, <:expr< [%typ: $type:ty$] >>))
    |> List.stable_sort Stdlib.compare in
  let attribute_names = 
    attribute_decls
    |> List.map (fun (aname, aty, is_chain) -> aname) in
  
  if not (Std.distinct attribute_names) then do {
    let repeats = Std2.hash_list_repeats attribute_names in
    failwith Fmt.(str "attributes must have distinct names (found repeated): %a" (list Dump.string) repeats)
  } else ();
  if [] = attribute_types then <:expr< () >>
  else <:expr< { $list:attribute_types$ } >>
}
;

value node_to_ar primitive_types rule =
  let ((lhsna_opt, lhsty), types) = match rule with [ RULE _ _ tyna l _  -> (tyna, l) | _ -> assert False ] in
  fun [
    <:expr:< [%node 0;] >> ->
        <:expr< [%nterm 0;] >>

  | <:expr:< [%node $lid:id$;] >> when Some id = lhsna_opt ->
        <:expr< [%nterm 0;] >>

  | <:expr:< [%node $int:n$;] >> ->
      let i = int_of_string n in
      if is_primitive_ctyp0 primitive_types (snd (List.nth types (i-1))) then
        <:expr< [%prim $int:n$;] >>
      else
        <:expr< [%nterm $int:n$;] >>

  | <:expr:< [%node $lid:nid$;] >> ->
      match types |> find_mapi (fun i -> fun [
          (Some id', ty) when nid = id' -> Some (i+1, ty)
        | _ -> None
        ]) with [
        Some (n, ty) ->
          if is_primitive_ctyp0 primitive_types ty then
            <:expr< [%prim $int:string_of_int n$;] >>
          else
            <:expr< [%nterm $int:string_of_int n$;] >>
      | None -> failwith Fmt.(str "node with name %a was not found" Dump.string nid)
      ]
  | _ -> failwith "caught"
  ]
;

value rewrite_expr f e =
  let dt = Camlp5_migrate.make_dt () in
  let fallback_migrate_expr = dt.migrate_expr in
  let migrate_expr dt e = match f e with [
    x -> x
  | exception Failure "caught" -> fallback_migrate_expr dt e
  ] in
  let dt = { (dt) with Camlp5_migrate.migrate_expr = migrate_expr } in
  dt.migrate_expr dt e
;

value rewrite_eqn primitive_types rule e =
  rewrite_expr (node_to_ar primitive_types rule) e
;

value rule_replace_node primitive_types age = match age with [
  RULE loc prodna tyna tyl eqns ->
  let new_eqns = List.map (rewrite_eqn primitive_types age) eqns in
  RULE loc prodna tyna tyl new_eqns
  | _ -> assert False
]
;

value equation_to_node_attributes rule e = match rule with [
  RULE _ prodna tyna tyl eqns ->
  let acc = ref [] in
  let collect_expr e = match e with [
    <:expr:< [%nterm $int:n$;] . $lid:attrna$ >>  | <:expr:< [%node $int:n$;] . $lid:attrna$ >> -> do {
      let n = int_of_string n in
      if 0 = n then Std.push acc (snd tyna, attrna)
      else if n > List.length tyl then
        Ploc.raise loc (Failure Fmt.(str "rule_to_node_attributes: node-number %d out-of-bounds" n))
      else
        let tyid = match snd (List.nth tyl (n-1)) with [
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
      Std.push acc ((snd tyna,prodna), attrna) ;
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

value cleanup_equation eqn = match eqn with [
  <:expr< $_$ . val := $_$ >> | <:expr< $_$ . $lid:_$ := $_$ >> -> eqn
| <:expr:< $e1$ := $e2$ >> -> <:expr< $e1$ . val := $e2$ >>
| _ -> eqn
]
;

value rule_to_equations rule = match rule with [
  RULE _ prodna tyna tyl eqns ->
  ((snd tyna, prodna), List.map cleanup_equation eqns)
| _ -> assert False
]
;

value make_typedecls loc rules =
  rules
  |> List.filter_map (fun [
    ATTRIBUTES _ _ -> None
  | RULE _ prodna tyna tyl _ ->
    Some (snd tyna, (loc, prodna, List.map snd tyl))
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

value lid_to_expr loc x = <:expr< $lid:x$ >> ;

value make_node_attributes loc l =
  l
  |> List.filter (fun [ RULE _ _ _ _ _ -> True | _ -> False ])
  |> List.concat_map rule_to_node_attributes
  |> List.sort Stdlib.compare
  |> Std.nway_partition (fun (ty1, _) (ty2, _) -> ty1=ty2)
  |> List.sort Stdlib.compare
  |> List.map (fun l ->
      let tyna = fst (List.hd l) in
      let attrs = l
                  |> List.map snd
                  |> List.sort_uniq Stdlib.compare
                  |> List.stable_sort Stdlib.compare
                  |> List.map (lid_to_expr loc)
                  |> Ppxutil.convert_up_list_expr loc in
      (<:patt< $lid:tyna$ >>, attrs))
  |> (fun l ->
      if l = [] then <:expr< () >>
      else <:expr< { $list:l$ } >>)
;

value make_prod_attributes loc l =
  l
  |> List.filter (fun [ RULE _ _ _ _ _ -> True | _ -> False ])
  |> List.concat_map rule_to_prod_attributes
  |> List.sort Stdlib.compare
  |> Std.nway_partition (fun (ty1, _) (ty2, _) -> ty1=ty2)
  |> List.sort Stdlib.compare
  |> List.map (fun l ->
      let (tyna,prodna) = fst (List.hd l) in
      let key = Printf.sprintf "%s__%s" tyna prodna in
      let attrs = l
                  |> List.map snd
                  |> List.sort_uniq Stdlib.compare
                  |> List.stable_sort Stdlib.compare
                  |> List.map (lid_to_expr loc)
                  |> Ppxutil.convert_up_list_expr loc in
      (<:patt< $lid:key$ >>, attrs))
  |> (fun l ->
      if l = [] then <:expr< () >>
      else <:expr< { $list:l$ } >>)
;

value resolve_node_extension primitive_types = fun [
  RULE _ _ _ _ _  as r -> rule_replace_node primitive_types r
| e -> e
]
;

value make_attribution loc l =
  l
  |> List.filter (fun [ RULE _ _ _ _ _ -> True | _ -> False ])
  |> List.map rule_to_equations
  |> List.stable_sort Stdlib.compare
  |> List.map (fun ((tyna, prodna), l) ->
      let key = Printf.sprintf "%s__%s" tyna prodna in
      let e = match l with [
        [] -> <:expr< () >>
      | [e] -> e
      | _ -> <:expr< do { $list:l$ } >> ] in
      (<:patt< $lid:key$ >>, e)
    )
  |> (fun l -> <:expr< { $list:l$ } >>)
;

value make_deriving_attribute loc debug modname amodel prims axiom l =
  let optional = if debug then <:expr< True >> else <:expr< False >> in
  let l = List.map (resolve_node_extension prims) l in
  let primitive_types =
    prims
    |> List.map (lid_to_expr loc)
    |> Ppxutil.convert_up_list_expr loc  in
  let attribute_types = make_attribute_types loc l in
  let node_attributes = make_node_attributes loc l in
  let production_attributes = make_prod_attributes loc l in
  let attribution = make_attribution loc l in
  <:attribute_body< "deriving" ag {
                    optional = $optional$ ;
                    module_name = $uid:modname$
                    ; attribution_model = $amodel$
                    ; primitive_types = $primitive_types$
                    ; axiom = $lid:axiom$
                    ; attribute_types = $attribute_types$
                    ; node_attributes = $node_attributes$
                    ; production_attributes = $production_attributes$
                    ; attribution = $attribution$
                    } ; >>
;

value attach_attribute tdl attr =
  let attr = <:vala< attr >> in
  let (last_td, tdl) = Std.sep_last tdl in
  let last_td = match last_td with [
    <:type_decl:< $tp:(loc,tyna)$ = $tk$ >> ->
    <:type_decl< $tp:(loc,tyna)$ = $tk$ $itemattrs:[attr]$ >>
  ] in
  tdl@[last_td]
;

value make_ag_str_item loc debug modname amodel prims axiom l = do {
  let tdl = make_typedecls loc l in
  let attr = make_deriving_attribute loc debug modname amodel prims axiom l in
  let manifest_tdl = tdl |> List.map (fun [
      <:type_decl:< $lid:tn$ $list:pl$ = $ty$ >> when is_generative_type ty -> <:type_decl:< $lid:tn$ $list:pl$ = T . $lid:tn$ == $ty$ >>
    | td -> td
    ]) in
  let attr_tdl = attach_attribute manifest_tdl attr in
  <:str_item<
    declare
    module T = struct
      type $list:tdl$ ;
    end ;
    type $list:attr_tdl$ ;
    end
  >>
}
;

value attribute_grammar = Grammar.Entry.create gram "attribute_grammar";
value attribute_grammar_body = Grammar.Entry.create gram "attribute_grammar_body";
value attribute_grammar_element = Grammar.Entry.create gram "attribute_grammar_element";

value check_id_colon_f = (fun strm ->
    match Stream.npeek 2 strm with
      [ [("LIDENT", _); ("", ":")] -> ()
      | _ -> raise Stream.Failure ])
;

value check_id_colon =
  Grammar.Entry.of_parser gram "check_id_colon"
    check_id_colon_f
;

EXTEND
  GLOBAL: check_id_colon attribute_grammar_body attribute_grammar_element
    attribute_grammar expr str_item ;

  str_item: [ [
    (debug, modname, amodel, prims, axiom, l) = attribute_grammar ->
    make_ag_str_item loc debug modname amodel prims axiom l
    ] ] ;

  attribute_grammar: [ [
      "ATTRIBUTE_GRAMMAR" ;
      (debug, modname, amodel, prims, axiom, l) = attribute_grammar_body ;
      "END" -> (debug, modname, amodel, prims, axiom, l)
    | "ATTRIBUTE_GRAMMAR" ; "{" ;
      (debug, modname, amodel, prims, axiom, l) = attribute_grammar_body ;
      "}" -> (debug, modname, amodel, prims, axiom, l)
    ] ] ;

  attribute_grammar_body: [ [
      debug = [ "DEBUG" ; b = [ UIDENT "True" -> True | UIDENT "False" -> False ] ; ";" -> b | -> False ] ;
      "MODULE" ; modname = UIDENT ; ";" ;
      "ATTRIBUTION_MODEL" ; amodel = expr ; ";" ;
      prims = [ "PRIMITIVES" ; prims = LIST1 LIDENT SEP "," ; ";" -> prims | -> [] ] ;
      "AXIOM" ; axiom = LIDENT ; ";" ;
      l = LIST1 attribute_grammar_element
      -> (debug, modname, amodel, prims, axiom, l)
    ] ] ;

  named_typename: [ [
    id = LIDENT ; ":" ; ty = LIDENT -> (Some id, ty)
  | id = LIDENT -> (None, id)
  ] ] ;

  named_type: [ [
    check_id_colon ; id = LIDENT ; ":" ; ty = ctyp -> (Some id, ty)
  | ty = ctyp -> (None, ty)
  ] ] ;

  attribute_grammar_element: [ [
      "ATTRIBUTE" ; aname = LIDENT ; ":" ; ty = ctyp ; ";" ->
      ATTRIBUTES loc [(aname, ty, False)]
    | "ATTRIBUTES" ; l = LIST1 [ aname = LIDENT ; ":" ; ty = ctyp ; ";" -> (aname, ty, False) ] ; "END" ; ";" ->
      ATTRIBUTES loc l
    | "ATTRIBUTES" ; "{" ; l = LIST1 [ aname = LIDENT ; ":" ; ty = ctyp ; ";" -> (aname, ty, False) ] ; "}" ; ";" ->
      ATTRIBUTES loc l
    | "CHAIN" ; aname = LIDENT ; ":" ; ty = ctyp ; ";" ->
      ATTRIBUTES loc [(aname, ty, True)]
    | "RULE" ; cid = UIDENT ; ":" ; naty = named_typename ;
      tl = [ ":=" ; tl = LIST0 named_type SEP "and" -> tl | -> [] ];
      "COMPUTE" ;
      comps = LIST1 [ e = expr LEVEL ":=" ; ";" -> e] ;
      "END" ; ";" ->
      RULE loc cid naty tl comps
    | "RULE" ; cid = UIDENT ; ":" ; naty = named_typename ;
      tl = [ ":=" ; tl = LIST0 named_type SEP "and" -> tl | -> [] ];
      e = expr ; ";" ->
      let comps = match e with [
        <:expr< do { $list:l$ } >> -> l
      | _ -> [e]
      ] in
      RULE loc cid naty tl comps
    ] ] ;

  expr: LEVEL "simple" [
    [
      "$" ; "[" ; n = INT ; "]" -> <:expr< [%node $int:n$;] >>
    | "$" ; "[" ; id = LIDENT ; "]" -> <:expr< [%node $lid:id$;] >>

    | "$" ; id = LIDENT -> <:expr< [%local $lid:id$;] >>
    | "INCLUDING" ; e = arefs -> <:expr< [%remote $exp:e$ ;] >>
    | "CONCAT" ; e1 = arefs ; "IN" ; e2 = nodes -> 
      <:expr< [%constituents { attributes = $e1$ ; nodes = $e2$ } ;] >>
    | "CONCAT" ; e1 = arefs ; "IN" ; e2 = nodes ; "SHIELD" ; e3 = nonterminals -> 
      <:expr< [%constituents { attributes = $e1$ ; nodes = $e2$ ; shield = $e3$ } ;] >>
    ]
  ] ;

  dummy:
    [ [ → () ] ]
  ;

  expr: LEVEL ":=" [ [
    "CHAINSTART" ; "$" ; "[" ; n = INT ; "]" ; "." ; attrna = LIDENT; ":=" ; e2 = SELF ; dummy ->
    <:expr< [%chainstart $int:n$;] . $lid:attrna$ := $e2$ >>
  | "CHAINSTART" ; "$" ; "[" ; id = LIDENT ; "]" ; "." ; attrna = LIDENT; ":=" ; e2 = SELF ; dummy ->
    <:expr< [%chainstart $lid:id$;] . $lid:attrna$ := $e2$ >>
  ] ] ;

  arefs: [ [ (nt, a) = aref -> <:expr< $lid:nt$ . $lid:a$ >>
           | "(" ; h = aref ; "," ; l = LIST1 aref SEP ","; ")" ->
             let l = [h::l] |> List.map (fun (nt,a) -> <:expr< $lid:nt$ . $lid:a$ >>) in
             <:expr< ( $list:l$ ) >>
           ] ] ;

  aref: [ [ nt = LIDENT ; "." ; a = LIDENT -> (nt, a) ] ] ;

  node: [ [
      "$" ; "[" ; n = INT ; "]" -> <:expr< [%node $int:n$ ;] >>
    | "$" ; "[" ; id = LIDENT ; "]" -> <:expr< [%node $lid:id$ ;] >>
    ] ] ; 
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
