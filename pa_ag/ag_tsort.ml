(* camlp5r *)
(* ag_tsort.ml,v *)

open Asttools;
open MLast;
open Pa_ppx_base ;
open Pa_passthru ;
open Ppxutil ;
open Surveil ;
open Pa_deriving_base ;
open Pa_ppx_utils ;
open Ag_types ;

value node_hash_module nt = Printf.sprintf "HTAttr_%s" nt ;
value node_constructor nt = Printf.sprintf "Node_%s" nt ;
value attr_constructor ?{prodname} attrna =
  match prodname with [
    None -> Printf.sprintf "Attr_%s" attrna
  | Some name -> Printf.sprintf "Attr_%s__%s" name attrna
  ]
;
value preprocess_fname nt = Printf.sprintf "preprocess_%s" nt ;
value parent_accessor_name nt = Printf.sprintf "%s__parent" nt ;
value parent_setter_name nt = Printf.sprintf "%s__set_parent" nt ;
value parent_isset_name nt = Printf.sprintf "%s__isset_parent" nt ;
value attr_accessor_name nt attrna = Printf.sprintf "%s__%s" nt attrna ;
value attr_setter_name nt attrna = Printf.sprintf "%s__set_%s" nt attrna ;
value attr_isset_name nt attrna = Printf.sprintf "%s__isset_%s" nt attrna ;

value (wrapper_module_longid, wrapper_module_module_expr) =
let loc = Ploc.dummy in
  (<:longident< Pa_ppx_ag_runtime.Attributes >>,
   <:module_expr< Pa_ppx_ag_runtime.Attributes >>)
;

value nonterminal_hashtable_declaration memo (name, attributes) =
  let open AGOps.NTOps in
  let open AG in
  let ag = memo.ag in
  let loc = ag.loc in
  match Demarshal.parse_prodname loc name with [
    {PN.nonterm_name=nt; case_name = None} ->
    Some (Reloc.str_item (fun _ -> Ploc.dummy) 0
            <:str_item< module $uid:node_hash_module nt$ = Hashtbl.Make(struct
                               type t = $lid:nt$ ;
                               open $wrapper_module_module_expr$ ;
                               value equal a b = a.id = b.id ;
                               value hash x = x.id ;
                             end) >>)
  | {PN.case_name = Some _} -> None
  ]
;

value disambiguated_attribute_name name attrna =
 Printf.sprintf "%s__%s" name attrna
;

value attributes_type_declaration memo (name, attribute_names) =
  let open AGOps.NTOps in
  let open AG in
  let ag = memo.ag in
  let loc = ag.loc in
  match (Demarshal.parse_prodname loc name) with [
    {PN.nonterm_name=nt; case_name = Some _} -> None

  | {PN.nonterm_name=nt; case_name = None} ->
    let attr_type_name = Printf.sprintf "%s_hashed_attributes_t" name in
    let dis_parent = disambiguated_attribute_name name "parent" in
    let ltl = [(loc, dis_parent, False, <:ctyp< $uid:node_hash_module nt$ . t (Node.t * int) >>, <:vala< [] >>)] in
    Some <:str_item< type $lid:attr_type_name$ = { $list:ltl$ } >>
  ]
;

value master_attribute_type_declaration memo =
  let open AGOps.NTOps in
  let open AG in
  let ag = memo.ag in
  let loc = ag.loc in
  let ltl = (ag.node_attributes@ag.production_attributes) |> List.filter_map (fun (name, _) ->
      match Demarshal.parse_prodname loc name with [
        {PN.case_name=Some _} -> None
      | {PN.case_name=None} ->
        let attr_type_name = Printf.sprintf "%s_hashed_attributes_t" name in
        Some (loc, name, False, <:ctyp< $lid:attr_type_name$ >>, <:vala< [] >>)
      ]) in
  <:str_item< type attributes_t = { $list:ltl$ } >>
;

value attribute_table_constructor_entry memo (name, al) =
  let open AGOps.NTOps in
  let open AG in
  let ag = memo.ag in
  let loc = ag.loc in
  match (Demarshal.parse_prodname loc name) with [
    {PN.nonterm_name=nt; case_name = Some _} -> None

  | {PN.nonterm_name=nt; case_name = None} ->
    let dis_parent = disambiguated_attribute_name name "parent" in
    let lel = [(<:patt< $lid:dis_parent$ >>, <:expr< $uid:node_hash_module nt$ . create 23 >>)] in
    Some (<:patt< $lid:name$ >>, <:expr< { $list:lel$ } >>)
  ]
;

value master_attribute_constructor_declaration memo =
  let open AGOps.NTOps in
  let open AG in
  let ag = memo.ag in
  let loc = ag.loc in
  let lel = (ag.node_attributes@ag.production_attributes) |> List.filter_map (attribute_table_constructor_entry memo) in do {
    assert (lel <> []) ;
    Reloc.str_item (fun _ -> Ploc.dummy) 0
      <:str_item< value mk () = { $list:lel$ } >>
  }
;

value parent_accessor_bindings memo (name, _) =
  let open AGOps.NTOps in
  let open AG in
  let ag = memo.ag in
  let loc = ag.loc in
  let dis_parent = disambiguated_attribute_name name "parent" in
  match Demarshal.parse_prodname loc name with [
    {PN.case_name = Some _} -> []
  | {PN.nonterm_name=nt; PN.case_name = None} ->
    [(<:patt< $lid:parent_accessor_name nt$ >>,
      <:expr< fun attrs -> fun node ->
                  $uid:node_hash_module nt$ . find attrs . $lid:nt$ . $lid:dis_parent$ node >>,
      <:vala< [] >>) ;
     (<:patt< $lid:parent_setter_name nt$ >>,
      <:expr< fun attrs -> fun node -> fun p ->
                  $uid:node_hash_module nt$ . add attrs . $lid:nt$ . $lid:dis_parent$ node p >>,
      <:vala< [] >>) ;
     (<:patt< $lid:parent_isset_name nt$ >>,
      <:expr< fun attrs -> fun node ->
                  $uid:node_hash_module nt$ . mem attrs . $lid:nt$ . $lid:dis_parent$ node >>,
      <:vala< [] >>)]
  ]
;

value attr_accessor_bindings memo (name, attribute_names) =
  let open AGOps.NTOps in
  let open AG in
  let ag = memo.ag in
  let loc = ag.loc in
  let pn = Demarshal.parse_prodname loc name in
  attribute_names |> List.concat_map (fun attrna ->
      [(<:patt< $lid:attr_accessor_name name attrna$ >>,
        match pn.PN.case_name with [
          None ->
          <:expr< fun attrs -> fun node ->
                  match node.attributes. $lid:attr_accessor_name name attrna$ with [
                  Some v -> v | None -> failwith $str:attr_accessor_name name attrna$
                  ] >>
        | _ ->
          <:expr< fun attrs -> fun prod_attrs ->
                  match prod_attrs. $lid:attr_accessor_name name attrna$ with [
                  Some v -> v | None -> failwith $str:attr_accessor_name name attrna$
                  ] >>
        ],
          <:vala< [] >>) ;

       (<:patt< $lid:attr_setter_name name attrna$ >>,
        match pn.PN.case_name with [ 
          None ->
          <:expr< fun attrs -> fun node -> fun v ->
                  node.attributes. $lid:attr_accessor_name name attrna$ := Some v >>
        | _ ->
          <:expr< fun attrs -> fun prod_attrs -> fun v ->
                  prod_attrs. $lid:attr_accessor_name name attrna$ := Some v >>
        ],
          <:vala< [] >>) ;
       (<:patt< $lid:attr_isset_name name attrna$ >>,
        match pn.PN.case_name with [
          None ->
          <:expr< fun attrs -> fun node ->
                  node.attributes. $lid:attr_accessor_name name attrna$ <> None >>
        | _ ->
          <:expr< fun attrs -> fun prod_attrs ->
                  prod_attrs. $lid:attr_accessor_name name attrna$ <> None >>
        ],
          <:vala< [] >>)]
    )
;

value node_attribute_table_declaration memo =
  let open AGOps.NTOps in
  let open AG in
  let ag = memo.ag in
  let loc = ag.loc in
  let l =
    (ag.node_attributes |> List.filter_map (nonterminal_hashtable_declaration memo))@
    ((ag.node_attributes@ag.production_attributes) |> List.filter_map (attributes_type_declaration memo))@
    [master_attribute_type_declaration memo]@
    [master_attribute_constructor_declaration memo]@
    [let parent_accessor_bindings = ag.node_attributes |> List.concat_map (parent_accessor_bindings memo) in
     let attr_accessor_bindings = (ag.node_attributes@ag.production_attributes) |> List.concat_map (attr_accessor_bindings memo) in
     <:str_item< value $list:parent_accessor_bindings@attr_accessor_bindings$ >>
    ] in
  Reloc.str_item (fun _ -> Ploc.dummy) 0
  <:str_item< module AttrTable = struct
    open $wrapper_module_module_expr$ ;
    declare $list:l$ end ;
    end >>
;

value node_module_declaration memo =
  let open AGOps.NTOps in
  let open AG in
  let ag = memo.ag in
  let loc = ag.loc in
  let branches = ag.nonterminals |> List.map (fun nt ->
      (loc, <:vala< node_constructor nt >>, <:vala< [<:ctyp< $lid:nt$ >>] >>, <:vala< None >>, <:vala< [] >>)
    ) in
  let eqbranches = ag.nonterminals |> List.map (fun nt ->
    let nodecons = node_constructor nt in
    (<:patt< ($uid:nodecons$ x, $uid:nodecons$ y) >>, <:vala< None >>, <:expr< x.id = y.id >>)
  ) in
  let eqbranches = eqbranches @ [
    (<:patt< _ >>, <:vala< None >>, <:expr< False >>)
  ] in
  let hashbranches = ag.nonterminals |> List.map (fun nt ->
    let nodecons = node_constructor nt in
    (<:patt< ($uid:nodecons$ x) >>, <:vala< None >>, <:expr< x.id >>)
  ) in
  let cmpbranches = ag.nonterminals |> List.map (fun nt ->
    let nodecons = node_constructor nt in
    (<:patt< ($uid:nodecons$ x, $uid:nodecons$ y) >>, <:vala< None >>, <:expr< Stdlib.compare x.id y.id >>)
  ) in
  let cmpbranches = cmpbranches @ [
    (<:patt< (x,y) >>, <:vala< None >>, <:expr< Stdlib.compare (Obj.tag (Obj.repr x)) (Obj.tag (Obj.repr y)) >>)
  ] in

  Reloc.str_item (fun _ -> Ploc.dummy) 0
  <:str_item< module Node = struct
                type t = [ $list:branches$ ] ;
                value equal x y = match (x,y) with [ $list:eqbranches$ ] ;
                value compare x y = match (x,y) with [ $list:cmpbranches$ ] ;
                value hash = fun [ $list:hashbranches$ ] ;
              end >>
;

value attr_type_declaration memo =
  let open AGOps.NTOps in
  let open AG in
  let ag = memo.ag in
  let loc = ag.loc in
  let branches =
    (ag.node_attributes@ag.production_attributes)
    |> List.map (fun (name, al) ->
        match Demarshal.parse_prodname loc name with [
          {PN.case_name=None} -> al |> List.map (fun a -> (None, a))
        | {PN.case_name=Some _} -> al |> List.map (fun a -> (Some name, a))
        ])
    |> List.concat
    |> Std2.hash_uniq
    |> List.sort Stdlib.compare
    |> List.map (fun [
        (None, attrna) ->
        (loc, <:vala< attr_constructor attrna >>, <:vala< [] >>, <:vala< None >>, <:vala< [] >>)
      | (Some prodname, attrna) ->
        (loc, <:vala< attr_constructor ~{prodname=prodname} attrna >>, <:vala< [] >>, <:vala< None >>, <:vala< [] >>)
      ]) in
  <:str_item< type attrname_t = [ $list:branches$ ] >>
;

value nodeattr_type_declaration memo =
  let open AGOps.NTOps in
  let open AG in
  let ag = memo.ag in
  let loc = ag.loc in
  Reloc.str_item (fun _ -> Ploc.dummy) 0
  <:str_item<
    module NodeAttrVertex = struct
      type t = option (Node.t * attrname_t) ;
      value equal a b = match (a,b) with [
                            (None, None) -> True
                          | (Some (n1, a1), Some (n2, a2)) -> Node.equal n1 n2 && a1 = a2
                          | _ -> False ];
      value compare a b = match (a,b) with [
                              (None, None) -> 0
                            | (None, Some _) -> -1
                            | (Some _, None) -> 1
                            | (Some (n1, a1), Some (n2, a2)) ->
                               match Node.compare n1 n2 with [
                                   0 -> Stdlib.compare a1 a2
                                 | x -> x
                                 ] ] ;
      value hash = fun [ None -> 0 | Some (n,a) -> Node.hash n + Hashtbl.hash a ] ;
    end
  >>
;

value lookup_parent_declaration memo =
  let open AGOps.NTOps in
  let open AG in
  let ag = memo.ag in
  let loc = ag.loc in
  let branches = ag.nonterminals |> List.map (fun nt ->
      (<:patt< Node . $uid:node_constructor nt$ node >>, <:vala< None >>,
       <:expr< AttrTable. $lid:parent_accessor_name nt$ attrs node >>)
    ) in
  Reloc.str_item (fun _ -> Ploc.dummy) 0
  <:str_item< value lookup_parent = fun attrs -> fun [ $list:branches$ ] >>
;

value actual_dep_function_declarations memo =
  let open AGOps.NTOps in
  let open AG in
  let ag = memo.ag in
  let loc = ag.loc in
  (ag.productions |> List.map (fun (nt, pl) ->
       let branches = pl |> List.map (fun p ->
           let deps = p |> P.ddp in
           let lhs_list = p.P.typed_equations |> List.map TAEQ.lhs in
           let indeps = Std.subtract lhs_list (deps |> List.concat_map (fun (a,b) -> [a;b])) in
           let aref_to_exp = fun [
             TAR.NT (TNR.PARENT tyname) aname ->
             <:expr< (Node . $uid:node_constructor tyname$ lhs, $uid:attr_constructor aname$) >>

           | TAR.NT ((TNR.CHILD tyname i) as nr) aname ->
              let v = match LMap.assoc nr p.P.rev_patt_var_to_noderef with [
                x -> x
              | exception Not_found ->
                Ploc.raise loc
                  (Failure "actual_dep_function_declarations: cannot map attribute-ref back to variable")
              ] in
              <:expr< (Node . $uid:node_constructor tyname$ $lid:v$, $uid:attr_constructor aname$) >>

           | TAR.PROD pn aname ->
             <:expr< (Node . $uid:node_constructor nt$ lhs, $uid:attr_constructor ~{prodname=PN.unparse pn} aname$) >>

           | _ -> assert False
           ] in
           let deps = List.map (fun (a, b) -> (aref_to_exp a, aref_to_exp b)) deps in
           let indeps = List.map aref_to_exp indeps in
           let depacts = deps |> List.map (fun (a,b) -> <:expr< Std.push acc (Some $a$, Some $b$) >>) in
           let indepacts = indeps |> List.map (fun a -> <:expr< Std.push acc (None, Some $a$) >>) in
           let child_node_acts = p.P.rev_patt_var_to_noderef |> LMap.toList |> List.filter_map (fun [
             (TNR.CHILD tyname i, v) ->
             let abs_childnum = match LMap.assoc v p.P.patt_var_to_childnum with [
               x -> x | exception Not_found -> assert False
             ] in
             let fname = preprocess_fname tyname in
             Some <:expr< do {
                          AttrTable . $lid:parent_setter_name tyname$
                            attrs
                            $lid:v$
                            (Node . $uid:node_constructor nt$ lhs, $int:string_of_int abs_childnum$) ;
                          $lid:fname$ attrs acc $lid:v$
                          } >>
           | (TNR.PRIM _ _, _) -> None
           ]) in
           let child_node_acts = child_node_acts@[ <:expr< () >> ] in
           (p.P.patt, <:vala< None >>,
            <:expr< do { $list:depacts@indepacts@child_node_acts$ } >>)
         ) in
       (<:patt< $lid:preprocess_fname nt$ >>,
        Reloc.expr (fun _ -> Ploc.dummy) 0
        <:expr< fun attrs -> fun acc -> fun lhs -> match lhs.node with [ $list:branches$ ] >>,
        <:vala< [] >>)
     ))
;

(** compile a typed-equation into an expression

    The context will be one in which "attrs" is the global
   attribute-table record, "lhs" is the parent node, and "v_i" (i > 0)
   are child nodes.

*)
value lookup_tnr p nr = match LMap.assoc nr p.P.typed_node_names with [
  x -> x | exception Not_found -> assert False
] 
;
value lookup_var p nr = match LMap.assoc (lookup_tnr p nr) p.P.rev_patt_var_to_noderef with [
  x -> x | exception Not_found -> assert False
]
;
value lookup_abs_childnum p nr = match LMap.assoc (lookup_var p nr) p.P.patt_var_to_childnum with [
  x -> x | exception Not_found -> assert False
]
;
value compile_teqn_tcond_body ag p body =
  let open AG in
  let open P in
  let open TAEQ in
  let open TNR in
  let dt = Camlp5_migrate.make_dt () in
  let fallback_migrate_expr = dt.migrate_expr in
  let migrate_expr dt e =
    match e with [
      <:expr:< [%prim $int:absi$ ;] >> ->
      let v = lookup_var p (NR.PRIM None (int_of_string absi)) in
      <:expr< $lid:v$ >>

    | <:expr:< [%prim $lid:tyname$ . ( $int:reli$ ) ;] >> when AG.is_primitive_ctyp ag tyname ->
      let v = lookup_var p (NR.PRIM (Some tyname) (int_of_string reli)) in
      <:expr< $lid:v$ >>

(*
    | <:expr:< [%prim int . ( $int:reli$ ) ;] >> ->
      let v = lookup_var p (NR.PRIM (Some "int") (int_of_string reli)) in
      <:expr< $lid:v$ >>
    | <:expr:< [%prim string . ( $int:reli$ ) ;] >> ->
      let v = lookup_var p (NR.PRIM (Some "string") (int_of_string reli)) in
      <:expr< $lid:v$ >>
*)
    | <:expr:< [%nterm 0 ;] . $lid:attrna$ >> ->
      let tnr = lookup_tnr p (NR.PARENT None) in
      let cnt = match tnr with [ TNR.PARENT cnt -> cnt | _ -> assert False ] in
      <:expr< ( AttrTable. $lid:attr_accessor_name cnt attrna$ attrs parent  ) >>

    | <:expr:< [%nterm $lid:nt$ ;] . $lid:attrna$ >> ->
      <:expr< ( AttrTable. $lid:attr_accessor_name nt attrna$ attrs parent  ) >>

    | <:expr:< [%nterm $int:absi$ ;] . $lid:attrna$ >> ->
      let tnr = lookup_tnr p (NR.CHILD None (int_of_string absi)) in
      let v = lookup_var p (NR.CHILD None (int_of_string absi)) in
      let cnt = match tnr with [ TNR.CHILD cnt _ -> cnt | _ -> assert False ] in
      <:expr< ( AttrTable. $lid:attr_accessor_name cnt attrna$ attrs $lid:v$  ) >>

    | <:expr:< [%nterm $lid:cnt$ . ( $int:reli$ ) ;] . $lid:attrna$ >> ->
      let v = lookup_var p (NR.CHILD (Some cnt) (int_of_string reli)) in
      <:expr< ( AttrTable. $lid:attr_accessor_name cnt attrna$ attrs $lid:v$  ) >>

    | <:expr:< [%local $lid:attrna$ ;] >> ->
      <:expr< ( AttrTable. $lid:attr_accessor_name (PN.unparse p.P.name) attrna$ attrs prod_attrs ) >>

    | e -> fallback_migrate_expr dt e
    ] in
  let dt = { (dt) with Camlp5_migrate.migrate_expr = migrate_expr } in
  dt.migrate_expr dt body
;

value attr_isset_expression loc ag p =
  let open AG in
  let open P in
  let open TAEQ in
  let open TNR in
  fun [
    TAR.NT (PARENT nt) attrna ->
    <:expr< AttrTable. $lid:attr_isset_name nt attrna$ attrs parent >>

  | TAR.NT ((CHILD dnt _) as dnr) dattr ->
    let v = match LMap.assoc dnr p.rev_patt_var_to_noderef with [ x -> x | exception Not_found -> assert False ] in
    <:expr< AttrTable. $lid:attr_isset_name dnt dattr$ attrs $lid:v$ >>

  | TAR.PROD dpn dattr ->
    <:expr< AttrTable. $lid:attr_isset_name (PN.unparse dpn) dattr$ attrs prod_attrs >>

  | ar -> Ploc.raise loc (Failure Fmt.(str "INTERNAL ERROR: attr_isset_expression:@ %a"
                                         TAR.pp_hum ar))
  ]
;

value attr_setter_expression loc ag p tar rhs =
  let open AG in
  let open P in
  let open TAEQ in
  let open TNR in
  match tar with [
    TAR.NT (PARENT nt) attrna ->
      <:expr< AttrTable. $lid:attr_setter_name nt attrna$ attrs lhs $rhs$ >>

  | TAR.PROD pn attrna ->
    let prodname = PN.unparse pn in 
    let e = <:expr< AttrTable. $lid:attr_setter_name prodname attrna$ attrs prod_lhs $rhs$ >> in
    <:expr< let prod_lhs = prod_attrs in $e$ >>

  | TAR.NT (CHILD cnt childnum) cattrna ->
    <:expr< AttrTable. $lid:attr_setter_name cnt cattrna$ attrs lhs $rhs$ >>

  ]
;

(** generate synthesized-attribute branches

    (1) args are noderef+attrname

    (2) for each equation that is for a synthesized attribute, we
   generate code to check that all required attributes are defined,
   that the specified attribute is *not* defined, and then execute the
   equation, define the attribute's entry.

    (3) then assign the computed value to the slot in the global
   attribute table.

*)
value synthesized_attribute_branch ag p teqn = do {
  let open AG in
  let open P in
  let open TAEQ in
  let open TNR in
  let loc = teqn.loc in
  match teqn.lhs with [
    TAR.NT (PARENT nt) attrna ->
    let attrcons = attr_constructor attrna in
    let ntcons = node_constructor nt in
    let patt = <:patt< (Node . $uid:ntcons$ ({node= $p.patt$ } as lhs), $uid:attrcons$) >> in
    let check_lhs_unset = <:expr< assert (not $attr_isset_expression loc ag p teqn.lhs$) >> in
    let check_deps_set = teqn.rhs_nodes |> List.filter_map (fun tar -> match tar with [
        TAR.NT (CHILD _ _| PARENT _) _ | TAR.PROD _ _ ->
        Some <:expr< assert $attr_isset_expression loc ag p tar$ >>

      | TAR.NT (PRIM _ _) _ -> None
      ]) in
    let body = compile_teqn_tcond_body ag p teqn.rhs_expr in
    let set_lhs = attr_setter_expression loc ag p teqn.lhs body in
    let l = [check_lhs_unset]@check_deps_set@[set_lhs; <:expr< None >>] in
    Some (patt, <:vala< None >>, <:expr< let parent = lhs in do { $list:l$ } >>)

  | TAR.PROD pn attrna ->
    let prodname = PN.unparse pn in 
    let nt = pn.PN.nonterm_name in
    let attrcons = attr_constructor ~{prodname=prodname} attrna in
    let ntcons = node_constructor nt in
    let patt = <:patt< (Node . $uid:ntcons$ ({node= $p.patt$ } as lhs), $uid:attrcons$) >> in
    let check_lhs_unset = <:expr< assert (not $attr_isset_expression loc ag p teqn.lhs$) >> in
    let check_deps_set = teqn.rhs_nodes |> List.filter_map (fun tar -> match tar with [
        TAR.NT (CHILD _ _ | PARENT _) _ ->
        Some <:expr< assert $attr_isset_expression loc ag p tar$ >>

      | TAR.NT (PRIM _ _) _ -> None
      ]) in
    let body = compile_teqn_tcond_body ag p teqn.rhs_expr in
    let set_lhs = attr_setter_expression loc ag p teqn.lhs body in
    let l = [check_lhs_unset]@check_deps_set@[set_lhs; <:expr< None >>] in
    let e = <:expr< do { $list:l$ } >> in
    let e = <:expr< let parent = lhs in $e$ >> in
    Some (patt, <:vala< None >>, e)
  | _ -> None
  ]
}
;

value synthesized_attribute_function memo =
  let open AGOps.NTOps in
  let open AG in
  let open P in
  let open TAEQ in
  let open TNR in
  let ag = memo.ag in
  let loc = ag.loc in
  let attr_branches = 
    ag.productions |> List.concat_map (fun (nt, pl) -> pl |> List.concat_map (fun p ->
        p.typed_equations |> List.filter_map (synthesized_attribute_branch ag p)
      )) in
  (<:patt< compute_synthesized_attribute >>,
   <:expr< fun attrs -> fun (node, attrna) -> match (node, attrna) with [ $list:attr_branches$ ] >>,
   <:vala< [] >>)
;


(** generate inherited-attribute branches

    (1) args are parent+childnum+childnode+attrname

    (2) for each equation that is for an inherited attribute, we
   generate code to check that the inferred child (via childnum) is
   equal to the specified childnode, all required attributes are
   defined, that the specified attribute is *not* defined, and then
   execute the equation, define the attribute's entry.  We can find
   that entry by first finding the child, using childnum.

    (3) then assign the computed value to the slot in the global
   attribute table.

*)
value inherited_attribute_branch ag p teqn = do {
  let open AG in
  let open P in
  let open TAEQ in
  let open TNR in
  let loc = teqn.loc in
  let pnt = p.name.PN.nonterm_name in
  match teqn.lhs with [
    TAR.NT (CHILD cnt childnum) cattrna ->
    let abs_childnum = lookup_abs_childnum p (NR.CHILD (Some cnt) childnum) in
    let cattrcons = attr_constructor cattrna in
    let cntcons = node_constructor cnt in
    let pntcons = node_constructor pnt in
    let patt = <:patt< (Node . $uid:pntcons$ ({node= $p.patt$ } as parent), $int:string_of_int abs_childnum$,
                        Node . $uid:cntcons$ lhs, $uid:cattrcons$) >> in
    let check_lhs_unset = <:expr< assert (not $attr_isset_expression loc ag p teqn.lhs$) >> in
    let check_deps_set = teqn.rhs_nodes |> List.filter_map (fun tar -> match tar with [
        TAR.NT (CHILD _ _ | PARENT _) _ ->
        Some <:expr< assert $attr_isset_expression loc ag p tar$ >>

      | TAR.NT (PRIM _ _) _ -> None
      ]) in
    let body = compile_teqn_tcond_body ag p teqn.rhs_expr in
    let set_lhs = attr_setter_expression loc ag p teqn.lhs body in
    let l = [check_lhs_unset]@check_deps_set@[set_lhs; <:expr< None >>] in
    Some (patt, <:vala< None >>, <:expr< do { $list:l$ } >>)

  | TAR.PROD _ _ | TAR.NT (PARENT _) _ | TAR.NT (PRIM _ _) _ -> None
  ]
}
;

value inherited_attribute_function memo =
  let open AGOps.NTOps in
  let open AG in
  let open P in
  let open TAEQ in
  let open TNR in
  let ag = memo.ag in
  let loc = ag.loc in
  let branches = 
    ag.productions |> List.map (fun (nt, pl) -> pl |> List.map (fun p ->
        p.typed_equations |> List.filter_map (inherited_attribute_branch ag p)
      ))
    |> List.concat |> List.concat in
  (<:patt< compute_inherited_attribute >>,
   Reloc.expr (fun _ -> Ploc.dummy) 0
   <:expr< fun attrs -> fun (node, attrna) ->
           let (parent, childnum) = lookup_parent attrs node in
           match (parent, childnum, node, attrna) with [ $list:branches$ ] >>,
   <:vala< [] >>)
;

value attribute_function memo =
  let open AGOps.NTOps in
  let open AG in
  let open P in
  let open TAEQ in
  let open TNR in
  let ag = memo.ag in
  let loc = ag.loc in
  let inh_patts =
    memo._AI |> List.map (fun (nt, attrs) ->
        attrs |> List.map (fun attrna ->
            <:patt< (Node. $uid:node_constructor nt$ _, $uid:attr_constructor attrna$) >>))
    |> List.concat
  in
  let syn_patts =
    memo._AS |> List.map (fun (nt, attrs) ->
        attrs |> List.map (fun attrna ->
            <:patt< (Node. $uid:node_constructor nt$ _, $uid:attr_constructor attrna$) >>))
    |> List.concat
  in
  let prod_patts =
    ag.productions |> List.concat_map (fun (nt, pl) -> pl |> List.concat_map (fun p ->
        p |> AGOps.POps.defining_occurrences |> List.filter_map (fun [
            (TAR.PROD pn attrna) -> Some (pn, attrna)
          | _ -> None
          ])
      ))
    |> List.map (fun (pn, attrna) ->
        let nt = pn.PN.nonterm_name in
        let prodname = PN.unparse pn in
        <:patt< (Node. $uid:node_constructor nt$ _, $uid:attr_constructor ~{prodname=prodname} attrna$) >>
      ) in

  let inh_branches = inh_patts |> List.map (fun p ->
      (<:patt< ( $p$ as aref ) >>, <:vala< None >>, <:expr< compute_inherited_attribute attrs aref >>)) in
  let syn_branches = syn_patts |> List.map (fun p ->
      (<:patt< ( $p$ as aref ) >>, <:vala< None >>, <:expr< compute_synthesized_attribute attrs aref >>)) in
  let prod_branches = prod_patts |> List.map (fun p ->
      (<:patt< ( $p$ as aref ) >>, <:vala< None >>, <:expr< compute_synthesized_attribute attrs aref >>)) in

  (<:patt< compute_attribute >>,
   Reloc.expr (fun _ -> Ploc.dummy) 0
   <:expr< fun attrs -> fun [ $list:inh_branches@syn_branches@prod_branches$ ] >>, <:vala< [] >>)
;

(** evaluate the AG on the argument tree.

    (1) create the global attribute-table
    (2) preprocess the tree to produce the dependency graph
    (3) tsort the graph
    (4) execute the graph in topological order
    (5) extract and return all attributes of the axiom node 
*)

value eval_functions memo =
  let open AGOps.NTOps in
  let open AG in
  let open P in
  let open TAEQ in
  let open TNR in
  let ag = memo.ag in
  let loc = ag.loc in
  let axiom = ag.axiom in
  let preprocess_axiom = Printf.sprintf "preprocess_%s" axiom in
  let result_expr =
    match List.assoc axiom memo._AS with [
      x -> x
    | exception Not_found -> assert False
    ]
    |> List.map (fun attrna ->
         <:expr< AttrTable. $lid:attr_accessor_name axiom attrna$ attrs t >>
       ) |> (fun l -> Expr.tuple loc l) in
  [(<:patt< compute_attribute1 >>,
    <:expr< fun attrs -> fun [ None -> () | Some a ->
      let newnode = compute_attribute attrs a in
      match newnode with [ None -> () | Some _ -> assert False ] ] >>,
    <:vala< [] >>);
(<:patt< evaluate >>,
   Reloc.expr (fun _ -> Ploc.dummy) 0
   <:expr< fun t ->
     let attrs = AttrTable.mk() in
     let deps = ref [] in
     let deps = do {
       ignore ($lid:preprocess_axiom$ attrs deps t) ;
       deps.val
     } in
   let g = edges_to_graph deps in do {
     if Dfs.has_cycle g then
       failwith "evaluate: cycle found in actual dependencies"
     else () ;
     TSort.iter (compute_attribute1 attrs) g ;
     $result_expr$
   }
   >>,
   <:vala< [] >>)]
;
