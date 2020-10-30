(* camlp5r *)
(* ag_types.ml,v *)

open Asttools;
open MLast;
open Pa_ppx_base ;
open Pa_passthru ;
open Ppxutil ;
open Surveil ;
open Pa_deriving_base ;
open Pa_ppx_utils ;

value canon_expr e = Reloc.expr (fun _ -> Ploc.dummy) 0 e ;
value canon_ctyp ty = Reloc.ctyp (fun _ -> Ploc.dummy) 0 ty ;
value builtin_types =
  let loc = Ploc.dummy in
  List.map canon_ctyp [
    <:ctyp< string >>
  ; <:ctyp< int >>
  ; <:ctyp< int32 >>
  ; <:ctyp< int64 >>
  ; <:ctyp< nativeint >>
  ; <:ctyp< float >>
  ; <:ctyp< bool >>
  ; <:ctyp< char >>
  ]
;

module PP_hum = struct
  value ctyp pps ty = Fmt.(pf pps "%s" (Eprinter.apply Pcaml.pr_ctyp Pprintf.empty_pc ty));
  value expr pps ty = Fmt.(pf pps "%s" (Eprinter.apply Pcaml.pr_expr Pprintf.empty_pc ty));
  value patt pps ty = Fmt.(pf pps "%s" (Eprinter.apply Pcaml.pr_patt Pprintf.empty_pc ty));
end
;
module AG = struct
  module NodeReference = struct
    type t = [
        PARENT of option string
      | CHILD of option string and int
      | PRIM of option string and int
      ] ;
  value pp_hum pps = fun [
    PARENT (Some name) -> Fmt.(pf pps "[%%nterm %s ;]" name)
  | PARENT None -> Fmt.(pf pps "[%%nterm 0 ;]")
  | CHILD (Some name) i -> Fmt.(pf pps "[%%nterm %s.(%d) ;]" name i)
  | CHILD None i -> Fmt.(pf pps "[%%nterm %d ;]" i)
  | PRIM (Some name) i -> Fmt.(pf pps "[%%prim %s.(%d) ;]" name i)
  | PRIM None i -> Fmt.(pf pps "[%%nterm %d ;]" i)
  ]
  ;

  value to_patt loc = fun [
    PARENT (Some name) -> <:patt< [%nterm $lid:name$ ;] >>
  | PARENT None -> <:patt< [%nterm 0 ;] >>
  | CHILD (Some name) i -> <:patt< [%nterm $lid:name$ . ( $int:string_of_int i$ ) ;] >>
  | CHILD None i -> <:patt< [%nterm $int:string_of_int i$ ;] >>
  | PRIM (Some name) i -> <:patt< [%prim $lid:name$ . ( $int:string_of_int i$ ) ;] >>
  | PRIM None i -> <:patt< [%prim $int:string_of_int i$ ;] >>
  ]
  ;
  value to_expr loc = fun [
    PARENT (Some name) -> <:expr< [%nterm $lid:name$ ;] >>
  | PARENT None -> <:expr< [%nterm 0 ;] >>
  | CHILD (Some name) i -> <:expr< [%nterm $lid:name$ . ( $int:string_of_int i$ ) ;] >>
  | CHILD None i -> <:expr< [%nterm $int:string_of_int i$ ;] >>
  | PRIM (Some name) i -> <:expr< [%prim $lid:name$ . ( $int:string_of_int i$ ) ;] >>
  | PRIM None i -> <:expr< [%prim $int:string_of_int i$ ;] >>
  ]
  ;
  end ;
  module NR = NodeReference ;
  module TypedNodeReference = struct
    type t = [
        PARENT of string
      | CHILD of string and int
      | PRIM of string and int
      ] ;
    value pp_hum pps = fun [
      PARENT name -> Fmt.(pf pps "[%%nterm %s ;]" name)
    | CHILD name i -> Fmt.(pf pps "[%%nterm %s.(%d) ;]" name i)
    | PRIM name i -> Fmt.(pf pps "[%%prim %s.(%d) ;]" name i)
    ]
    ;
    value to_nr = fun [
      PARENT name -> NR.PARENT (Some name)
    | CHILD name i -> NR.CHILD (Some name) i
    | PRIM name i -> NR.PRIM (Some name) i
    ]
    ;
    value to_patt loc x = NR.to_patt loc (to_nr x) ;
    value to_expr loc x = NR.to_expr loc (to_nr x) ;
  end
  ;
  module TNR = TypedNodeReference ;

  module ProductionName = struct
    type t = {
      nonterm_name: string
    ; case_name: option string
    } ;
    value pp_hum pps = fun [
      {nonterm_name=nonterm_name; case_name = None} -> Fmt.(pf pps "%s" nonterm_name)
    | {nonterm_name=nonterm_name; case_name = Some case_name} -> Fmt.(pf pps "%s__%s" nonterm_name case_name)
    ]
    ;
  end ;
  module PN = ProductionName ;

  module AEQ = struct
    type t = {
      lhs : (NR.t * string)
    ; rhs_nodes : list (NR.t * string)
    ; rhs_expr : MLast.expr
    }
    ;
    value pp_hum pps x = Fmt.(pf pps "%a.%s := %a\n" NR.pp_hum (fst x.lhs) (snd x.lhs) PP_hum.expr x.rhs_expr) ;
  end ;

  module TAEQ = struct
    type t = {
      lhs : (TNR.t * string)
    ; rhs_nodes : list (TNR.t * string)
    ; rhs_expr : MLast.expr
    }
    ;
    value pp_hum pps x = Fmt.(pf pps "%a.%s := %a\n" TNR.pp_hum (fst x.lhs) (snd x.lhs) PP_hum.expr x.rhs_expr) ;
  end ;
  module Cond = struct
    type t = {
      body_nodes : list (NR.t * string)
    ; body_expr : MLast.expr
    }
    ;
    value pp_hum pps x = Fmt.(pf pps "assert %a\n"  PP_hum.expr x.body_expr) ;
  end ;

  module TCond = struct
    type t = {
      body_nodes : list (TNR.t * string)
    ; body_expr : MLast.expr
    }
    ;
    value pp_hum pps x = Fmt.(pf pps "assert %a\n" PP_hum.expr x.body_expr) ;
  end ;

  module Production = struct
    type t = {
      name : PN.t
    ; loc : Ploc.t
    ; typed_node_names : list (NR.t * TNR.t)
    ; equations : list AEQ.t
    ; typed_equations : list TAEQ.t
    ; conditions : list Cond.t
    ; typed_conditions : list TCond.t
    ; patt : MLast.patt
    } ;
    value pp_hum pps x =
      Fmt.(pf pps "%a : %a\n%a@ %a"
             PN.pp_hum x.name
             PP_hum.patt x.patt
             (list AEQ.pp_hum) x.equations
             (list Cond.pp_hum) x.conditions
          ) ;
    value typed_attribute p (nr, attrna) =
      match List.assoc nr p.typed_node_names with [
        x -> (x, attrna)
      | exception Not_found ->
        Ploc.raise p.loc (Failure Fmt.(str "attribute %a.%s could not be converted to its typed form"
                                         NR.pp_hum nr attrna))
      ]
    ;
    value typed_equation p aeq =
      let { AEQ.lhs = lhs ; rhs_nodes = rhs_nodes ; rhs_expr = rhs_expr } = aeq in
      {
        TAEQ.lhs = typed_attribute p lhs
      ; rhs_nodes = List.map (typed_attribute p) rhs_nodes
      ; rhs_expr = rhs_expr
      }
      ;
    value typed_condition p cond =
      let { Cond.body_nodes = body_nodes ; body_expr = body_expr } = cond in
      {
        TCond.body_nodes = List.map (typed_attribute p) body_nodes
      ; body_expr = body_expr
      }
      ;
  end ;
  module P = Production ;

  type t = {
    loc : Ploc.t
  ; nonterminals : list string
  ; equations : list (PN.t * (list AEQ.t))
  ; conditions : list (PN.t * (list Cond.t))
  ; productions : list (string * list P.t)
  }
  ;
  value mk0 loc nonterminals equations conditions = {
    loc = loc
  ; nonterminals = nonterminals
  ; equations = equations
  ; conditions = conditions
  ; productions = []
  }
  ;
end ;

module Demarshal = struct

value expr_to_attribute_reference e =
  let open AG in
  let open AEQ in
  match e with [
    <:expr< [%nterm $lid:tyname$;] . $lid:attrna$ >> -> 
    (NR.PARENT (Some tyname), attrna)
  | <:expr< [%nterm 0;] . $lid:attrna$ >> ->
    (NR.PARENT None, attrna)
  | <:expr< [%nterm $int:n$;] . $lid:attrna$ >> ->
    (NR.CHILD None (int_of_string n), attrna)
  | <:expr< [%nterm $lid:tyname$ . ( $int:n$ );] . $lid:attrna$ >> ->
    (NR.CHILD (Some tyname) (int_of_string n), attrna)
  | <:expr< [%prim $int:n$;] . $lid:attrna$ >> ->
    (NR.PRIM None (int_of_string n), attrna)
  | _ -> Ploc.raise (MLast.loc_of_expr e) (Failure Fmt.(str "expr_to_attribute_reference: bad expr:@ %a"
                                                          Pp_MLast.pp_expr e))
  ]
;

value extract_attribute_references e =
  let references = ref [] in
  let dt = Camlp5_migrate.make_dt () in
  let fallback_migrate_expr = dt.migrate_expr in
  let migrate_expr dt e =
    try do { Std.push references (expr_to_attribute_reference e); e } 
    with _ -> fallback_migrate_expr dt e in
  let dt = { (dt) with Camlp5_migrate.migrate_expr = migrate_expr } in do {
    ignore(dt.migrate_expr dt e) ;
    List.rev references.val
  }
;

value assignment_to_equation_or_condition e = match e with [
    <:expr< $lhs$ . val := $rhs$ >> ->
    Left {
      AG.AEQ.lhs = expr_to_attribute_reference lhs
    ; rhs_nodes = extract_attribute_references rhs
    ; rhs_expr = rhs }
  | <:expr< $lhs$ := $rhs$ >> ->
    Left { 
      AG.AEQ.lhs = expr_to_attribute_reference lhs
    ; rhs_nodes = extract_attribute_references rhs
    ; rhs_expr = rhs }
  | <:expr< assert $e$ >> ->
    Right { 
      AG.Cond.body_nodes = extract_attribute_references e
    ; body_expr = e }
  | _ -> Ploc.raise (MLast.loc_of_expr e)
      (Failure Fmt.(str "assignment_to_equation_or_condition: neither assignment nor condition@ %a"
                      Pp_MLast.pp_expr e))
]
;

value name_re = Pcre.regexp "^(.*)__((?:_?[^_])+_?)$" ;
value parse_prodname loc s =
  let open AG in
  match Pcre.extract ~{rex=name_re} ~{pos=0} s with [
    [|_;lhs;rhs|] ->
    { PN.nonterm_name = lhs; case_name = Some rhs }
  | exception Not_found ->
    { PN.nonterm_name = s ; case_name = None }
  ]
;

value extract_attribute_equations_and_conditions loc l : (list (AG.PN.t * (list (choice AG.AEQ.t AG.Cond.t)))) =
  l |> List.map (fun (prodname, e) ->
    let prodname = parse_prodname loc prodname in
    match e with [
      <:expr< do { $list:l$ } >> ->
      (prodname, List.map assignment_to_equation_or_condition l)
    | <:expr< $_$ . val := $_$ >> ->
      (prodname, [assignment_to_equation_or_condition e])
    | _ -> Ploc.raise (MLast.loc_of_expr e)
        (Failure Fmt.(str "extract_attribute_equations_and_conditions (production %a): unrecognized@ %a"
                        AG.PN.pp_hum prodname Pp_MLast.pp_expr e))
    ])
;

value extract_attribute_equations loc l : (list (AG.PN.t * (list AG.AEQ.t))) =
  extract_attribute_equations_and_conditions loc l
  |> List.map (fun (n, l) ->
                (n, l |> Std.filter Asttools.isLeft |> List.map Asttools.outLeft))
;

value extract_attribute_conditions loc l : (list (AG.PN.t * (list AG.Cond.t))) =
  extract_attribute_equations_and_conditions loc l
  |> List.map (fun (n, l) ->
                (n, l |> Std.filter Asttools.isRight |> List.map Asttools.outRight))
;


value compute_name2nodename type_decls =
  type_decls |> List.map (fun (name, td) ->
     match td.tdDef with [
       (<:ctyp< unique $lid:nodename$ >>
       | <:ctyp< Unique.unique $lid:nodename$ >>
       | <:ctyp< Pa_ppx_unique_runtime.Unique.unique $lid:nodename$ >>) ->
       [(name,nodename)]
     | _ -> []
     ]
    ) |> List.concat
;

module NodeAliases = struct
  open AG ;
  value mk () = ref [] ;
  value get x = x.val ;
  value next_nterm_number node_aliases name =
    match List.find_map (fun [
        (TNR.CHILD n i, _) when n = name -> Some i
      | _ -> None
      ]) node_aliases.val with [
        Some n -> n+1
      | None -> 1
      ]
  ;
  value next_prim_number node_aliases name =
    match List.find_map (fun [
        (TNR.PRIM n i, _) when n = name ->
        Some i
      | _ -> None
      ]) node_aliases.val with [
        Some n -> n+1
      | None -> 1
      ]
  ;
  value add x v = Std.push x v ;
end ;
module NA = NodeAliases ;

value branch2production loc ag lhs_name b =
  let open AG in
  match b with [
  <:constructor< $uid:ci$ of $list:tl$ $_algattrs:_$ >> ->
  let node_aliases = NA.mk() in
  let patl = tl |> List.mapi (fun i -> fun [
      <:ctyp:< $lid:tyname$ >> when List.mem tyname ag.nonterminals -> do {
        let aliasnum = NA.next_nterm_number node_aliases tyname in
        NA.add node_aliases (TNR.CHILD tyname aliasnum, NR.CHILD None (i+1)) ;
        NR.to_patt loc (NR.CHILD None (i+1))
      }
    | <:ctyp:< $lid:tyname$ >> as z when List.mem (canon_ctyp z) builtin_types -> do {
        let aliasnum = NA.next_prim_number node_aliases tyname in
        NA.add node_aliases (TNR.PRIM tyname aliasnum, NR.PRIM None (i+1)) ;
        NR.to_patt loc (NR.PRIM None (i+1))
      }
    | ty ->
      Ploc.raise (MLast.loc_of_ctyp ty)
        (Failure Fmt.(str "productions: unsupported rhs-of-production type: %s@ %a"
                        lhs_name Pp_MLast.pp_ctyp ty))
  ]) in
  let pn = { PN.nonterm_name = lhs_name ; case_name = Some ci } in
  let equations = match List.assoc pn ag.equations with [ x -> x | exception Not_found -> [] ] in
  let conditions = match List.assoc pn ag.conditions with [ x -> x | exception Not_found -> [] ] in
  let node_aliases = [(TNR.PARENT lhs_name, NR.PARENT None) :: NA.get node_aliases] in
  let typed_node_names = 
    (List.map (fun (tnr,_) -> (TNR.to_nr tnr, tnr)) node_aliases)
    @(List.map (fun (a,b) -> (b,a)) node_aliases) in
  let p = {
    P.name = pn
  ; loc = loc
  ; typed_node_names = typed_node_names
  ; equations = equations
  ; typed_equations = []
  ; conditions = conditions
  ; typed_conditions = []
  ; patt = Patt.applist <:patt< $uid:ci$ >> patl
  } in
  let typed_equations = List.map (P.typed_equation p) equations in
  let typed_conditions = List.map (P.typed_condition p) conditions in
  { (p) with
    P.typed_equations = typed_equations
  ; typed_conditions = typed_conditions
  }
]
;

value tuple2production loc ag lhs_name tl =
  let open AG in
  let node_aliases = NA.mk() in
  let patl = tl |> List.mapi (fun i -> fun [
      <:ctyp:< $lid:tyname$ >> when List.mem tyname ag.nonterminals -> do {
        let aliasnum = NA.next_nterm_number node_aliases tyname in
        NA.add node_aliases (TNR.CHILD tyname aliasnum, NR.CHILD None (i+1)) ;
        NR.to_patt loc (NR.CHILD None (i+1))
      }
    | <:ctyp:< $lid:tyname$ >> as z when List.mem (canon_ctyp z) builtin_types -> do {
        let aliasnum = NA.next_prim_number node_aliases tyname in
        NA.add node_aliases (TNR.PRIM tyname aliasnum, NR.PRIM None (i+1)) ;
        NR.to_patt loc (NR.PRIM None (i+1))
      }
    | ty ->
      Ploc.raise (MLast.loc_of_ctyp ty)
        (Failure Fmt.(str "productions: unsupported rhs-of-production type: %s@ %a"
                        lhs_name Pp_MLast.pp_ctyp ty))
  ]) in
  let pn = { PN.nonterm_name = lhs_name ; case_name = None } in
  let equations = match List.assoc pn ag.equations with [ x -> x | exception Not_found -> [] ] in
  let conditions = match List.assoc pn ag.conditions with [ x -> x | exception Not_found -> [] ] in
  let node_aliases = [(TNR.PARENT lhs_name, NR.PARENT None) :: NA.get node_aliases] in
  let typed_node_names = 
    (List.map (fun (tnr,_) -> (TNR.to_nr tnr, tnr)) node_aliases)
    @(List.map (fun (a,b) -> (b,a)) node_aliases) in
  let p = {
    P.name = pn
  ; loc = loc
  ; typed_node_names = typed_node_names
  ; equations = equations
  ; typed_equations = []
  ; conditions = conditions
  ; typed_conditions = []
  ; patt = Patt.tuple loc patl
  } in
  let typed_equations = List.map (P.typed_equation p) equations in
  let typed_conditions = List.map (P.typed_condition p) conditions in
  { (p) with
    P.typed_equations = typed_equations
  ; typed_conditions = typed_conditions
  }
;

value productions ag type_decls =
  let open AG in
  let l = type_decls |>
  List.map (fun (name, td) ->
    if List.mem name ag.nonterminals then
      let node_name = Printf.sprintf "%s_node" name in
      let td = match List.assoc node_name type_decls with [
        x -> x
      | exception Not_found -> assert False
      ] in
      match td.tdDef with [
        (<:ctyp:< [ $list:branches$ ] >> | <:ctyp:< $_$ == [ $list:branches$ ] >>) ->
          List.map (branch2production loc ag name) branches
      | <:ctyp:< ( $list:tl$ ) >> ->
          [tuple2production loc ag name tl]
      | <:ctyp:< $lid:_$ >> as z ->
        [tuple2production loc ag name [z]]
      | ty ->
        Ploc.raise (MLast.loc_of_ctyp ty) (Failure Fmt.(str "productions: extraction from type %s failed" name))
      ]
    else []
  )
  |> List.concat in
  let productions = ag.AG.nonterminals |> List.map (fun n ->
    (n, Std.filter (fun p -> n = p.P.name.PN.nonterm_name) l)
  ) in
  { (ag) with AG.productions = productions }
;

end
;

module AGOps = struct
  open AG ;

  value productions ag nt =
    match List.assoc nt ag.productions with [
      x -> x
    | exception Not_found ->
      Ploc.raise ag.loc (Failure Fmt.(str "No productions found for nonterminal %s" nt))
    ]
  ;

  module P = struct
    value attribute_occurrences p =
      p.P.typed_equations
      |> List.map (fun teq -> [teq.TAEQ.lhs :: teq.TAEQ.rhs_nodes])
      |> List.concat ;

    value defining_occurrences p =
      List.map (fun teq -> teq.TAEQ.lhs) p.P.typed_equations ;

    value inherited_occurrences p =
      p
      |> defining_occurrences
      |> Std.filter (fun [
          (TNR.CHILD _ _, _) -> True
        | _ -> False
        ])
    ;
    value synthesized_occurrences p =
      p
      |> defining_occurrences
      |> Std.filter (fun [
          (TNR.PARENT _, _) -> True
        | _ -> False
        ])
    ;
  end ;

  module Attributes = struct
    value is_inherited ag (ntname, attrna) =
      ntname
      |> productions ag
      |> List.map P.inherited_occurrences
      |> List.concat
      |> Std.filter (fun [
          (TNR.CHILD n _, attrna') -> n = ntname && attrna = attrna'
        | _ -> False
        ])
      |> ((<>) [])
    ;
    value is_synthesized ag (ntname,attrna) =
      ntname
      |> productions ag
      |> List.map P.synthesized_occurrences
      |> List.concat
      |> Std.filter (fun [
          (TNR.PARENT n, attrna') -> n = ntname && attrna = attrna'
        | _ -> False
        ])
      |> ((<>) [])
    ;
  end ;

  module NT = struct
    value attributes_of ag ntname =
      ag.productions
      |> List.map snd |> List.concat
      |> List.map P.attribute_occurrences |> List.concat
      |> List.filter_map (fun [
          (TNR.CHILD n _, attrna) when n = ntname -> Some attrna
        | (TNR.PARENT n, attrna) when n = ntname -> Some attrna
        | _ -> None
        ])
    ;

    value inherited_attributes_of ag ntname =
      ag.productions
      |> List.map snd |> List.concat
      |> List.map P.inherited_occurrences |> List.concat
      |> List.filter_map (fun [
          (TNR.CHILD n _, attrna) when n = ntname -> Some attrna
        | _ -> None
        ])
    ;
    value synthesized_attributes_of ag ntname =
      ag.productions
      |> List.map snd |> List.concat
      |> List.map P.synthesized_occurrences |> List.concat
      |> List.filter_map (fun [
          (TNR.PARENT n, attrna) when n = ntname -> Some attrna
        | _ -> None
        ])
    ;
  end ;

  value well_formed ag =
    (ag.nonterminals |> List.for_all (fun nt ->
      Std.same_members (NT.attributes_of ag nt)
        (Std.union (NT.inherited_attributes_of ag nt) (NT.synthesized_attributes_of ag nt))
    ))
    && (ag.nonterminals |> List.for_all (fun nt ->
        [] = Std.intersect
          (NT.inherited_attributes_of ag nt)
          (NT.synthesized_attributes_of ag nt)
    ))
    && (ag.productions |> List.for_all (fun (_, pl) ->
        pl |> List.for_all (fun p ->
            Std.distinct (P.defining_occurrences p)
          )
      ))
  ;
end
;
