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
  value ctyp_top pps x = Fmt.(pf pps "#<ctyp< %a >>" ctyp x) ;
  value expr pps ty = Fmt.(pf pps "%s" (Eprinter.apply Pcaml.pr_expr Pprintf.empty_pc ty));
  value expr_top pps x = Fmt.(pf pps "#<expr< %a >>" expr x) ;
  value patt pps ty = Fmt.(pf pps "%s" (Eprinter.apply Pcaml.pr_patt Pprintf.empty_pc ty));
  value patt_top pps x = Fmt.(pf pps "#<patt< %a >>" patt x) ;
end
;

type storage_mode_t = [ Hashtables | Records ] ;

module AG = struct
  module ProductionName = struct
    type t = {
      nonterm_name: string
    ; case_name: option string
    } ;
    value pp_hum pps = fun [
      {nonterm_name=nonterm_name; case_name = None} -> Fmt.(pf pps "%s__" nonterm_name)
    | {nonterm_name=nonterm_name; case_name = Some case_name} -> Fmt.(pf pps "%s__%s" nonterm_name case_name)
    ]
    ;
    value pp_top pps x = Fmt.(pf pps "#<pn< %a >>" pp_hum x) ;
    value unparse = fun [
      {nonterm_name=nt; case_name=None} -> nt
    | {nonterm_name=nt; case_name=Some s} -> nt^"__"^s
    ]
    ;
  end ;
  module PN = ProductionName ;

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
  value pp_top pps x = Fmt.(pf pps "#<nr< %a >>" pp_hum x) ;

  value to_patt loc = fun [
    PARENT (Some name) -> <:patt< [%nterm $lid:name$ ;] >>
  | PARENT None -> <:patt< [%nterm 0 ;] >>
  | CHILD (Some name) i -> <:patt< [%nterm $lid:name$ . ( $int:string_of_int i$ ) ;] >>
  | CHILD None i when i > 0 -> <:patt< [%nterm $int:string_of_int i$ ;] >>
  | CHILD None i when i <= 0 -> assert False
  | PRIM (Some name) i -> <:patt< [%prim $lid:name$ . ( $int:string_of_int i$ ) ;] >>
  | PRIM None i when i > 0 -> <:patt< [%prim $int:string_of_int i$ ;] >>
  | PRIM None i when i <= 0 -> assert False
  ]
  ;
  value to_expr loc = fun [
    PARENT (Some name) -> <:expr< [%nterm $lid:name$ ;] >>
  | PARENT None -> <:expr< [%nterm 0 ;] >>
  | CHILD (Some name) i -> <:expr< [%nterm $lid:name$ . ( $int:string_of_int i$ ) ;] >>
  | CHILD None i when i > 0 -> <:expr< [%nterm $int:string_of_int i$ ;] >>
  | CHILD None i when i <= 0 -> assert False
  | PRIM (Some name) i -> <:expr< [%prim $lid:name$ . ( $int:string_of_int i$ ) ;] >>
  | PRIM None i when i > 0 -> <:expr< [%prim $int:string_of_int i$ ;] >>
  | PRIM None i when i <= 0 -> assert False
  ]
  ;
  end ;
  module NR = NodeReference ;
  module AR = struct
    type t = [
      NT of NR.t and string
    | PROD of PN.t and string
    | CHAIN of PN.t and string
    ]
    ;
    value pp_hum pps = fun [
      NT nr a -> Fmt.(pf pps "%a.%s" NR.pp_hum nr a)
    | PROD pn a -> Fmt.(pf pps "%a.%s" PN.pp_hum pn a)
    ]
    ;
    value pp_top pps x = Fmt.(pf pps "#<ar< %a >>" pp_hum x) ;
  end ;

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
    value pp_top pps x = Fmt.(pf pps "#<tnr< %a >>" pp_hum x) ;
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
  module TAR = struct
    type t = [
      NT of TNR.t and string
    | PROD of PN.t and string
    ]
    ;
    value pp_hum pps = fun [
      NT nr a -> Fmt.(pf pps "%a.%s" TNR.pp_hum nr a)
    | PROD pn a -> Fmt.(pf pps "%a.%s" PN.pp_hum pn a)
    ]
    ;
    value pp_top pps x = Fmt.(pf pps "#<tar< %a >>" pp_hum x) ;
  end ;

  value wrap_comment pp1 pps x = Fmt.(pf pps "(* %a *)" pp1 x) ;

  module AEQ = struct
    type t = {
      loc : Ploc.t
    ; lhs : AR.t
    ; msg : option string
    ; rhs_nodes : list AR.t
    ; rhs_expr : MLast.expr
    }
    ;
    value pp_hum ?{is_condition=False} pps x =
      if is_condition then do {
        assert (match x.lhs with [ AR.PROD _ "condition" -> True | _ -> False ]) ;
        Fmt.(pf pps "assert %a %a"
               (option Dump.string) x.msg
               PP_hum.expr x.rhs_expr) ;
      }
      else
        Fmt.(pf pps "%a := %a%a" AR.pp_hum x.lhs PP_hum.expr x.rhs_expr
               (option (wrap_comment Dump.string)) x.msg) ;
    value pp_top ?{is_condition=False} pps x = Fmt.(pf pps "#<aeq< %a >>" (pp_hum ~{is_condition=is_condition}) x) ;
  end ;

  type production_action_t = [
      Equation of AEQ.t
    | Condition of AEQ.t
    | Chainstart of AEQ.t
  ]
  ;

  module TAEQ = struct
    type t = {
      loc : Ploc.t
    ; lhs : TAR.t
    ; msg : option string
    ; rhs_nodes : list TAR.t
    ; rhs_expr : MLast.expr
    }
    ;
    value pp_hum ?{is_condition=False} pps x =
      if is_condition then do {
        assert (match x.lhs with [ TAR.PROD _ "condition" -> True | _ -> False ]) ;
        Fmt.(pf pps "assert %a %a"
               (option (wrap_comment Dump.string)) x.msg
               PP_hum.expr x.rhs_expr
            )
      }
      else
        Fmt.(pf pps "%a := %a%a" TAR.pp_hum x.lhs PP_hum.expr x.rhs_expr
               (option (wrap_comment Dump.string)) x.msg) ;
    value pp_top ?{is_condition=False} pps x = Fmt.(pf pps "#<taeq< %a >>" (pp_hum ~{is_condition=is_condition}) x) ;
  end ;

  module Production = struct
    type t = {
      name : PN.t
    ; loc : Ploc.t
    ; typed_nodes : list TNR.t
    ; typed_node_names : list (NR.t * TNR.t)
    ; equations : list AEQ.t
    ; typed_equations : list TAEQ.t
    ; conditions : list AEQ.t
    ; typed_conditions : list TAEQ.t
    ; patt : MLast.patt
    ; patt_var_to_noderef : list (string * TNR.t)
    ; rev_patt_var_to_noderef : list (TNR.t * string)
    ; patt_var_to_childnum : list (string * int)
    } ;
    value pp_hum pps x =
      Fmt.(pf pps "%a : %a\n%a@ %a"
             PN.pp_hum x.name
             PP_hum.patt x.patt
             (list AEQ.pp_hum) x.equations
             (list AEQ.pp_hum) x.conditions
          ) ;
    value pp_top pps x = Fmt.(pf pps "#<prod< %a >>" pp_hum x) ;
    value typed_attribute p = fun [
      AR.NT nr attrna ->
        match List.assoc nr p.typed_node_names with [
          x -> TAR.NT x attrna
        | exception Not_found ->
          Ploc.raise p.loc (Failure Fmt.(str "attribute %a.%s could not be converted to its typed form"
                                           NR.pp_hum nr attrna))
        ]
    | AR.PROD pn attrna -> TAR.PROD pn attrna
    ]
    ;
    value typed_equation p aeq =
      let { AEQ.loc = loc; lhs = lhs ; msg = msg ; rhs_nodes = rhs_nodes ; rhs_expr = rhs_expr } = aeq in
      {
        TAEQ.loc = loc
      ; lhs = typed_attribute p lhs
      ; msg = msg
      ; rhs_nodes = List.map (typed_attribute p) rhs_nodes
      ; rhs_expr = rhs_expr
      }
      ;
  end ;
  module P = Production ;

  module AttributeType = struct
    type t = {
      ty : ctyp
    ; is_chain : bool
    }
    ;
    value mk = fun [
      <:ctyp< $ty$ [@chain] >> -> { ty = ty ; is_chain = True }
    | ty -> { ty = ty ; is_chain = True }
    ]
    ;
  end;
  module AT = AttributeType ;
  type t = {
    loc : Ploc.t
  ; storage_mode : storage_mode_t
  ; axiom : string
  ; attribute_types : list (string * AT.t)
  ; node_attributes : list (string * (list string))
  ; production_attributes : list (string * (list string))
  ; nonterminals : list string
  ; equations : list (PN.t * (list AEQ.t))
  ; conditions : list (PN.t * (list AEQ.t))
  ; productions : list (string * list P.t)
  }
  ;
  value mk0 loc storage_mode axiom nonterminals
    (attribute_types, node_attributes, production_attributes)
    equations conditions = {
    loc = loc
  ; storage_mode = storage_mode
  ; axiom = axiom
  ; nonterminals = nonterminals
  ; attribute_types = attribute_types |> List.map (fun (ana, aty) -> (ana, AT.mk aty))
  ; node_attributes = node_attributes
  ; production_attributes = production_attributes
  ; equations = equations
  ; conditions = conditions
  ; productions = []
  }
  ;
end ;

module Demarshal = struct

value expr_to_attribute_reference pn e =
  let open AG in
  let open AEQ in
  match e with [
    <:expr< [%nterm $lid:tyname$;] . $lid:attrna$ >> -> 
    AR.NT (NR.PARENT (Some tyname)) attrna
  | <:expr< [%nterm 0;] . $lid:attrna$ >> ->
    AR.NT (NR.PARENT None) attrna
  | <:expr< [%nterm $int:n$;] . $lid:attrna$ >> ->
    AR.NT (NR.CHILD None (int_of_string n)) attrna
  | <:expr< [%nterm $lid:tyname$ . ( $int:n$ );] . $lid:attrna$ >> ->
    AR.NT (NR.CHILD (Some tyname) (int_of_string n)) attrna
  | <:expr< [%prim $int:n$;] >> ->
    AR.NT (NR.PRIM None (int_of_string n)) ""
  | <:expr< [%local $lid:attrna$;] >> ->
    AR.PROD pn attrna
  | _ -> Ploc.raise (MLast.loc_of_expr e) (Failure Fmt.(str "expr_to_attribute_reference: bad expr:@ %a"
                                                          Pp_MLast.pp_expr e))
  ]
;

value extract_attribute_references pn e =
  let references = ref [] in
  let dt = Camlp5_migrate.make_dt () in
  let fallback_migrate_expr = dt.migrate_expr in
  let migrate_expr dt e =
    try do { Std.push references (expr_to_attribute_reference pn e); e } 
    with _ -> fallback_migrate_expr dt e in
  let dt = { (dt) with Camlp5_migrate.migrate_expr = migrate_expr } in do {
    ignore(dt.migrate_expr dt e) ;
    List.rev references.val
  }
;

value assignment_to_equation_or_condition pn e = match e with [
    <:expr:< $lhs$ . val := $rhs$ >> | <:expr:< $lhs$ := $rhs$ >> ->
    (True, {
      AG.AEQ.loc = loc
    ; lhs = expr_to_attribute_reference pn lhs
    ; msg = None
    ; rhs_nodes = extract_attribute_references pn rhs
    ; rhs_expr = rhs })

  | <:expr:< condition $str:msg$ $e$ >> ->
    (False, { 
      AG.AEQ.loc = loc
    ; msg = Some msg
    ; lhs = AG.AR.PROD pn "condition"
    ; rhs_nodes = extract_attribute_references pn e
    ; rhs_expr = e })
  | <:expr:< condition $e$ >> ->
    (False, { 
      AG.AEQ.loc = loc
    ; msg = None
    ; lhs = AG.AR.PROD pn "condition"
    ; rhs_nodes = extract_attribute_references pn e
    ; rhs_expr = e })

  | _ -> Ploc.raise (MLast.loc_of_expr e)
      (Failure Fmt.(str "assignment_to_equation_or_condition: neither assignment nor condition@ %a"
                      Pp_MLast.pp_expr e))
]
;

value name_re = Pcre.regexp "^(.*)__((?:_?[^_])+_?)?$" ;
value parse_prodname loc s =
  let open AG in
  match Pcre.extract ~{rex=name_re} ~{pos=0} s with [
    [|_;lhs;""|] ->
    { PN.nonterm_name = lhs; case_name = None }
  | [|_;lhs;rhs|] ->
    { PN.nonterm_name = lhs; case_name = Some rhs }
  | exception Not_found ->
    { PN.nonterm_name = s; case_name = None }
  ]
;

value extract_attribute_equations_and_conditions loc l : (list (AG.PN.t * (list (bool * AG.AEQ.t)))) =
  l |> List.map (fun (prodname, e) ->
    let prodname = parse_prodname loc prodname in
    match e with [
      <:expr< do { $list:l$ } >> ->
      (prodname, List.map (assignment_to_equation_or_condition prodname) l)
    | <:expr< $_$ . val := $_$ >> ->
      (prodname, [assignment_to_equation_or_condition prodname e])
    | _ -> Ploc.raise (MLast.loc_of_expr e)
        (Failure Fmt.(str "extract_attribute_equations_and_conditions (production %a): unrecognized@ %a"
                        AG.PN.pp_hum prodname Pp_MLast.pp_expr e))
    ])
;

value extract_attribute_equations loc l : (list (AG.PN.t * (list AG.AEQ.t))) =
  extract_attribute_equations_and_conditions loc l
  |> List.map (fun (n, l) ->
                (n, l |> Std.filter (fun (iseqn, _) -> iseqn) |> List.map snd))
;

value extract_attribute_conditions loc l : (list (AG.PN.t * (list AG.AEQ.t))) =
  extract_attribute_equations_and_conditions loc l
  |> List.map (fun (n, l) ->
                (n, l |> Std.filter (fun (iseqn, _) -> not iseqn) |> List.map snd))
;

value compute_name2nodename type_decls =
  type_decls |> List.map (fun (name, td) ->
     match td.tdDef with [
       (
         <:ctyp< unique $lid:nodename$ >>
       | <:ctyp< Unique.unique $lid:nodename$ >>
       | <:ctyp< Pa_ppx_unique_runtime.Unique.unique $lid:nodename$ >>
       | <:ctyp< attributed $lid:nodename$ $_$ >>
       | <:ctyp< Attributes.attributed $lid:nodename$ $_$ >>
       | <:ctyp< Pa_ppx_ag_runtime.Attributes.attributed $lid:nodename$ $_$ >>
       ) ->
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

value tuple2production loc ag lhs_name ?{case_name=None} tl =
  let open AG in
  let node_aliases = NA.mk() in
  let typed_nodes = ref [TNR.PARENT lhs_name] in
  let patt_nref_l = tl |> List.mapi (fun i -> fun [
      <:ctyp:< $lid:tyname$ >> when List.mem tyname ag.nonterminals -> do {
        let aliasnum = NA.next_nterm_number node_aliases tyname in
        NA.add node_aliases (TNR.CHILD tyname aliasnum, NR.CHILD None (i+1)) ;
        Std.push typed_nodes (TNR.CHILD tyname aliasnum) ;
        let v = Printf.sprintf "v_%d" (i+1) in
        (<:patt< $lid:v$ >>, (v, TNR.CHILD tyname aliasnum), (v, i+1))
      }
    | <:ctyp:< $lid:tyname$ >> as z when List.mem (canon_ctyp z) builtin_types -> do {
        let aliasnum = NA.next_prim_number node_aliases tyname in
        NA.add node_aliases (TNR.PRIM tyname aliasnum, NR.PRIM None (i+1)) ;
        Std.push typed_nodes (TNR.PRIM tyname aliasnum) ;
        let v = Printf.sprintf "v_%d" (i+1) in
        (<:patt< $lid:v$ >>, (v, TNR.PRIM tyname aliasnum), (v, i+1))
      }
    | ty ->
      Ploc.raise (MLast.loc_of_ctyp ty)
        (Failure Fmt.(str "productions: unsupported rhs-of-production type: %s@ %a"
                        lhs_name Pp_MLast.pp_ctyp ty))
  ]) in
  let pn = { PN.nonterm_name = lhs_name ; case_name = case_name } in
  let typed_nodes = List.rev typed_nodes.val in
  let equations = match List.assoc pn ag.equations with [ x -> x | exception Not_found -> [] ] in
  let conditions = match List.assoc pn ag.conditions with [ x -> x | exception Not_found -> [] ] in
  let node_aliases = [(TNR.PARENT lhs_name, NR.PARENT None) :: NA.get node_aliases] in
  let typed_node_names = 
    (List.map (fun (tnr,_) -> (TNR.to_nr tnr, tnr)) node_aliases)
    @(List.map (fun (a,b) -> (b,a)) node_aliases) in
  let p = {
    P.name = pn
  ; loc = loc
  ; typed_nodes = typed_nodes
  ; typed_node_names = typed_node_names
  ; equations = equations
  ; typed_equations = []
  ; conditions = conditions
  ; typed_conditions = []
  ; patt = Patt.tuple loc (List.map Std.fst3 patt_nref_l)
  ; patt_var_to_noderef = List.map Std.snd3 patt_nref_l
  ; rev_patt_var_to_noderef = patt_nref_l |> List.map Std.snd3 |> List.map (fun (a,b) -> (b,a))
  ; patt_var_to_childnum = List.map Std.third3 patt_nref_l
  } in
  let typed_equations = List.map (P.typed_equation p) equations in
  let typed_conditions = List.map (P.typed_equation p) conditions in
  { (p) with
    P.typed_equations = typed_equations
  ; typed_conditions = typed_conditions
  }
;

value branch2production loc ag lhs_name b =
  let open AG in
  match b with [
    <:constructor:< $uid:ci$ of $list:tl$ $_algattrs:_$ >> as gc
    when ag.storage_mode = Records && tl <> [] && List.mem_assoc (lhs_name^"__"^ci) ag.production_attributes ->
      let (last, tl) = sep_last tl in
      let lastpatt = match last with [
        <:ctyp< $lid:n$ >> when n = lhs_name^"__"^ci^"_attributes" -> <:patt< prod_attrs >>
      | _ -> Ploc.raise loc
               (Failure Fmt.(str "branch2production: unrecognizable last type:@ %a"
                               Pp_MLast.pp_generic_constructor gc))
      ] in
      let p = tuple2production loc ag lhs_name ~{case_name=Some ci} tl in
      { (p) with
        patt = match p.P.patt with [
          <:patt< ( $list:patl$ ) >> -> Patt.applist <:patt< $uid:ci$ >> (patl@[lastpatt])
        | p -> Patt.applist <:patt< $uid:ci$ >> ([p]@[lastpatt])
        ]
      }
    | <:constructor< $uid:ci$ of $list:tl$ $_algattrs:_$ >> ->
      let p = tuple2production loc ag lhs_name ~{case_name=Some ci} tl in
      { (p) with
        patt = match p.P.patt with [
          <:patt< ( $list:patl$ ) >> -> Patt.applist <:patt< $uid:ci$ >> patl
        | p -> Patt.applist <:patt< $uid:ci$ >> [p]
        ]
      }
  ]
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

  module POps = struct
    value attribute_occurrences p =
      p.P.typed_equations
      |> List.map (fun teq -> [teq.TAEQ.lhs :: teq.TAEQ.rhs_nodes])
      |> List.concat ;

    value defining_occurrences p =
      (List.map (fun teq -> teq.TAEQ.lhs) p.P.typed_equations)@
      (if p.P.typed_conditions <> [] then [(List.hd p.P.typed_conditions).TAEQ.lhs] else [])
    ;

    value inherited_occurrences p =
      p
      |> defining_occurrences
      |> Std.filter (fun [
          TAR.NT (TNR.CHILD _ _) _ -> True
        | _ -> False
        ])
    ;
    value synthesized_occurrences p =
      p
      |> defining_occurrences
      |> Std.filter (fun [
          TAR.NT (TNR.PARENT _) _ -> True
        | TAR.PROD _ _ -> True
        | _ -> False
        ])
    ;

    value direct_reference_graph p =
      (p.P.typed_equations
       |> List.concat_map (fun teq ->
           let open TAEQ in
           List.map (fun rhs_ar -> (rhs_ar, teq.lhs)) teq.rhs_nodes))@
      (p.P.typed_conditions
       |> List.concat_map (fun tcond ->
           let open TAEQ in
           List.map (fun rhs_ar -> (rhs_ar, tcond.lhs)) tcond.rhs_nodes))
    ;

  end ;

  module NTOps = struct
    value _attributes_of ag ntname =
      ag.productions
      |> List.map snd |> List.concat
      |> List.map POps.attribute_occurrences |> List.concat
      |> List.filter_map (fun [
          TAR.NT (TNR.CHILD n _) attrna when n = ntname -> Some attrna
        | TAR.NT (TNR.PARENT n) attrna when n = ntname -> Some attrna
        | _ -> None
        ])
      |> Std2.hash_uniq
    ;

    value _inherited_attributes_of ag ntname =
      ag.productions
      |> List.map snd |> List.concat
      |> List.map POps.inherited_occurrences |> List.concat
      |> List.filter_map (fun [
          TAR.NT (TNR.CHILD n _) attrna when n = ntname -> Some attrna
        | _ -> None
        ])
      |> Std2.hash_uniq
    ;
    value _synthesized_attributes_of ag ntname =
      ag.productions
      |> List.map snd |> List.concat
      |> List.map POps.synthesized_occurrences |> List.concat
      |> List.filter_map (fun [
          TAR.NT (TNR.PARENT n) attrna when n = ntname -> Some attrna
        | _ -> None
        ])
      |> Std2.hash_uniq
    ;

    type memoized_af_ai_is_t = {
      ag : AG.t
    ; _A : list (string * list string)
    ; _AI : list (string * list string)
    ; _AS : list (string * list string)
    }
    ;

    value mk_memo ag =
    let a = ag.nonterminals |> List.map (fun nt ->
        (nt, _attributes_of ag nt)
      ) in
    let ainh = ag.nonterminals |> List.map (fun nt ->
        (nt, _inherited_attributes_of ag nt)
      ) in
    let asyn = ag.nonterminals |> List.map (fun nt ->
        (nt, _synthesized_attributes_of ag nt)
      ) in
    { ag = ag ; _A = a ; _AI = ainh ; _AS = asyn }
    ;
    value _A m nt = match List.assoc nt m._A with [
      x -> x
    | exception Not_found ->
      Ploc.raise m.ag.loc
        (Failure Fmt.(str "INTERNAL ERROR: A: nonterminal %s appears to be unknown" nt))
    ]
    ;
    value _AI m nt = match List.assoc nt m._AI with [
      x -> x
    | exception Not_found ->
      Ploc.raise m.ag.loc
        (Failure Fmt.(str "INTERNAL ERROR: AI: nonterminal %s appears to be unknown" nt))
    ]
    ;
    value _AS m nt = match List.assoc nt m._AS with [
      x -> x
    | exception Not_found ->
      Ploc.raise m.ag.loc
        (Failure Fmt.(str "INTERNAL ERROR: AS: nonterminal %s appears to be unknown" nt))
    ]
    ;

  end ;


  (** an AG is well-formed2 if every attribute reference in all equations
      and conditions is declared in the typed attributes *)

  value attribute_exists attributes (nt, attrna) =
    List.mem_assoc nt attributes &&
    let attrs = List.assoc nt attributes in
    List.mem attrna attrs
  ;

  value well_formed_aref ag =
    let open AG in
    let open TAR in
    let open TNR in
    let open PN in
    fun [
      NT (PRIM _ _) "" -> True
    | NT (PARENT nt) attrna -> attribute_exists ag.node_attributes (nt, attrna)
    | NT (CHILD nt _) attrna -> attribute_exists ag.node_attributes (nt, attrna)
    | PROD pn attrna -> attribute_exists ag.production_attributes (PN.unparse pn, attrna)
    | _ -> False
    ]
  ;

  value true_or_exn ~{exnf} x = if x then x else exnf() ;

  value well_formed_equation0 ag pn teq =
    let open AG.TAEQ in
    well_formed_aref ag teq.lhs &&
    List.for_all (well_formed_aref ag) teq.rhs_nodes
  ;

  value well_formed_equation ag pn teq =
    let open AG.TAEQ in
    true_or_exn ~{exnf=fun () ->
        Ploc.raise teq.loc (Failure Fmt.(str "not a well-formed equation in production %a: %a"
                                           PN.pp_hum pn
                                           (TAEQ.pp_hum ~{is_condition=False}) teq))}
      (well_formed_equation0 ag pn teq)
  ;

  value well_formed_condition0 typed_attributes pn tcond =
    let open AG.TAEQ in
    well_formed_aref typed_attributes tcond.lhs &&
    List.for_all (well_formed_aref typed_attributes) tcond.rhs_nodes
  ;

  value well_formed_condition typed_attributes pn tcond =
    let open AG.TAEQ in
    true_or_exn ~{exnf=fun () ->
        Ploc.raise tcond.loc (Failure Fmt.(str "not a well-formed condition in production %a: %a"
                                             PN.pp_hum pn
                                             (TAEQ.pp_hum ~{is_condition=True}) tcond))}
      (well_formed_condition0 typed_attributes pn tcond)
  ;

  value well_formed2 m =
    let ag = m.NTOps.ag in
    (ag.productions |> List.for_all (fun (nt, pl) -> pl |> List.for_all (fun p ->
         p.P.typed_equations |> List.for_all (well_formed_equation ag p.P.name) &&
         p.P.typed_conditions |> List.for_all (well_formed_condition ag p.P.name)
       )))
  ;

  value well_formed m =
    let ag = m.NTOps.ag in
    (well_formed2 m) &&
    (ag.nonterminals |> List.for_all (fun nt ->
        [] = Std.intersect (NTOps._AI m nt) (NTOps._AS m nt)
    ))
    && (ag.productions |> List.for_all (fun (_, pl) ->
        pl |> List.for_all (fun p ->
            Std.distinct (POps.defining_occurrences p)
          )
      ))
  ;

  value complete m =
    let ag = m.NTOps.ag in
    let loc = ag.loc in
    (ag.nonterminals |> List.for_all (fun nt ->
         true_or_exn ~{exnf=fun () ->
             Ploc.raise loc
               (Failure Fmt.(str "complete: AG is not complete (nonterminal X = %s): sets (A(X) = { %a }) != (AI(X) = { %a }) union (AS(X) = { %a })"
                               nt (list string) (NTOps._A m nt)
                               (list string) (NTOps._AI m nt)
                               (list string) (NTOps._AS m nt)))}
           (Std.same_members (NTOps._A m nt) (Std.union (NTOps._AI m nt) (NTOps._AS m nt))) &&
         true_or_exn ~{exnf=fun () ->
             Ploc.raise loc
               (Failure Fmt.(str "complete: AG is not complete (nonterminal X = %s): sets (A(X) = { %a }) != (declared_attributes(X) = { %a })"
                               nt (list string) (NTOps._A m nt)
                               (list string) (List.assoc nt ag.node_attributes)
                               ))}
           (Std.same_members (NTOps._A m nt)
        (match List.assoc nt ag.node_attributes with
           [ l -> l | exception Not_found -> assert False ]))
    ))
    && (ag.productions |> List.for_all
          (fun (_, pl) -> pl |> List.for_all (fun p ->
               (List.tl p.P.typed_nodes) |> List.for_all (fun node ->
                   match node with [
                     TNR.PARENT nt ->
                     let synthesized = NTOps._AS m nt in
                     let occurrences = List.map (fun a -> TAR.NT node a) synthesized in
                     Std.subset occurrences (POps.defining_occurrences p)
                   | TNR.CHILD nt _ ->
                     let inherited = NTOps._AI m nt in
                     let occurrences = List.map (fun a -> TAR.NT node a) inherited in
                     Std.subset occurrences (POps.defining_occurrences p)
                   | TNR.PRIM _ _ -> True
                   ]
                 ))))
    && ([] = NTOps._AI m ag.axiom)
    && True
  ;

  value locally_acyclic m =
    let ag = m.NTOps.ag in
    ag.productions |> List.for_all (fun (_, pl) -> pl |> List.for_all (fun p ->
        let ddp = POps.direct_reference_graph p in
        not Tsort0.(cyclic (nodes ddp) (mkadj ddp))
      ))
  ;

end
;
