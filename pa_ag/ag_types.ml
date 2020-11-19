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

module Pp_hum = struct
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
  value pp_hum ~{is_chainstart} pps = fun [
    PARENT (Some name) -> do {
      assert (not is_chainstart) 
    ; Fmt.(pf pps "[%%nterm %s ;]" name)
    }
  | PARENT None -> do {
      assert (not is_chainstart) 
    ; Fmt.(pf pps "[%%nterm 0 ;]")
    }

  | CHILD (Some name) i when is_chainstart -> Fmt.(pf pps "[%%chainstart %s.(%d) ;]" name i)
  | CHILD None i when is_chainstart -> Fmt.(pf pps "[%%chainstart %d ;]" i)

  | CHILD (Some name) i -> Fmt.(pf pps "[%%nterm %s.(%d) ;]" name i)
  | CHILD None i -> Fmt.(pf pps "[%%nterm %d ;]" i)

  | PRIM (Some name) i -> do {
      assert (not is_chainstart) 
    ; Fmt.(pf pps "[%%prim %s.(%d) ;]" name i)
    }
  | PRIM None i -> do {
      assert (not is_chainstart) 
    ; Fmt.(pf pps "[%%nterm %d ;]" i)
    }
  ]
  ;
  value pp_top pps x = Fmt.(pf pps "#<nr< %a >>" (pp_hum ~{is_chainstart=False}) x) ;

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
    | CHAINSTART of PN.t and NR.t and string
    ]
    ;
    value rec pp_hum pps = fun [
      NT nr a -> Fmt.(pf pps "%a.%s" (NR.pp_hum ~{is_chainstart=False}) nr a)
    | PROD pn a -> Fmt.(pf pps "%a.%s" PN.pp_hum pn a)
    | CHAINSTART pn nr a ->
      Fmt.(pf pps "(* @%a *)%a.%s" PN.pp_hum pn (NR.pp_hum ~{is_chainstart=True}) nr a)
    ]
    ;
    value pp_top pps x = Fmt.(pf pps "#<ar< %a >>" pp_hum x) ;

    value expr_to_ar pn e =
      match e with [
        <:expr< [%nterm $lid:tyname$;] . $lid:attrna$ >> -> 
        NT (NR.PARENT (Some tyname)) attrna
      | <:expr< [%nterm 0;] . $lid:attrna$ >> ->
        NT (NR.PARENT None) attrna
      | <:expr< [%nterm $int:n$;] . $lid:attrna$ >> ->
        NT (NR.CHILD None (int_of_string n)) attrna
      | <:expr< [%nterm $lid:tyname$ . ( $int:n$ );] . $lid:attrna$ >> ->
        NT (NR.CHILD (Some tyname) (int_of_string n)) attrna
      | <:expr< [%prim $int:n$;] >> ->
        NT (NR.PRIM None (int_of_string n)) ""
      | <:expr< [%local $lid:attrna$;] >> ->
        PROD pn attrna

      | <:expr< [%chainstart $int:n$;] . $lid:attrna$ >> ->
        CHAINSTART pn (NR.CHILD None (int_of_string n)) attrna
      | <:expr< [%chainstart $lid:tyname$ . ( $int:n$ );] . $lid:attrna$ >> ->
        CHAINSTART pn (NR.CHILD (Some tyname) (int_of_string n)) attrna

      | _ -> Ploc.raise (MLast.loc_of_expr e)
          (Failure Fmt.(str "expr_to_ar: bad expr:@ %a"
                          Pp_MLast.pp_expr e))
      ]
    ;
  end ;

  module TypedNodeReference = struct
    type t = [
        PARENT of string
      | CHILD of string and int
      | PRIM of string and int
      ] ;
    value pp_hum ~{is_chainstart} pps = fun [
      PARENT name -> do {
        assert (not is_chainstart) 
      ; Fmt.(pf pps "[%%nterm %s ;]" name)
      }

    | CHILD name i when is_chainstart -> Fmt.(pf pps "[%%chainstart %s.(%d) ;]" name i)
    | CHILD name i -> Fmt.(pf pps "[%%nterm %s.(%d) ;]" name i)

    | PRIM name i -> do {
        assert (not is_chainstart) 
      ; Fmt.(pf pps "[%%prim %s.(%d) ;]" name i)
      }
    ]
    ;
    value pp_top pps x = Fmt.(pf pps "#<tnr< %a >>" (pp_hum ~{is_chainstart=False}) x) ;
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
    | CHAINSTART of PN.t and TNR.t and string
    ]
    ;
    value pp_hum pps = fun [
      NT nr a -> Fmt.(pf pps "%a.%s" (TNR.pp_hum ~{is_chainstart=False}) nr a)
    | PROD pn a -> Fmt.(pf pps "%a.%s" PN.pp_hum pn a)
    | CHAINSTART pn nr a ->
      Fmt.(pf pps "(* @%a *)%a.%s" PN.pp_hum pn (TNR.pp_hum ~{is_chainstart=True}) nr a)
    ]
    ;
    value pp_top pps x = Fmt.(pf pps "#<tar< %a >>" pp_hum x) ;

    value expr_to_tar pn e =
      let open TNR in
      match e with [
        <:expr< [%nterm $lid:tyname$;] . $lid:attrna$ >> -> 
        NT (PARENT tyname) attrna

      | <:expr< [%nterm $lid:tyname$ . ( $int:n$ );] . $lid:attrna$ >> ->
        NT (CHILD tyname (int_of_string n)) attrna

      | <:expr< [%prim $lid:tyname$ . ( $int:n$ );] >> ->
        NT (PRIM tyname (int_of_string n)) ""

      | <:expr< [%local $lid:attrna$;] >> ->
        PROD pn attrna

      | <:expr< [%chainstart $lid:tyname$ . ( $int:n$ );] . $lid:attrna$ >> ->
        CHAINSTART pn (CHILD tyname (int_of_string n)) attrna

      | _ -> Ploc.raise (MLast.loc_of_expr e)
          (Failure Fmt.(str "expr_to_attribute_reference: bad expr:@ %a"
                          Pp_MLast.pp_expr e))
  ]
  ;

  value tar_to_expr loc e =
    let open TNR in
    match e with [
      NT (PARENT tyname) attrna ->
      <:expr< [%nterm $lid:tyname$;] . $lid:attrna$ >>

    | NT (CHILD tyname n) attrna ->
      <:expr< [%nterm $lid:tyname$ . ( $int:string_of_int n$ );] . $lid:attrna$ >>

    | NT (PRIM tyname n) "" ->
      <:expr< [%prim $lid:tyname$ . ( $int:string_of_int n$ );] >>

    | PROD pn attrna ->
      <:expr< [%local $lid:attrna$;] >>

    | CHAINSTART pn (CHILD tyname n) attrna ->
      <:expr< [%chainstart $lid:tyname$ . ( $int:string_of_int n$ );] . $lid:attrna$ >>
    ]
    ;
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
               Pp_hum.expr x.rhs_expr) ;
      }
      else
        Fmt.(pf pps "%a := %a%a" AR.pp_hum x.lhs Pp_hum.expr x.rhs_expr
               (option (wrap_comment Dump.string)) x.msg) ;
    value pp_top pps x = Fmt.(pf pps "#<aeq< %a >>" (pp_hum ~{is_condition=False}) x) ;
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
    value lhs e = e.lhs ;
    value rhs_expr e = e.rhs_expr ;
    value rhs_nodes e = e.rhs_nodes ;
    value pp_hum ?{is_condition=False} pps x =
      if is_condition then do {
        assert (match x.lhs with [ TAR.PROD _ "condition" -> True | _ -> False ]) ;
        Fmt.(pf pps "assert %a %a"
               (option (wrap_comment Dump.string)) x.msg
               Pp_hum.expr x.rhs_expr
            )
      }
      else
        Fmt.(pf pps "%a := %a%a" TAR.pp_hum x.lhs Pp_hum.expr x.rhs_expr
               (option (wrap_comment Dump.string)) x.msg) ;
    value pp_top pps x = Fmt.(pf pps "#<taeq< %a >>" (pp_hum ~{is_condition=False}) x) ;
  end ;

  module Production = struct
    type t = {
      name : PN.t
    ; loc : Ploc.t
    ; typed_nodes : list TNR.t
    ; typed_node_names : list (NR.t * TNR.t)
    ; typed_equations : list TAEQ.t
    ; typed_conditions : list TAEQ.t
    ; patt : MLast.patt
    ; patt_var_to_noderef : list (string * TNR.t)
    ; rev_patt_var_to_noderef : list (TNR.t * string)
    ; patt_var_to_childnum : list (string * int)
    } ;
    value lhs p = p.name.PN.nonterm_name ;
    value pp_hum pps x =
      Fmt.(pf pps "%a : %a\n%a@ %a"
             PN.pp_hum x.name
             Pp_hum.patt x.patt
             (list ~{sep=sp} TAEQ.pp_hum) x.typed_equations
             (list ~{sep=sp} TAEQ.pp_hum) x.typed_conditions
          ) ;
    value pp_top pps x = Fmt.(pf pps "#<prod< %a >>" pp_hum x) ;
    value typed_attribute loc p =
      let lookup_nr ~{is_chainstart} nr =
        match List.assoc nr p.typed_node_names with [
          x -> x
        | exception Not_found ->
          Ploc.raise loc (Failure Fmt.(str "nonterminal %a could not be converted to its typed form"
                                         (NR.pp_hum ~{is_chainstart}) nr))
        ] in
      fun [
      (AR.NT nr attrna) as ar ->
      TAR.NT (lookup_nr ~{is_chainstart=False} nr) attrna
    | AR.PROD pn attrna -> TAR.PROD pn attrna
    | AR.CHAINSTART pn nr attrna ->
      TAR.CHAINSTART pn (lookup_nr ~{is_chainstart=True} nr) attrna
    ]
    ;
    value typed_rhs loc p e =
      let dt = Camlp5_migrate.make_dt () in
      let fallback_migrate_expr = dt.migrate_expr in
      let migrate_expr dt e =
        let pn = p.name in
        try e |> AR.expr_to_ar pn |> typed_attribute loc p |> TAR.tar_to_expr (loc_of_expr e)
        with _ -> fallback_migrate_expr dt e in
      let dt = { (dt) with Camlp5_migrate.migrate_expr = migrate_expr } in
      dt.migrate_expr dt e
    ;
    value typed_equation p aeq =
      let { AEQ.loc = loc; lhs = lhs ; msg = msg ; rhs_nodes = rhs_nodes ; rhs_expr = rhs_expr } = aeq in
      {
        TAEQ.loc = loc
      ; lhs = typed_attribute loc p lhs
      ; msg = msg
      ; rhs_nodes = List.map (typed_attribute loc p) rhs_nodes
      ; rhs_expr = typed_rhs loc p rhs_expr
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
    | ty -> { ty = ty ; is_chain = False }
    ]
    ;
    value pp_hum pps x =
      Fmt.(pf pps "%a%s" Pp_hum.ctyp x.ty (if x.is_chain then "[@chain]" else ""))
    ;
    value pp_top pps x = Fmt.(pf pps "#<at< %a >>" pp_hum x) ;
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
  value node_productions ag nt =
    match List.assoc nt ag.productions with [
      x -> x
    | exception Not_found ->
      Ploc.raise ag.loc
        (Failure Fmt.(str "node_productions: nonterminal %s has no productions -- surely this is an error" nt))
    ]
  ;
  value node_attributes ag nt =
    match List.assoc nt ag.node_attributes with [
      x -> x
    | exception Not_found -> []
    ]
  ;
  value node_attribute_exists ag (nt, attrna) =
    List.mem_assoc nt ag.node_attributes &&
    let attrs = List.assoc nt ag.node_attributes in
    List.mem attrna attrs
  ;
  value production_attributes ag nt =
    match List.assoc nt ag.production_attributes with [
      x -> x
    | exception Not_found -> []
    ]
  ;
  value production_attribute_exists ag (pn, attrna) =
    let pn = PN.unparse pn in
    List.mem_assoc pn ag.production_attributes &&
    let attrs = List.assoc pn ag.production_attributes in
    List.mem attrna attrs
  ;
  value attribute_type ag attrna =
    match List.assoc attrna ag.attribute_types with [
      x -> x
    | exception Not_found ->
      Ploc.raise ag.loc (Failure Fmt.(str "attribute_type: attribute %s has no declared type" attrna))
    ]
  ;
end ;

module Demarshal = struct

value extract_attribute_references pn e =
  let references = ref [] in
  let dt = Camlp5_migrate.make_dt () in
  let fallback_migrate_expr = dt.migrate_expr in
  let migrate_expr dt e =
    try do { Std.push references (AG.AR.expr_to_ar pn e); e } 
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
    ; lhs = AG.AR.expr_to_ar pn lhs
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
  ; typed_equations = []
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

value branch2production ag lhs_name b =
  let open AG in
  match b with [
    <:constructor:< $uid:ci$ of $list:tl$ $_algattrs:_$ >> as gc
    when ag.storage_mode = Records && tl <> [] && List.mem_assoc (lhs_name^"__"^ci) ag.production_attributes ->
      let (last, tl) = sep_last tl in
      let lastpatt = match last with [
        <:ctyp:< $lid:n$ >> when n = lhs_name^"__"^ci^"_attributes" -> <:patt< prod_attrs >>
      | ty -> Ploc.raise (MLast.loc_of_ctyp ty)
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
    | <:constructor:< $uid:ci$ of $list:tl$ $_algattrs:_$ >> ->
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
          List.map (branch2production ag name) branches
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
  { (ag) with
    AG.productions = productions
  ; equations = []
  ; conditions = []
  }
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

  module G = Graph.Persistent.Digraph.ConcreteBidirectionalLabeled(
  struct
    type t = string ;
    value equal = (=) ;
    value compare = Stdlib.compare ;
    value hash = Hashtbl.hash ;
  end)(
  struct
    type t = option Production.t ;
    value compare = Stdlib.compare ;
    value default = None ;
  end) ;

  value prodtree_graph ag =
      let open AG in
      let open TNR in
      let g = G.empty in
      let g = List.fold_left G.add_vertex g ag.nonterminals in
      let add_edge g (lhs, pn, rhs) = match (lhs, rhs) with [
        (PARENT pnt, CHILD cnt _) -> G.add_edge_e g (pnt, Some pn, cnt)
      | _ -> g
      ] in
      List.fold_left (fun g (_,pl) ->
          List.fold_left (fun g p ->
              let lhs = List.hd p.P.typed_nodes in
              let rhsl = List.tl p.P.typed_nodes in
              List.fold_left (fun g rhs -> add_edge g (lhs, p, rhs)) g rhsl) g pl) g ag.productions
  ;

    type memoized_af_ai_is_t = {
      ag : AG.t
    ; _A : list (string * list string)
    ; _AI : list (string * list string)
    ; _AS : list (string * list string)
    ; _PT : G.t
    }
    ;

    value mk_memo ag =
    let pt = prodtree_graph ag in
    let a = ag.nonterminals |> List.map (fun nt ->
        (nt, _attributes_of ag nt)
      ) in
    let ainh = ag.nonterminals |> List.map (fun nt ->
        (nt, _inherited_attributes_of ag nt)
      ) in
    let asyn = ag.nonterminals |> List.map (fun nt ->
        (nt, _synthesized_attributes_of ag nt)
      ) in
    { ag = ag ; _A = a ; _AI = ainh ; _AS = asyn ; _PT = pt }
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

(** an AG covers with predicate [pred] a production prod = "a -> ...."

    [pred prod] is TRUE

    OR

    in every possible parsetree where [prod] appears, some ancestor
    production prod' satisfies predicate [pred], viz. [pred prod'].

    ASSUMPTION: the axiom nonterminal is only seen on the LHS of
    productions.  All nonterminals are derivable from axiom.

    DEFINITIONS:

    (a, prod, b) in TREE: exactly when production [prod] is "a ->
    .... b ...."  TREEPRED(b): { (a,p) | (a,p,b) in TREE }

    ALGORITHM:

    TOCOVER: set of productions that must be covered

    SEEN: set of nonterminals we've seen already

    initial state:

      (1) SEEN={}, TOCOVER=[]

      (2) if the initial production [initprod] enjoys [pred initprod]
    then we're done;

      (3) otherwise, add [initprod] to TOCOVER

    INVARIANTS:
        { lhs(p) | p in TOCOVER } is disjoint from SEEN
        for all p in TOCOVER: not (pred p)

    step:

      (1) select and remove a production [p] from TOCOVER

      (2) if [lhs(p)] is the axiom, and [pred p] is false, then fail

      (3) get the list of its direct predecessor productions
          pl=TREEPRED(lhs(p)) in the parse-tree relation.

      (4) add [lhs(p)] to SEEN

      (5) for each (a,prod) in pl:
            if not [pred prod] and a is not in SEEN then
              add prod to TOCOVER

    termination condition:

      when TOCOVER is empty

    success condition: we don't fail.

    Proof of termination: SEEN grows with each step iteration, and
    TOCOVER is always disjoint from SEEN.  So eventually there are no
    nonterminals that can be added to TOCOVER.  Each step iteration
    removes an element from TOCOVER.

    Correctness: consider a -covered- member [nt] of TOCOVER: either
    it satisfies the predicate, or some ancestor in the TREE relation
    satisfies the predicate.  Each step will replace [nt] with all its
    predecessors.  Eventually, every such predecessor will be replaced
    by a covered predecessor.

    Consider a -non-covered- member [nt] of TOCOVER: there must be a
    parse-tree in which from the axiom we can derive [nt] without
    passing thru a production that satisfies the predicate.  Repeated
    application of [step] will produce that path up to axiom, and the
    axiom is not covered.  QED.

*)

  value covers_with memo pred initpl =
    let open NTOps in
    let open AG in
    let ag = memo.ag in
    let rec covrec seen tocover =
      match tocover with [
        [] -> True
      | [p' :: tocover] ->
        let lhs = P.lhs p' in
        if lhs = ag.axiom && not (pred p') then False else
        let seen = [ lhs :: seen ] in
        let pred_pl = G.pred_e memo._PT lhs in
        let tocover = List.fold_left (fun tocover (a, prod', _) ->
            let prod' = match prod' with [ Some p -> p | None -> assert False ] in
            if not (pred prod') && not (List.mem a seen) then
              [prod' :: tocover] else tocover
          ) tocover pred_pl in
        covrec seen tocover
      ]
    in
    let initpl = List.filter (fun p -> not(pred p)) initpl in
    match initpl with [ [] -> True | _ -> covrec [] initpl ]
  ;
  (** an AG is well-formed2 if every attribute reference in all equations
      and conditions is declared in the typed attributes *)

  value well_formed_aref ag =
    let open AG in
    let open TAR in
    let open TNR in
    let open PN in
    fun [
      NT (PRIM _ _) "" -> True
    | NT (PARENT nt) attrna -> AG.node_attribute_exists ag (nt, attrna)
    | NT (CHILD nt _) attrna -> AG.node_attribute_exists ag (nt, attrna)
    | PROD pn attrna -> AG.production_attribute_exists ag (pn, attrna)
    | CHAINSTART pn (CHILD nt _) attrna -> AG.node_attribute_exists ag (nt, attrna)
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

  value chain_attributes_of ag nt =
    nt
  |> AG.node_attributes ag
  |> List.map (fun a -> (a, AG.attribute_type ag a))
  |> List.filter_map (fun (a, aty) -> if aty.AT.is_chain then Some a else None)
  ;

  value covers_chain ag attrna prod =
    prod.P.typed_equations |> List.exists (fun [
      {TAEQ.lhs=TAR.CHAINSTART _ (TNR.CHILD _ _) attrna'} -> attrna = attrna'
    | _ -> False
    ])
  ;

  value well_formed_chains0 m =
    let ag = m.NTOps.ag in
    let chain_attributes = ag.attribute_types |> List.filter_map (fun (ana, aty) ->
        if aty.AT.is_chain then Some ana else None) in
    chain_attributes |> List.for_all (fun cattr ->
        let pre = "pre_"^cattr in
        let post = "post_"^cattr in
        not(List.mem_assoc pre ag.attribute_types) &&
        not (List.mem_assoc post ag.attribute_types))
  ;

  value well_formed_chains1 m =
    let ag = m.NTOps.ag in
    (ag.nonterminals |> List.for_all (fun nt ->
         match chain_attributes_of ag nt with [
           [] -> True
         | l ->
           l |> List.for_all (fun attrna ->
               let pred prod = covers_chain ag attrna prod in
               let pl = AG.node_productions ag nt in
               covers_with m pred pl
             )
         ]
       ))
  ;

  value well_formed_chains m =
    well_formed_chains0 m && well_formed_chains1 m
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
    let loc = ag.loc in
    (well_formed2 m) &&
    (well_formed_chains m) &&
    (ag.nonterminals |> List.for_all (fun nt ->
         true_or_exn ~{exnf=fun() ->
             Ploc.raise loc
               (Failure Fmt.(str "well_formed: nonterminal %s: AI (@[<h>{ %a }@]) not disjoint from AS (@[<h>{ %a }@])"
                               nt
                               (list ~{sep=sp} string) (NTOps._AI m nt) 
                               (list ~{sep=sp} string) (NTOps._AS m nt)))}
           ([] = Std.intersect (NTOps._AI m nt) (NTOps._AS m nt))
    ))
    && (ag.productions |> List.for_all (fun (_, pl) ->
        pl |> List.for_all (fun p ->
            true_or_exn ~{exnf=fun () ->
                Ploc.raise loc
                  (Failure Fmt.(str "well_formed: in production %a defining occurrences are not distinct: { %a }"
                                  PN.pp_hum p.P.name
                                  (list ~{sep=sp} TAR.pp_hum) (POps.defining_occurrences p)))}
              (Std.distinct (POps.defining_occurrences p))
          )
      ))
  ;

  value complete m =
    let ag = m.NTOps.ag in
    let loc = ag.loc in
    (ag.nonterminals |> List.for_all (fun nt ->
         true_or_exn ~{exnf=fun () ->
             Ploc.raise loc
               (Failure Fmt.(str "complete: AG is not complete (nonterminal X = %s): sets (@[<h>A(X) = { %a }@]) != (@[<h>AI(X) = { %a }@]) union (@[<h>AS(X) = { %a }@])"
                               nt (list ~{sep=sp} string) (NTOps._A m nt)
                               (list ~{sep=sp} string) (NTOps._AI m nt)
                               (list ~{sep=sp} string) (NTOps._AS m nt)))}
           (Std.same_members (NTOps._A m nt) (Std.union (NTOps._AI m nt) (NTOps._AS m nt))) &&
         true_or_exn ~{exnf=fun () ->
             Ploc.raise loc
               (Failure Fmt.(str "complete: AG is not complete (nonterminal X = %s): sets (@[<h>A(X) = { %a }@]) != (@[<h>declared_attributes(X) = { %a }@])"
                               nt (list ~{sep=sp} string) (NTOps._A m nt)
                               (list ~{sep=sp} string) (List.assoc nt ag.node_attributes)
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

  (** [chain_to_copychains ag]

      This function takes an AG, assumed to be well-formed (per above),
      and replaces [@chain] attributes and CHAINSTART equations with
      normal attributes and copy-rules.  It fills-in chain-inferrable
      equations where missing.

      (a) collect every [@chain] attribute "a", check that "pre_a" and
      "post_a" are not already declared.

      (b) for each nonterminal "X" with a [@chain} attribute "a",
      replace it with "pre_a" and "post_a", neither of which are
      [@chain].  Also replace in the global attribute_types table.

      ================================================================

      (c) for every production for nonterminal X:

      (c.1) there can be defining and applied occurrences for "a" on
      the lhs, and on children with chain attribute a.  These can
      appear in equations that define the chain attribute, or define
      other attributes, either nodes or local attributes.

      Let's treat each of: defining occurrences for attributes of the
      parent/lhs, attributes of child nodes that do not define the
      chain attribute, local attributes, defining occurrences for
      attributes of child nodes that DO define the chain attribute.

      assume that child nodes that have the chain attribute are
      numbered [0..N).  N=0 means no such child nodes.

      (c.2) the production can also contain a CHAINSTART for attribute
      "a" on some nonterminal.

      So we'll handle these cases one-by-one.  Assume we have a
      production "X -> rhs", and that the child nodes with chain
      attribute "a" are numbered child_[0..N-1] (N=0 means no such
      children).  Assume that all rhs nonterminals are numbered
      rhs_[0..M-1].

      Also, we'll deal first with defining occurrence, and only then
      with applied occurrences.

      (d) [%chainstart child.(i)].a := rhs -- replace with regular
      equation "child_{i}.a := rhs".  If X has chain attribute "a", and
      if it hasn't a defining occurrence, add equation "X.a := X.a".

      At this point, we can proceed as if there are no CHAINSTART
      equations for "a".  Also, the parent node X has chain attribute
      "a".

      (e) parent node occurrences of "a".  If there are no defining
      occurrences of "a", and N=0, add equation "parent.a := parent.a";
      if N>0 then add equation "parent.a := child_{N-1}.a".

      (f) rhs nonterminals that do not have chain attributes "a" --
      nothing to do here.

      (g) rhs nonterminals that have chain attribute (hence, N>0):
      child_{i}.a -- if there is not a defining occurrence:

        if i = 0: add equation "child_{i=0}.a := parent.a"

        if i > 0: add equation "child_{i}.a := child_{i-1}.a"

      (h) local attributes cannot be chain attributes.

      ================================================================

      Now we can rewrite all occurrences to eliminate "a" in favor of
      "{pre,post}_a".

      (i) applied occurrences of "parent.a" are rewritten to
      "parent.pre_a".

      (j) defining occurrences "parent.a" are rewritten to
      "parent.post_a".

      (k) defining occurrences of "child_{i}.a" are rewritten to
      "child_{i}.pre_a".

      (l) referring occurrences of "child_{i}.a" are rewritten to
      "child_{i}.post_a".

   *)

  value augment_production ag cattr p =
    let loc = p.P.loc in
    let pnt = p.P.name.PN.nonterm_name in
    let defined_arefs = List.map TAEQ.lhs p.P.typed_equations in
    let cattr_children = (List.tl p.P.typed_nodes) |> List.filter_map TNR.(fun [
        (CHILD nt i) as cnr when AG.node_attribute_exists ag (nt, cattr) -> Some (cnr, (nt, i))
      | _ -> None
      ]) in
    let parent_has_cattr = AG.node_attribute_exists ag (pnt, cattr) in
    let has_chainstart = defined_arefs |> List.exists TAR.(fun [
        TAR.CHAINSTART _ cnr attr when cattr = attr -> True
      | _ -> False
      ]) in
    let (child_equations, last_nr, last_expr) =
      cattr_children
      |> List.mapi (fun i c -> (i,c))
      |> List.fold_left (fun (acc, prev_nr, prev_expr) (i, (cnr, (c_nt, c_index))) ->
          let newacc =
            if List.mem (TAR.NT cnr cattr) defined_arefs ||
               (i = 0 && has_chainstart) then acc else
              [TAEQ.{
                lhs = TAR.NT cnr cattr
              ; loc = loc
              ; msg = None
              ; rhs_nodes = [TAR.NT prev_nr cattr]
              ; rhs_expr = prev_expr
              } :: acc] in
          let newprev = <:expr< [%nterm $lid:c_nt$ . ( $int:string_of_int c_index$ );] . $lid:cattr$ >> in
          (newacc, cnr, newprev)
        ) ([], TNR.PARENT pnt, <:expr< [%nterm $lid:pnt$;] . $lid:cattr$ >>) in
    let parent_equations =
      if not parent_has_cattr then [] else
      if List.mem (TAR.NT (TNR.PARENT pnt) cattr) defined_arefs then [] else
      if has_chainstart then 
        (* parent.cattr := parent. cattr *)
        [TAEQ.{
            lhs=TAR.NT (TNR.PARENT pnt) cattr
          ; loc = p.P.loc
          ; msg = None
          ; rhs_nodes = [TAR.NT (TNR.PARENT pnt) cattr]
          ; rhs_expr = <:expr< [%nterm $lid:pnt$;] . $lid:cattr$ >>
          }]
      else
        (* parent.cattr := (last_child|parent). cattr *)
        [TAEQ.{
            lhs=TAR.NT (TNR.PARENT pnt) cattr
          ; loc = loc
          ; msg = None
          ; rhs_nodes = [TAR.NT last_nr cattr]
          ; rhs_expr = last_expr
          }] in
    let new_equations = parent_equations @ child_equations in
    if [] = new_equations then p else
    {(p) with
     P.typed_equations = p.P.typed_equations @ new_equations }
  ;

  value add_chain_attributes_once ag cattr =
    let open AG in
    let nt_needs_chain p =
      let pnt = p.P.name.PN.nonterm_name in
      let parent_has_cattr = AG.node_attribute_exists ag (pnt, cattr) in
      let child_has_cattr = (List.tl p.P.typed_nodes) |> List.exists TNR.(fun [
          CHILD nt i -> AG.node_attribute_exists ag (nt, cattr)
        | _ -> False
        ]) in
      let defined_arefs = List.map TAEQ.lhs p.P.typed_equations in
      let has_chainstart = defined_arefs |> List.exists TAR.(fun [
        TAR.CHAINSTART _ cnr attr when cattr = attr -> True
      | _ -> False
      ]) in
      child_has_cattr && not parent_has_cattr && not has_chainstart in
    let add_cattr_ntl = ag.productions |> List.filter_map (fun (pnt, pl) ->
      if pl |> List.exists nt_needs_chain then Some pnt else None) in
    let new_node_attributes = ag.node_attributes |> List.map (fun (nt, al) ->
      (nt, if List.mem nt add_cattr_ntl then [cattr :: al] else al)) in
    (add_cattr_ntl <> [], { (ag) with node_attributes = new_node_attributes})
  ;

  value add_chain_attributes ag cattr =
    let rec add1 ag =
      let (changed, ag) = add_chain_attributes_once ag cattr in
      if changed then add1 ag else ag
    in add1 ag
  ;

  value augment_one_chain ag cattr =
    let ag = add_chain_attributes ag cattr in
    let productions =
      ag.productions |> List.map (fun (nt, pl) ->
          (nt, List.map (augment_production ag cattr) pl)) in
    { (ag) with productions = productions }
  ;

  value augment_chains_with_copychains ag =
    let open AG in
    let chain_attributes = ag.attribute_types |> List.filter_map (fun (aname, at) ->
        if at.AT.is_chain then Some aname else None) in
    List.fold_left augment_one_chain ag chain_attributes
  ;

  value replace_rhs_tar cattr =
    let pre = "pre_"^cattr in
    let post = "post_"^cattr in
    let open TAR in
    let open TNR in
    fun [
      NT (PARENT _ as nt) a when a = cattr -> NT nt pre
    | NT (CHILD _ _ as nt) a when a = cattr -> NT nt post
    | x -> x
    ]
  ;

  value replace_rhs p cattr e =
    let dt = Camlp5_migrate.make_dt () in
    let fallback_migrate_expr = dt.migrate_expr in
    let migrate_expr dt e =
      let pn = p.P.name in
      try e |> TAR.expr_to_tar pn |> replace_rhs_tar cattr |> TAR.tar_to_expr (loc_of_expr e)
      with _ -> fallback_migrate_expr dt e in
    let dt = { (dt) with Camlp5_migrate.migrate_expr = migrate_expr } in
    dt.migrate_expr dt e
  ;

  value replace_equation ag cattr p e =
    let open TAEQ in
    let open TAR in
    let pre = "pre_"^cattr in
    let post = "post_"^cattr in
    let (parent, children) = match p.P.typed_nodes with [ [h :: t] -> (h,t) | _ -> assert False ] in
    let new_lhs = match e.lhs with [
      NT nt a when nt = parent && a = cattr ->
      NT parent post
    | NT cnt a when a = cattr && List.mem cnt children ->
      NT cnt pre
    | CHAINSTART _ cnt a when a = cattr && List.mem cnt children ->
      NT cnt pre
    | x -> x
    ] in
    let new_rhs_expr = replace_rhs p cattr e.rhs_expr in
    let new_rhs_nodes = List.map (replace_rhs_tar cattr) e.rhs_nodes in
    { (e) with
      lhs = new_lhs
    ; rhs_expr = new_rhs_expr
    ; rhs_nodes = new_rhs_nodes
    }
  ;

  value replace_production ag cattr p =
    let open AG in
    let open P in
    let new_typed_equations =
      List.map (replace_equation ag cattr p) p.typed_equations in
    let new_typed_conditions =
      List.map (replace_equation ag cattr p) p.typed_conditions in
    {(p) with
      typed_equations = new_typed_equations
    ; typed_conditions = new_typed_conditions
    }
  ;

  value replace_chain_attributes ag cattr =
    let open AG in
    let pre = "pre_"^cattr in
    let post = "post_"^cattr in
    let aty = {(List.assoc cattr ag.attribute_types) with AT.is_chain = False } in
    let new_attribute_types =
      ag.attribute_types
      |> List.remove_assoc cattr
      |> (fun l -> [(pre, aty); (post, aty)]@l) in
    let new_node_attributes =
      ag.node_attributes |> List.map (fun (nt, al) ->
          (nt,
           if List.mem cattr al then
             al |> Std.except cattr |> (fun l -> [pre; post]@l)
           else al)) in
    { (ag) with
      attribute_types = new_attribute_types
    ; node_attributes = new_node_attributes }
  ;

  value replace_one_chain ag cattr =
    let ag = replace_chain_attributes ag cattr in
    let productions =
      ag.productions |> List.map (fun (nt, pl) ->
          (nt, List.map (replace_production ag cattr) pl)) in
    { (ag) with productions = productions }
  ;

  value replace_chains_with_pre_post ag =
    let open AG in
    let chain_attributes = ag.attribute_types |> List.filter_map (fun (aname, at) ->
        if at.AT.is_chain then Some aname else None) in
    List.fold_left replace_one_chain ag chain_attributes
  ;


end
;
