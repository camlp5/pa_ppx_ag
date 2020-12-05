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
value is_builtin_ctyp z = List.mem (canon_ctyp z) builtin_types ;

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
  module PN = struct
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
  module ProductionName = PN ;

  module NR = struct
    type t = [
        PARENT of option string
      | CHILD of option string and int
      | PRIM of option string and int
      ] ;
    value expr_to_nterm e =
      match e with [
        <:expr< [%nterm $lid:tyname$;] >> -> 
        PARENT (Some tyname)
      | <:expr< [%nterm 0;] >> ->
        PARENT None
      | <:expr< [%nterm $int:n$;] >> ->
        CHILD None (int_of_string n)
      | <:expr< [%nterm $lid:tyname$ . ( $int:n$ );]  >> ->
        CHILD (Some tyname) (int_of_string n)

      | _ -> Ploc.raise (MLast.loc_of_expr e)
          (Failure Fmt.(str "expr_to_nterm: bad expr:@ %a"
                          Pp_MLast.pp_expr e))
      ]
    ;
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
  module NodeReference = NR ;
  module AR = struct
    type t = [
      NT of NR.t and string
    | PROD of PN.t and string
    | CHAINSTART of PN.t and NR.t and string
    | REMOTE of list (string * string)
    | CONSTITUENTS of list NR.t and list (string * string) and list string
    ]
    ;
    value rec pp_hum pps = fun [
      NT nr a -> Fmt.(pf pps "%a.%s" (NR.pp_hum ~{is_chainstart=False}) nr a)
    | PROD pn a -> Fmt.(pf pps "%a.%s" PN.pp_hum pn a)
    | CHAINSTART pn nr a ->
      Fmt.(pf pps "(* @%a *)%a.%s" PN.pp_hum pn (NR.pp_hum ~{is_chainstart=True}) nr a)
    | REMOTE l ->
      Fmt.(pf pps "{%a}" (list ~{sep=comma} (pair ~{sep=const string "."} string string)) l)
    | CONSTITUENTS nodes attrs shields ->
      Fmt.(pf pps "CONSTITUENTS [%a] ATTRIBUTES [%a] SHIELD [%a]"
             (list ~{sep=comma} (NR.pp_hum ~{is_chainstart=False})) nodes
             (list ~{sep=comma} (pair ~{sep=const string "."} string string)) attrs
             (list ~{sep=comma} string) shields)
    ]
    ;
    value pp_top pps x = Fmt.(pf pps "#<ar< %a >>" pp_hum x) ;


    value expr_to_lident_pair = fun [
      <:expr< $lid:l$ . $lid:r$ >> -> (l, r)
    | e -> Ploc.raise (MLast.loc_of_expr e)
        (Failure Fmt.(str "expr_to_lident_pair: not a lident pair:@ %a"
                        Pp_MLast.pp_expr e))
    ]
    ;
    open Pa_ppx_params.Runtime ;
    type lident_pair_ne_list_t = ne_list ((lident * lident) [@convert  ( [%typ: expr], expr_to_lident_pair );])
    [@@deriving params;]
    ;
    value expr_to_remote = fun [
      <:expr< [%remote $exp:e$;] >> ->
        e
        |> params_lident_pair_ne_list_t
        |> List.sort_uniq Stdlib.compare
        |> List.stable_sort Stdlib.compare
    | _ -> assert False
    ]
    ;
    value remote_to_expr loc l =
      let l = List.map (fun (p,a) -> <:expr< $lid:p$ . $lid:a$ >>) l in
      match l with [
        [_ ; _ :: _] -> <:expr< [%remote ( $list:l$ );] >>
      | [e] -> <:expr< [%remote $exp:e$ ;] >>
      | [] -> assert False
      ]
    ;

    type nr_t = NR.t ;
    value params_nr_t = NR.expr_to_nterm ;
    type constituents_t = {
      nodes : ne_list nr_t
    ; attributes : lident_pair_ne_list_t [@default [];]
    ; shield : list lident [@default [];]
    } [@@deriving params;]
    ;

    value expr_to_ar pn e =
      match e with [

        <:expr< [%chainstart $int:n$;] . $lid:attrna$ >> ->
        CHAINSTART pn (NR.CHILD None (int_of_string n)) attrna
      | <:expr< [%chainstart $lid:tyname$ . ( $int:n$ );] . $lid:attrna$ >> ->
        CHAINSTART pn (NR.CHILD (Some tyname) (int_of_string n)) attrna

      | <:expr< $e$ . $lid:attrna$ >> -> 
        NT (NR.expr_to_nterm e) attrna

      | <:expr< [%prim $int:n$;] >> ->
        NT (NR.PRIM None (int_of_string n)) ""
      | <:expr< [%local $lid:attrna$;] >> ->
        PROD pn attrna

      | <:expr< [%remote $exp:_$;] >> -> REMOTE (expr_to_remote e)

      | <:expr< [%constituents $exp:e$;] >> ->
        let c = params_constituents_t e in
        let nodes =
          c.nodes
          |> List.sort_uniq Stdlib.compare
          |> List.stable_sort Stdlib.compare in
        let attributes =
          c.attributes
          |> List.sort_uniq Stdlib.compare
          |> List.stable_sort Stdlib.compare in
        let shield =
          c.shield
          |> List.sort_uniq Stdlib.compare
          |> List.stable_sort Stdlib.compare in

        CONSTITUENTS nodes attributes shield

      | _ -> Ploc.raise (MLast.loc_of_expr e)
          (Failure Fmt.(str "expr_to_ar: bad expr:@ %a"
                          Pp_MLast.pp_expr e))
      ]
    ;
  end ;

  module TNR = struct
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


    value expr_to_nterm e =
      match e with [
        <:expr< [%nterm $lid:tyname$;] >> -> 
        PARENT tyname

      | <:expr< [%nterm $lid:tyname$ . ( $int:n$ );] >> ->
        CHILD tyname (int_of_string n)

      | _ -> Ploc.raise (MLast.loc_of_expr e)
          (Failure Fmt.(str "expr_to_nterm: bad expr:@ %a"
                          Pp_MLast.pp_expr e))
  ]
  ;
  end
  ;
  module TypedNodeReference = TNR ;
  module TAR = struct
    type t = [
      NT of TNR.t and string
    | PROD of PN.t and string
    | CHAINSTART of PN.t and TNR.t and string
    | REMOTE of list (string * string)
    | CONSTITUENTS of list TNR.t and list (string * string) and list string
    ]
    ;
    value pp_hum pps = fun [
      NT nr a -> Fmt.(pf pps "%a.%s" (TNR.pp_hum ~{is_chainstart=False}) nr a)
    | PROD pn a -> Fmt.(pf pps "%a.%s" PN.pp_hum pn a)
    | CHAINSTART pn nr a ->
      Fmt.(pf pps "(* @%a *)%a.%s" PN.pp_hum pn (TNR.pp_hum ~{is_chainstart=True}) nr a)
    | REMOTE l ->
      Fmt.(pf pps "{%a}" (list ~{sep=comma} (pair ~{sep=const string "."} string string)) l)
    | CONSTITUENTS nodes attrs shields ->
      Fmt.(pf pps "CONSTITUENTS [%a] ATTRIBUTES [%a] SHIELD [%a]"
             (list ~{sep=comma} (TNR.pp_hum ~{is_chainstart=False})) nodes
             (list ~{sep=comma} (pair ~{sep=const string "."} string string)) attrs
             (list ~{sep=comma} string) shields)
    ]
    ;
    value pp_top pps x = Fmt.(pf pps "#<tar< %a >>" pp_hum x) ;

    open Pa_ppx_params.Runtime ;
    type tnr_t = TNR.t ;
    value params_tnr_t = TNR.expr_to_nterm ;
    type constituents_t = {
      nodes : ne_list tnr_t
    ; attributes : AR.lident_pair_ne_list_t [@default [];]
    ; shield : list lident [@default [];]
    } [@@deriving params;]
    ;

    value of_expr pn e =
      let open TNR in
      match e with [

        <:expr< [%chainstart $lid:tyname$ . ( $int:n$ );] . $lid:attrna$ >> ->
        CHAINSTART pn (CHILD tyname (int_of_string n)) attrna

      | <:expr< $e$ . $lid:attrna$ >> -> 
        NT (TNR.expr_to_nterm e) attrna

      | <:expr< [%prim $lid:tyname$ . ( $int:n$ );] >> ->
        NT (PRIM tyname (int_of_string n)) ""

      | <:expr< [%local $lid:attrna$;] >> ->
        PROD pn attrna

      | <:expr< [%remote $exp:_$;] >> ->
        REMOTE (AR.expr_to_remote e)

      | <:expr< [%constituents $exp:e$;] >> ->
        let c = params_constituents_t e in
        CONSTITUENTS c.nodes c.attributes c.shield

      | _ -> Ploc.raise (MLast.loc_of_expr e)
          (Failure Fmt.(str "expr_to_attribute_reference: bad expr:@ %a"
                          Pp_MLast.pp_expr e))
  ]
  ;

  value to_expr loc e =
    let open TNR in
    match e with [
      NT (PRIM tyname n) "" ->
      <:expr< [%prim $lid:tyname$ . ( $int:string_of_int n$ );] >>

    | NT tnr attrna ->
      <:expr< $TNR.to_expr loc tnr$ . $lid:attrna$ >>

    | PROD pn attrna ->
      <:expr< [%local $lid:attrna$;] >>

    | CHAINSTART pn (CHILD tyname n) attrna ->
      <:expr< [%chainstart $lid:tyname$ . ( $int:string_of_int n$ );] . $lid:attrna$ >>

    | REMOTE l -> AR.remote_to_expr loc l

    | CONSTITUENTS nodes attributes shield ->
      let nodes = Ppxutil.convert_up_list_expr loc (List.map (TNR.to_expr loc) nodes) in
      let attributes = Ppxutil.convert_up_list_expr loc (List.map (fun (a,b) -> <:expr< $lid:a$ . $lid:b$ >>) attributes) in
      let shield = Ppxutil.convert_up_list_expr loc (List.map (fun a -> <:expr< $lid:a$ >>) shield) in
      <:expr< [%constituents { nodes = $nodes$ ; attributes = $attributes$ ; shield = $shield$ } ;] >>
    ]
    ;
  end ;

  value wrap_comment pp1 pps x = Fmt.(pf pps "(* %a *)" pp1 x) ;

  module AEQ = struct
    type t = {
      loc : Ploc.t
    ; lhs : AR.t
    ; rhs_nodes : list AR.t
    ; rhs_expr : MLast.expr
    }
    ;
    value pp_hum pps x =
        Fmt.(pf pps "%a := %a" AR.pp_hum x.lhs Pp_hum.expr x.rhs_expr) ;
    value pp_top pps x = Fmt.(pf pps "#<aeq< %a >>" pp_hum x) ;
  end ;

  module ASide = struct
    type t = {
      loc : Ploc.t
    ; rhs_nodes : list AR.t
    ; rhs_expr : MLast.expr
    }
    ;
    value pp_hum pps x =
      Fmt.(pf pps "side-effect %a" Pp_hum.expr x.rhs_expr)
    ;
    value pp_top pps x = Fmt.(pf pps "#<side< %a >>" pp_hum x) ;
  end ;

  module TAEQ = struct
    type t = {
      loc : Ploc.t
    ; lhs : TAR.t
    ; rhs_nodes : list TAR.t
    ; rhs_expr : MLast.expr
    }
    ;
    value lhs e = e.lhs ;
    value rhs_expr e = e.rhs_expr ;
    value rhs_nodes e = e.rhs_nodes ;
    value pp_hum pps x =
      Fmt.(pf pps "%a := %a" TAR.pp_hum x.lhs Pp_hum.expr x.rhs_expr) ;
    value pp_top pps x = Fmt.(pf pps "#<taeq< %a >>" pp_hum x) ;

    value remote_upward_attributes e =
      e.rhs_nodes |> List.filter (fun [ TAR.REMOTE _ -> True | _ -> False ])
    ;
    value constituents_references e =
      e.rhs_nodes |> List.filter (fun [ TAR.CONSTITUENTS _ _ _ -> True | _ -> False ])
    ;
  end ;

  module TSide = struct
    type t = {
      loc : Ploc.t
    ; rhs_nodes : list TAR.t
    ; rhs_expr : MLast.expr
    }
    ;
    value rhs_expr e = e.rhs_expr ;
    value rhs_nodes e = e.rhs_nodes ;
    value pp_hum pps x =
      Fmt.(pf pps "side-effect %a"
             Pp_hum.expr x.rhs_expr
          )
    ;
    value pp_top pps x = Fmt.(pf pps "#<tside< %a >>" pp_hum x) ;
  end ;

  module P = struct
    type t = {
      name : PN.t
    ; loc : Ploc.t
    ; typed_nodes : list TNR.t
    ; typed_node_names : list (NR.t * TNR.t)
    ; typed_equations : list TAEQ.t
    ; typed_side_effects : list TSide.t
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
             (list ~{sep=sp} TSide.pp_hum) x.typed_side_effects
          ) ;
    value pp_top pps x = Fmt.(pf pps "#<prod< %a >>" pp_hum x) ;

    value typed_nr ~{is_chainstart} loc p nr =
      match List.assoc nr p.typed_node_names with [
        x -> x
      | exception Not_found ->
        Ploc.raise loc (Failure Fmt.(str "nonterminal %a could not be converted to its typed form"
                                       (NR.pp_hum ~{is_chainstart}) nr))
    ]
    ;
    value typed_attribute loc p =
      fun [
      (AR.NT nr attrna) as ar ->
      TAR.NT (typed_nr ~{is_chainstart=False} loc p nr) attrna
    | AR.PROD pn attrna -> TAR.PROD pn attrna
    | AR.CHAINSTART pn nr attrna ->
      TAR.CHAINSTART pn (typed_nr ~{is_chainstart=True} loc p nr) attrna
    | AR.REMOTE l -> TAR.REMOTE l
    | AR.CONSTITUENTS a b c ->
      let a = List.map (typed_nr ~{is_chainstart=False} loc p) a in
      TAR.CONSTITUENTS a b c
    ]
    ;
    value typed_rhs loc p e =
      let dt = Camlp5_migrate.make_dt () in
      let fallback_migrate_expr = dt.migrate_expr in
      let migrate_expr dt e =
        let pn = p.name in
        try e |> AR.expr_to_ar pn |> typed_attribute loc p |> TAR.to_expr (loc_of_expr e)
        with _ -> fallback_migrate_expr dt e in
      let dt = { (dt) with Camlp5_migrate.migrate_expr = migrate_expr } in
      dt.migrate_expr dt e
    ;
    value typed_side_effect p aeq =
      let { ASide.loc = loc ; rhs_nodes = rhs_nodes ; rhs_expr = rhs_expr } = aeq in
      {
        TSide.loc = loc
      ; rhs_nodes = List.map (typed_attribute loc p) rhs_nodes
      ; rhs_expr = typed_rhs loc p rhs_expr
      }
    ;
    value typed_equation p aeq =
      let { AEQ.loc = loc; lhs = lhs ; rhs_nodes = rhs_nodes ; rhs_expr = rhs_expr } = aeq in
      {
        TAEQ.loc = loc
      ; lhs = typed_attribute loc p lhs
      ; rhs_nodes = List.map (typed_attribute loc p) rhs_nodes
      ; rhs_expr = typed_rhs loc p rhs_expr
      }
    ;
    value remote_upward_attributes p =
      (p.typed_equations |> List.concat_map TAEQ.remote_upward_attributes)
    ;
    value constituents_references p =
      (p.typed_equations |> List.concat_map TAEQ.constituents_references)
    ;
    value parent_nonterminal p = p.name.PN.nonterm_name ;
    value child_nonterminals p =
      p.typed_nodes |> List.filter_map (fun [ TNR.CHILD cnt _ -> Some cnt | _ -> None ])
    ;
    value map_typed_equations f p =
      {(p) with typed_equations = List.map f p.typed_equations }
    ;
    value map_typed_side_effects f p =
      {(p) with typed_side_effects = List.map f p.typed_side_effects }
    ;
  end ;
  module Production = P ;

  module AT = struct
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
  module AttributeType = AT ;
  type t = {
    loc : Ploc.t
  ; storage_mode : storage_mode_t
  ; axiom : string
  ; attribute_types : list (string * AT.t)
  ; node_attributes : list (string * (list string))
  ; production_attributes : list (string * (list string))
  ; nonterminals : list string
  ; equations : list (PN.t * (list AEQ.t))
  ; side_effects : list (PN.t * (list ASide.t))
  ; productions : list (string * list P.t)
  }
  ;
  value mk0 loc storage_mode axiom nonterminals
    (attribute_types, node_attributes, production_attributes)
    equations side_effects = {
    loc = loc
  ; storage_mode = storage_mode
  ; axiom = axiom
  ; nonterminals = nonterminals
  ; attribute_types = attribute_types |> List.map (fun (ana, aty) -> (ana, AT.mk aty))
  ; node_attributes = node_attributes
  ; production_attributes = production_attributes
  ; equations = equations
  ; side_effects = side_effects
  ; productions = []
  }
  ;
  value all_productions ag =
    ag.productions |> List.concat_map (fun (_, pl) -> pl)
  ;
  value map_productions f ag =
    { (ag) with productions =
      ag.productions |> List.map (fun (nt, pl) -> (nt, (pl |> List.map (f nt)))) }
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
    | exception Not_found ->
      Ploc.raise ag.loc
        (Failure Fmt.(str "node_attributes: nonterminal %s has no attributes -- surely this is an error" nt))
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
  value is_declared_attribute ag attrna = List.mem_assoc attrna ag.attribute_types ;
  value attribute_type ag attrna =
    match List.assoc attrna ag.attribute_types with [
      x -> x
    | exception Not_found ->
      Ploc.raise ag.loc (Failure Fmt.(str "attribute_type: attribute %s has no declared type" attrna))
    ]
  ;

  value remote_upward_attributes ag =
    let open P in
    let open TAEQ in
    ag.productions
    |> List.concat_map (fun (nt, pl) ->
        pl |> List.concat_map P.remote_upward_attributes)
    |> List.sort_uniq Stdlib.compare
    |> List.stable_sort Stdlib.compare
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

value assignment_to_equation_or_side_effect pn e = match e with [
    <:expr:< $lhs$ . val := $rhs$ >> | <:expr:< $lhs$ := $rhs$ >> ->
    Left {
      AG.AEQ.loc = loc
    ; lhs = AG.AR.expr_to_ar pn lhs
    ; rhs_nodes = extract_attribute_references pn rhs
    ; rhs_expr = rhs }

  | <:expr:< condition $str:msg$ $e$ >> ->
    Right { 
      AG.ASide.loc = loc
    ; rhs_nodes = extract_attribute_references pn e
    ; rhs_expr = <:expr< if not $e$ then failwith $str:msg$ else () >> }
  | <:expr:< condition $e$ >> ->
    let msg = Fmt.(str "condition %a failed" Pp_MLast.pp_expr e) in
    Right { 
      AG.ASide.loc = loc
    ; rhs_nodes = extract_attribute_references pn e
    ; rhs_expr = <:expr< if not $e$ then failwith $str:msg$ else () >> }

  | e ->
    let loc = MLast.loc_of_expr e in
    Right { 
      AG.ASide.loc = loc
    ; rhs_nodes = extract_attribute_references pn e
    ; rhs_expr = e }

  | _ -> Ploc.raise (MLast.loc_of_expr e)
      (Failure Fmt.(str "assignment_to_equation_or_side_effect: neither assignment nor condition/side-effect@ %a"
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

value extract_attribute_equations_and_side_effects loc l : (list (AG.PN.t * (list (choice AG.AEQ.t AG.ASide.t)))) =
  l |> List.map (fun (prodname, e) ->
    let prodname = parse_prodname loc prodname in
    match e with [
      <:expr< do { $list:l$ } >> ->
      (prodname, List.map (assignment_to_equation_or_side_effect prodname) l)
    | <:expr< $_$ . val := $_$ >> | <:expr< $_$ := $_$ >> ->
      (prodname, [assignment_to_equation_or_side_effect prodname e])
    | _ -> Ploc.raise (MLast.loc_of_expr e)
        (Failure Fmt.(str "extract_attribute_equations_and_side_effects (production %a): unrecognized@ %a"
                        AG.PN.pp_hum prodname Pp_MLast.pp_expr e))
    ])
;

value extract_attribute_equations loc l : (list (AG.PN.t * (list AG.AEQ.t))) =
  extract_attribute_equations_and_side_effects loc l
  |> List.map (fun (n, l) ->
                (n, l |> List.filter_map (fun [ Left e -> Some e | _ -> None ])))
;

value extract_attribute_side_effects loc l : (list (AG.PN.t * (list AG.ASide.t))) =
  extract_attribute_equations_and_side_effects loc l
  |> List.map (fun (n, l) ->
                (n, l |> List.filter_map (fun [ Right c -> Some c | _ -> None ])))
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

module NA = struct
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
module NodeAliases = NA ;

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
    | <:ctyp:< $lid:tyname$ >> as z when is_builtin_ctyp z -> do {
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
  let side_effects = match List.assoc pn ag.side_effects with [ x -> x | exception Not_found -> [] ] in
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
  ; typed_side_effects = []
  ; patt = Patt.tuple loc (List.map Std.fst3 patt_nref_l)
  ; patt_var_to_noderef = List.map Std.snd3 patt_nref_l
  ; rev_patt_var_to_noderef = patt_nref_l |> List.map Std.snd3 |> List.map (fun (a,b) -> (b,a))
  ; patt_var_to_childnum = List.map Std.third3 patt_nref_l
  } in
  let typed_equations = List.map (P.typed_equation p) equations in
  let typed_side_effects = List.map (P.typed_side_effect p) side_effects in
  { (p) with
    P.typed_equations = typed_equations
  ; typed_side_effects = typed_side_effects
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
  ; side_effects = []
  }
;

end
;

module AGOps = struct
  open AG ;

  module POps = struct
    value attribute_occurrences p =
      p.P.typed_equations
      |> List.map (fun teq -> [teq.TAEQ.lhs :: teq.TAEQ.rhs_nodes])
      |> List.concat ;

    value defining_occurrences p =
      (List.map (fun teq -> teq.TAEQ.lhs) p.P.typed_equations)
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
           List.map (fun rhs_ar -> (rhs_ar, teq.lhs)) teq.rhs_nodes))
    ;

  end ;

  module NTOps = struct
    value _attributes_of ag ntname =
      ag
      |> AG.all_productions
      |> List.map POps.attribute_occurrences |> List.concat
      |> List.filter_map (fun [
          TAR.NT (TNR.CHILD n _) attrna when n = ntname -> Some attrna
        | TAR.NT (TNR.PARENT n) attrna when n = ntname -> Some attrna
        | _ -> None
        ])
      |> List.sort_uniq Stdlib.compare |> List.stable_sort Stdlib.compare
    ;

    value _inherited_attributes_of ag ntname =
      ag
      |> AG.all_productions
      |> List.map POps.inherited_occurrences |> List.concat
      |> List.filter_map (fun [
          TAR.NT (TNR.CHILD n _) attrna when n = ntname -> Some attrna
        | _ -> None
        ])
      |> List.sort_uniq Stdlib.compare |> List.stable_sort Stdlib.compare
    ;
    value _synthesized_attributes_of ag ntname =
      ag
      |> AG.all_productions
      |> List.map POps.synthesized_occurrences |> List.concat
      |> List.filter_map (fun [
          TAR.NT (TNR.PARENT n) attrna when n = ntname -> Some attrna
        | _ -> None
        ])
      |> List.sort_uniq Stdlib.compare |> List.stable_sort Stdlib.compare
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
      List.fold_left (fun g p ->
          let lhs = List.hd p.P.typed_nodes in
          let rhsl = List.tl p.P.typed_nodes in
          List.fold_left (fun g rhs -> add_edge g (lhs, p, rhs)) g rhsl)
        g (AG.all_productions ag)
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

  value true_or_exn ~{exnf} x = if x then x else exnf() ;

  value well_formed_aref0 loc ag =
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

  value well_formed_aref loc ag x =
    true_or_exn ~{exnf=fun () ->
      Ploc.raise loc (Failure Fmt.(str "not a well-formed attribute ref: %a"
                                     TAR.pp_hum x))}
    (well_formed_aref0 loc ag x)
  ;

  value well_formed_equation0 ag pn teq =
    let open AG.TAEQ in
    well_formed_aref teq.loc ag teq.lhs &&
    List.for_all (well_formed_aref teq.loc ag) teq.rhs_nodes
  ;

  value well_formed_equation ag pn teq =
    let open AG.TAEQ in
    true_or_exn ~{exnf=fun () ->
        Ploc.raise teq.loc (Failure Fmt.(str "not a well-formed equation in production %a: %a"
                                           PN.pp_hum pn
                                           TAEQ.pp_hum teq))}
      (well_formed_equation0 ag pn teq)
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
        not(AG.is_declared_attribute ag pre) &&
        not (AG.is_declared_attribute ag post))
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
    ag |> AG.all_productions |> List.for_all (fun p ->
         p.P.typed_equations |> List.for_all (well_formed_equation ag p.P.name) &&
         [] = p.P.typed_side_effects
       )
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
    && (ag |> AG.all_productions |> List.for_all (fun p ->
            true_or_exn ~{exnf=fun () ->
                Ploc.raise loc
                  (Failure Fmt.(str "well_formed: in production %a defining occurrences are not distinct: { %a }"
                                  PN.pp_hum p.P.name
                                  (list ~{sep=sp} TAR.pp_hum) (POps.defining_occurrences p)))}
              (Std.distinct (POps.defining_occurrences p))
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
                               (list ~{sep=sp} string) (AG.node_attributes ag nt)
                               ))}
           (Std.same_members (NTOps._A m nt)
        (AG.node_attributes ag nt))
    ))
    && (ag |> AG.all_productions |> List.for_all (fun p ->
               (List.tl p.P.typed_nodes) |> List.for_all (fun node ->
                   match node with [
                     TNR.PARENT nt ->
                     let synthesized = NTOps._AS m nt in
                     let occurrences = List.map (fun a -> TAR.NT node a) synthesized in
                     true_or_exn ~{exnf=fun () ->
                         Ploc.raise loc
                           (Failure Fmt.(str "complete: production %s AS(%s) @[<h>({ %a })@] not a subset of defining_occurrences @[<h>({ %a })@]"
                                           (PN.unparse p.P.name)
                                           nt
                                           (list ~{sep=sp} TAR.pp_hum) occurrences
                                           (list ~{sep=sp} TAR.pp_hum) (POps.defining_occurrences p)))}
                       (Std.subset occurrences (POps.defining_occurrences p))
                   | TNR.CHILD nt _ ->
                     let inherited = NTOps._AI m nt in
                     let occurrences = List.map (fun a -> TAR.NT node a) inherited in
                     true_or_exn ~{exnf=fun () ->
                         Ploc.raise loc
                           (Failure Fmt.(str "complete: production %s AI(%s) @[<h>({ %a })@] not a subset of defining_occurrences @[<h>({ %a })@]"
                                           (PN.unparse p.P.name)
                                           nt
                                           (list ~{sep=sp} TAR.pp_hum) occurrences
                                           (list ~{sep=sp} TAR.pp_hum) (POps.defining_occurrences p)))}
                       (Std.subset occurrences (POps.defining_occurrences p))
                   | TNR.PRIM _ _ -> True
                   ]
                 )))
    && ([] = NTOps._AI m ag.axiom)
    && True
  ;

  value locally_acyclic m =
    let ag = m.NTOps.ag in
    ag |> AG.all_productions |> List.for_all (fun p ->
        true_or_exn ~{exnf=fun () ->
            Ploc.raise ag.AG.loc
              (Failure Fmt.(str "locally_acyclic: production %s is locally cyclic\n%a"
                              (PN.unparse p.P.name)
                              P.pp_hum p))}
          (let ddp = POps.direct_reference_graph p in
        not Tsort0.(cyclic (nodes ddp) (mkadj ddp)))
      )
  ;

  module Chain = struct

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
          ; rhs_nodes = [TAR.NT (TNR.PARENT pnt) cattr]
          ; rhs_expr = <:expr< [%nterm $lid:pnt$;] . $lid:cattr$ >>
          }]
      else
        (* parent.cattr := (last_child|parent). cattr *)
        [TAEQ.{
            lhs=TAR.NT (TNR.PARENT pnt) cattr
          ; loc = loc
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
      try e |> TAR.of_expr pn |> replace_rhs_tar cattr |> TAR.to_expr (loc_of_expr e)
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
    {(p) with
      typed_equations = new_typed_equations
    }
  ;

  value replace_chain_attributes ag cattr =
    let open AG in
    let pre = "pre_"^cattr in
    let post = "post_"^cattr in
    let aty = {(AG.attribute_type ag cattr) with AT.is_chain = False } in
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

  module SideEffect = struct

  value rewrite_side_effect_production ag p = do {
    let open AG in
    let open P in
    let loc = ag.AG.loc in
    assert (production_attribute_exists ag (p.name, "side_effect")) ;
    assert ([] <> p.typed_side_effects) ;
    let new_rhs_expr =
      let sidel = List.map TSide.rhs_expr p.typed_side_effects in
      let l = sidel @ [ <:expr< () >> ] in
      <:expr< do { $list:l$ } >> in
    let new_rhs_nodes =
      p.typed_side_effects
      |> List.concat_map TSide.rhs_nodes
      |> List.sort_uniq Stdlib.compare in
    let new_eqn = {
      TAEQ.loc = MLast.loc_of_expr new_rhs_expr
    ; lhs = TAR.PROD p.name "side_effect"
    ; rhs_nodes = new_rhs_nodes
    ; rhs_expr = new_rhs_expr
    } in
    {(p) with typed_side_effects = [] ; typed_equations = [new_eqn :: p.typed_equations]}
  }
  ;

  value rewrite_side_effect_equations ag =
    ag |> AG.map_productions (fun nt p ->
        if p.P.typed_side_effects = [] then p
        else
          rewrite_side_effect_production ag p
      )
    ;

  value add_side_effect_attributes ag =
    let open AG in
    let open P in
    let open TAEQ in
    let loc = ag.AG.loc in
    let side_effect_pns = ag |> AG.all_productions |> List.filter_map (fun p ->
        if p.typed_side_effects <> [] &&
           not(production_attribute_exists ag (p.name, "side_effect")) then
          Some (PN.unparse p.name)
        else None
      ) in
    let ag = side_effect_pns |> List.fold_left (fun ag pn ->
        let old_al = AG.production_attributes ag pn in
        {(ag) with
         production_attributes =
           ag.production_attributes
           |> List.remove_assoc pn
           |> (fun l -> [(pn, ["side_effect" :: old_al]) :: l])
        }
      ) ag in
    let new_productions =
      if ag.storage_mode = Hashtables then ag.productions else
        ag.productions |> List.map (fun (nt, pl) -> (nt, pl |> List.map (fun p ->
        let loc = p.P.loc in
        if [] = AG.production_attributes ag (PN.unparse p.name) then p else
        let new_patt = match p.patt with [
          <:patt< $_$ prod_attrs >> -> p.patt
        | <:patt< ( $list:_$ ) >>  -> p.patt
        | _ -> <:patt< $p.patt$ prod_attrs >>
        ] in
        {(p) with patt = new_patt }
      ))) in
    let ag = {(ag) with productions = new_productions } in
    if not (AG.is_declared_attribute ag "side_effect") then
      {(ag) with
       attribute_types = [("side_effect", AT.mk <:ctyp< unit >>) :: ag.attribute_types]}
    else ag
  ;

  value rewrite_side_effects ag =
    ag |> add_side_effect_attributes |> rewrite_side_effect_equations
  ;

  end
  ;

  value add_new_attribute ag (new_attr, ty) ntl =
    let open AG in
    let ag = {
      (ag) with
      attribute_types = [(new_attr, AT.mk ty) :: ag.attribute_types]
    } in
    let ag = {
      (ag) with
      node_attributes =
        ag.node_attributes |> List.map (fun (nt, al) ->
            (nt, if List.mem nt ntl then [new_attr :: al] else al))
    } in
    ag
  ;

  module RUA = struct
  (** remote upward attribute sets

      (1) syntax: [%remote X.a, Y.b, Z.c]

      (2) check that a,b,c all have the same type

      (3) check that X.a, Y.b and Z.c all are declared properly

      (4) check that X,Y,Z are distinct

      (5) compute new attribute-name, as (a) sort set, then (b) concat
     with "__"

      (6) If one of the X,Y,Z is the LHS of the production, then
     rewrite the remote attribute-set to a local reference to that
     attribute of the LHS.

      (7) Otherwise, we need to compute the set S of nonterminals that
     need this new attribute #5.

          (a) S starts with { LHS }

          (b) for every production P whose LHS is not the axiom, and
          with a RHS nonterminal in S, and whose LHS is not one of X,Y,Z,
          add P.LHS to S.

          (c) success condition: RHS nonterminals of productions whose LHS
          is the axiom, are NOT in S.

      (8) Now, for every production whose LHS is not in S, but
          has a RHS child X in S, add the equation:

          X.{#5 attribute name} := LHS.{relevant attribute name from upward remote set}

      (9) for every production who LHS is in S, and has a RHS child X in S,
          add the equation:

          X.{#5 attribute name} := LHS.{#5 attribute name}

      (10) add {#5 attribute name} as an attribute to every nonterminal in S.

      (11) declare {#5 attribute name} with type of X.a

  *)

  value rua_to_attribute = fun [
    TAR.REMOTE l ->
    l |> List.concat_map (fun (a,b) -> [a;b]) |> String.concat "__"
  | _ -> assert False ]
  ;

  value rua_to_nt_aref ag rua nt =
    let l = match rua with [ TAR.REMOTE l -> l | _ -> assert False ] in
    l |> List.find_map (fun [
        (n,a) when nt = n && AG.node_attribute_exists ag (n,a) -> Some a
      | _ -> None
      ])
  ;

  value nt_satisfies_rua ag rua nt =
    None <> rua_to_nt_aref ag rua nt
  ;

  value rua_production_step ag rua sofar p =
    let parent_nt = P.parent_nonterminal p in
    let child_nts = P.child_nonterminals p in
    if not (List.mem parent_nt sofar) && not (nt_satisfies_rua ag rua parent_nt) &&
       [] <> Std.intersect (P.child_nonterminals p) sofar then
      Some parent_nt else None
  ;

  value rua_nonterminals_step ag rua sofar =
    let open AG in
    let open P in
    let open TAEQ in
    ag |> AG.all_productions |> List.filter_map (rua_production_step ag rua sofar)
    |> List.sort_uniq Stdlib.compare
  ;

  value production_uses_rua rua p =
    List.mem rua (P.remote_upward_attributes p)
  ;

  value nt_uses_rua ag rua nt =
    let pl = AG.node_productions ag nt in
    pl |> List.exists (production_uses_rua rua)
  ;

  value rua_nonterminals ag rua init =
    let rec setrec sofar =
      let addl = rua_nonterminals_step ag rua sofar in
      if addl = [] then sofar
      else setrec (addl@sofar)
    in do {
      assert (init |> List.for_all (nt_uses_rua ag rua)) ;
      setrec init
    }
  ;

  value rua_type ag rua =
    let aname = match rua with [
      TAR.REMOTE [(_, aname) :: _] -> aname
    | _ -> assert False
    ] in
    (AG.attribute_type ag aname).AT.ty
  ;

  (** replace_rua:

      (1) compute full list of nonterminals that need the new
     attribute

      (2) declare the new attribute's type

      (3) add the new attribute to the list from #1

      (4) stitch thru equations to copy-chain the new attribute: for
     each production:

          (a) if the LHS is not in list #1 and there is a child in
     list #1, then *perforce* the LHS must satisfy the RUA (have a
     satisfying attribute).  Add an equation copying it to each child
     that is in list #1.

          (b) if both LHS and child are in list #1, then add an
     equation copying it to the child.

      (5) rewrite matching RUAs using the attribute:

          (a) if the LHS is not in list #1 but satisfies the RUA, then
     rewrite all instances of the RUA in equations/conditions to use
     the LHS attribute.

          (b) if the LHS is in list #1 then rewrite all instances of
     teh RUA in equations/conditions to use the new attribute on the
     LHS.

  *)

  value rua_copy_equation loc (cnr, new_attr) (parent, p_attr) =
    let lhs = TAR.NT cnr new_attr in
    let rhs = TAR.NT (TNR.PARENT parent) p_attr in
    Some {
        TAEQ.loc = loc
      ; lhs = lhs
      ; rhs_nodes = [rhs]
      ; rhs_expr = TAR.to_expr loc rhs
      }
  ;

  value replace_rua_tar rua rua_tar =
    let open TAR in
    let open TNR in
    fun [
      REMOTE _ as a when a = rua -> rua_tar
    | x -> x
    ]
  ;

  value replace_rhs_expr_rua p rua new_tar e =
    let dt = Camlp5_migrate.make_dt () in
    let fallback_migrate_expr = dt.migrate_expr in
    let pn = p.P.name in
    let migrate_expr dt e =
      try e |> TAR.of_expr pn |> replace_rua_tar rua new_tar |> TAR.to_expr (loc_of_expr e)
      with _ -> fallback_migrate_expr dt e in
    let dt = { (dt) with Camlp5_migrate.migrate_expr = migrate_expr } in
    dt.migrate_expr dt e
  ;

  value stitch_rua_copy_chain ag rua new_attr ntl =
    let open AG in
    let open P in
    ag |> AG.map_productions (fun nt p ->
        let loc = p.loc in
        let parent = P.parent_nonterminal p in
        let children = P.child_nonterminals p in
        let copy_equations = match (List.mem (P.parent_nonterminal p) ntl,
                                    ([] <> Std.intersect children ntl),
                                    rua_to_nt_aref ag rua parent) with [
          (True, True, None) ->
          (* both parent and children have the RUA attribute; add copy-equations *)
          p.typed_nodes |> List.filter_map (fun [
              (TNR.CHILD cnt _) as cnr when List.mem cnt ntl ->
              rua_copy_equation loc (cnr, new_attr) (parent, new_attr)
            | _ -> None
        ])

        | (False, True, None) ->
          (* children have RUA, parent does not; parent DOES NOT satisfies RUA *)
          Ploc.raise loc (Failure Fmt.(str "stitch_rua_copy_chain: malformed production %s"
                                         (PN.unparse p.name)))

        | (_, True, Some satisfying_attrna) ->
          (* children have RUA; parent satisfies RUA, add copy-equations *)
          p.typed_nodes |> List.filter_map (fun [
              (TNR.CHILD cnt _) as cnr when List.mem cnt ntl ->
              rua_copy_equation loc (cnr, new_attr) (parent, satisfying_attrna)
            | _ -> None
          ])

        | (_, False, _) ->
          (* no children have RUA; do nothing *)
          []
      ] in
      { (p) with typed_equations = copy_equations @ p.typed_equations }
    )
  ;

  value replace_teqn_rua ag rua p e =
    let open AG in
    let open P in
    let open TAEQ in
    let loc = p.P.loc in
    let parent = P.parent_nonterminal p in
    let new_attr = rua_to_attribute rua in
    match (node_attribute_exists ag (parent, new_attr), rua_to_nt_aref ag rua parent) with [
      (True, _) ->
      (* parent has new attr, replace rhs with this TAR *)
      let new_tar = TAR.NT (TNR.PARENT parent) new_attr in
      let new_rhs_expr = replace_rhs_expr_rua p rua new_tar e.TAEQ.rhs_expr in
      let new_rhs_nodes = e.rhs_nodes |> List.map (fun [
          TAR.REMOTE _ as r when r = rua -> new_tar
        | x -> x
        ]) in
      { (e) with
        rhs_expr = new_rhs_expr
      ; rhs_nodes = new_rhs_nodes
      }

    | (False, None) -> do {
      (* parent hasn't new attr, and doesn't satisfy RUA:
         there better not be any RUA references in rhs,
         since we can't replace them *)
        assert (not (List.mem rua (TAEQ.remote_upward_attributes e))) ;
        e
      }

    | (False, Some attrna) ->
      (* parent satisfies RUA, use that to rewrite rhs *)
      let new_tar = TAR.NT (TNR.PARENT parent) attrna in
      let new_rhs_expr = replace_rhs_expr_rua p rua new_tar e.rhs_expr in
      let new_rhs_nodes = e.rhs_nodes |> List.map (fun [
          TAR.REMOTE _ as r when r = rua -> new_tar
        | x -> x
        ]) in
      { (e) with
        rhs_expr = new_rhs_expr
      ; rhs_nodes = new_rhs_nodes
      }
    ]
    ;

  value replace_rhs_rua ag rua =
    let open AG in
    let open P in
    ag |> AG.map_productions (fun nt p ->
        p |> P.map_typed_equations (replace_teqn_rua ag rua p)
      )
  ;

  value rua_affected_nts ag rua =
    ag.productions |> List.filter_map (fun (nt, pl) ->
      if pl |> List.exists (fun p -> List.mem rua (P.remote_upward_attributes p)) then
        Some nt
      else None)
  ;

  value replace1_rua ag rua =
    let open AG in
    let ntl = rua_affected_nts ag rua in
    let full_ntl = rua_nonterminals ag rua ntl in
    if List.mem ag.axiom full_ntl then
      Ploc.raise ag.loc
        (Failure Fmt.(str "replace1_rua: nonterminal %s is the axiom (@[<h>full set = { %a }@]), found during processing of remote upward attribute %a"
                        ag.axiom
                        (list ~{sep=sp} string) full_ntl
                        TAR.pp_hum rua))
    else
      let ty = rua_type ag rua in
      let new_attr = rua_to_attribute rua in
      let ag = add_new_attribute ag (new_attr, ty) full_ntl in
      let ag = stitch_rua_copy_chain ag rua new_attr full_ntl in
      replace_rhs_rua ag rua
  ;

  value replace_ruas ag =
    let ruas = AG.remote_upward_attributes ag in
    List.fold_left replace1_rua ag ruas
  ;
  end
  ;

  module Constituents = struct

    (** A constituents reference (CR) is a triple

        CONSTITUENTS <nodes> ATTRIBUTES <attributes> SHIELD
       <nonterminals>

        viz

        CONSTITUENTS $1, $2 ATTRIBUTES X.a, Y,b SHIELD Z

        The latter two components together are a constituents
       attribute reference (CAR)

        To replace CRs:

        (0) So, first compute all unique constituent attribute
       references (CAR), then do the following for each CAR:

      (1) compute new attribute name in same manner as for RUA (sort
       (CAR.attrs, CAR.shield), concat with "__")

      (2) compute set of nonterminals START that mention that CAR.

      (3) initialize CARREACH = {}

      (4) DFS from nodes in START, following lhs->rhs relation in
       productions, but with a special first-step:

        (a.1) FIRST STEP: for each node X in START, for each
       production with LHS of X, collect all CRs that match CAR.
       Collect all "nodes" in these CRs, and these become the rhs we
       visit.

        (a.2) NORMAL STEP: starting from a node X, we visit all
       nonterminal children.  The visit to rhs is thus:

        (b) if rhs is in DFS stack, return

        (c) if rhs is in CAR.shield, return

        (d) if rhs is in CARREACH, return

        (e) if rhs is in CAR.attrs, add to CARREACH

        (f) else continue with DFS

      (5) after DFS thru all rhs children, if any child is in
       CARREACH, then add lhs to CARREACH

      (6) CARREACH is the set of nodes that need the new attribute.  A
       node X gets into CARREACH in two ways:

        (a) X is in CAR.attrs

        (b) In some production of X, a RHS nonterminal Y is in
       CARREACH

  *)

  value all_crs ag =
    ag
    |> AG.all_productions
    |> List.concat_map P.constituents_references
    |> List.sort_uniq Stdlib.compare
  ;

  module CAR = struct
    type t = {
      attributes : list (string * string)
    ; shield : list string
    } ;
    value of_cr = fun [
      TAR.CONSTITUENTS _ attributes shield -> { attributes=attributes ; shield=shield }
    | _ -> assert False
    ] ;

    value to_attribute car = 
      ((car.attributes |> List.concat_map (fun (a,b) -> [a;b]))@
       car.shield) |> String.concat "__"
    ;

    value type_of ag car =
    let aname =  car.attributes |> List.hd |> snd in
    (AG.attribute_type ag aname).AT.ty
    ;

  end ;

  value nts_mentioning_car ag car =
    ag.AG.productions |> List.filter_map (fun (nt, pl) ->
      if pl |> List.exists (fun p ->
          List.mem car (List.map CAR.of_cr (P.constituents_references p))) then
        Some nt else None
    )
  ;

  value car_to_nt_aref ag nt car =
    car.CAR.attributes |> List.find_map (fun [
        (n, a) when n = nt && AG.node_attribute_exists ag (n,a) -> Some a
      | _ -> None
      ])
  ;

  value nt_satisfies_car ag nt car =
    None <> car_to_nt_aref ag car nt
  ;

  value nts_needing_car_attribute ag car =
    let acc = ref [] in

    let rec dfsrec stk nt =
      if List.mem nt stk then ()
      else if List.mem nt acc.val then ()
      else if List.mem nt car.CAR.shield then ()
      else if nt_satisfies_car ag car nt then Std.push acc nt
      else
      let child_is_in = ref False in
      let pl = AG.node_productions ag nt in do {
        pl |> List.iter (fun p ->
           p.P.typed_nodes |> List.iter (fun [
             TNR.CHILD cnt _ -> do {
                 dfsrec [nt :: stk] cnt ;
                 if List.mem cnt acc.val then child_is_in.val := True else ()
               }
             | _ -> ()
           ])) ;
        if child_is_in.val && not (List.mem nt acc.val) then
          Std.push acc nt
        else ()
      } in

    let dfs1 nt =
      let visit_children =
        nt
      |> AG.node_productions ag
      |> List.concat_map P.constituents_references
      |> List.filter (fun cr -> car = CAR.of_cr cr)
      |> List.concat_map (fun [ TAR.CONSTITUENTS nodes _ _ -> nodes | _ -> assert False ])
      |> List.map (fun [ TNR.CHILD cnt _ -> cnt | _ -> assert False ])
      |> List.sort_uniq Stdlib.compare
      |> List.stable_sort Stdlib.compare in do {
        visit_children |> List.iter (fun nt -> dfsrec [] nt)
      }
    in
    let start = nts_mentioning_car ag car in do {
      List.iter dfs1 start;
      let carreach = List.stable_sort Stdlib.compare acc.val in
      (start, carreach)
    }
  ;

  (** how to rewrite CAR to normal copychain

      (0) declare the new CAR attribute

      (1) for all NT in CARREACH, add the new CAR attribute to the NT

      (2) for each NT in CARREACH:

        (a) IF it satisfies CAR (it is in CAR.attrs) then add copy
     equation from satisfying attr to new CAR attribute

        (b) otherwise children must be in CARREACH: concatenate new CR
     attribute values of all children NTs in CARREACH, assign to NT's
     CAR attribute value.

      (3) For each NT in START, for each production, for each
     equation/condition, for each CR:

        (a) rewrite CR reference to reference the CAR attribute on all
      CR.nodes, concatenating them all.

  *)

  value stitch_production_copychain ag car new_attr carreach nt p =
    let loc = ag.AG.loc in
    match car_to_nt_aref ag nt car with [
      Some sat_attr ->
      let rhs = TAR.NT (TNR.PARENT nt) sat_attr in
      let rhs_expr = <:expr< [%nterm 0;] . $lid:sat_attr$ >> in
      let lhs = TAR.NT (TNR.PARENT nt) new_attr in
      let copy_eq = {
        TAEQ.loc = loc
      ; lhs = lhs
      ; rhs_nodes = [rhs]
      ; rhs_expr = rhs_expr
      } in
      {(p) with P.typed_equations = [copy_eq :: p.P.typed_equations]}
    | None ->
      let rhs_nodes = (List.tl p.P.typed_nodes) |> List.filter_map (fun [
          (TNR.CHILD cnt _) as cnr when List.mem cnt carreach ->
          Some (TAR.NT cnr new_attr)
        | _ -> None
        ]) in
      let rhs_expr = <:expr< List.concat ($Ppxutil.convert_up_list_expr loc (List.map (TAR.to_expr loc) rhs_nodes)$) >> in
      let lhs = TAR.NT (TNR.PARENT nt) new_attr in
      let copy_eq = {
        TAEQ.loc = loc
      ; lhs = lhs
      ; rhs_nodes = rhs_nodes
      ; rhs_expr = rhs_expr
      } in
      {(p) with P.typed_equations = [copy_eq :: p.P.typed_equations]}
    ]
  ;

  value stitch_car_copychains ag car new_attr carreach =
    ag |> AG.map_productions (fun nt p ->
      if List.mem nt carreach then stitch_production_copychain ag car new_attr carreach nt p
      else p)
  ;


  value replace_cr crmap fallback cr =
    let open TAR in
    let open TNR in
    match List.assoc cr crmap with [
      (_, e) -> e
    | exception Not_found -> fallback
    ]
  ;

  value replace_rhs_expr_cr p (crmap : list (TAR.t * (list TAR.t * MLast.expr))) e =
    let dt = Camlp5_migrate.make_dt () in
    let fallback_migrate_expr = dt.migrate_expr in
    let pn = p.P.name in
    let migrate_expr dt e =
      try e |> TAR.of_expr pn |> replace_cr crmap e
      with _ -> fallback_migrate_expr dt e in
    let dt = { (dt) with Camlp5_migrate.migrate_expr = migrate_expr } in
    dt.migrate_expr dt e
  ;

  value compute_replacements_for_cr loc new_attr cr = match cr with [
    (TAR.CONSTITUENTS nodes _ _) as cr ->
    let new_tars = List.map (fun tnr -> TAR.NT tnr new_attr) nodes in
    let new_expr =
      new_tars
      |> List.map (TAR.to_expr loc)
      |> Ppxutil.convert_up_list_expr loc
      |> (fun e -> <:expr< List.concat $e$ >>)
    in
    (new_tars, new_expr)
  | _ -> assert False
  ]
  ;

  value replace_teqn_car ag car p e =
    let open AG in
    let open P in
    let open TAEQ in
    let loc = p.P.loc in
    let crs =
      e
      |> constituents_references
      |> List.filter (fun cr -> car = (CAR.of_cr cr)) in
    let new_attr = CAR.to_attribute car in
    let crmap = crs |> List.map (fun cr ->
      (cr, compute_replacements_for_cr loc new_attr cr)) in

    if [] = crmap then e else

    let new_rhs_expr = replace_rhs_expr_cr p crmap e.TAEQ.rhs_expr in
    let new_rhs_nodes = e.rhs_nodes |> List.concat_map (fun tar -> match List.assoc tar crmap with [
        (l,_) -> l
      | exception Not_found -> [tar]
      ]) in
    { (e) with
      rhs_expr = new_rhs_expr
    ; rhs_nodes = new_rhs_nodes
    }
  ;

  value replace_rhs_car ag car =
    let open AG in
    let open P in
    ag |> AG.map_productions (fun nt p ->
        p |> P.map_typed_equations (replace_teqn_car ag car p)
      )
  ;

  value rewrite1_car ag car =
    let loc = ag.AG.loc in
    let (start, carreach) = nts_needing_car_attribute ag car in
    let ty = CAR.type_of ag car in
    let new_attr = CAR.to_attribute car in
    let ag = add_new_attribute ag (new_attr, ty) carreach in
    let ag = stitch_car_copychains ag car new_attr carreach in
    replace_rhs_car ag car
  ;

  value rewrite_crs ag =
    let cars =
      ag
      |> all_crs
      |> List.map CAR.of_cr
      |> List.sort_uniq Stdlib.compare
      |> List.stable_sort Stdlib.compare in
    List.fold_left rewrite1_car ag cars
  ;
  end
  ;

end
;
