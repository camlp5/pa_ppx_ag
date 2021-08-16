(* camlp5r *)
(* pa_deriving_migrate.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Asttools;
open MLast;
open Pa_ppx_base ;
open Pa_passthru ;
open Ppxutil ;
open Surveil ;
open Pa_deriving_base ;
open Pa_ppx_utils ;
open Ag_types ;
open Ag_tsort ;

value debug = Pa_passthru.debug ;

module AGContext = struct

open Pa_ppx_params.Runtime ;

type attributed_params_t = Pa_deriving_attributed.AC.t ;
value params_attributed_params_t arg = Pa_deriving_attributed.AC.params [] arg ;

value compute_typed_attributes loc attribute_types node_attributes production_attributes =
  let attr2type homename aname =
    match List.assoc aname attribute_types with [
      x -> x
    | exception Not_found ->
      Ploc.raise loc
        (Failure Fmt.(str "compute_typed_attributes: attribute %s.%s has no declared type"
                        homename aname ))
    ] in
  (node_attributes |> List.map (fun (nt, attrs) ->
    (nt, attrs |> List.map (fun aname -> (aname, attr2type nt aname)))))@
  (production_attributes |> List.map (fun (pname, attrs) ->
       (pname, attrs |> List.map (fun aname -> (aname, attr2type pname aname)))))
;


type t = {
  optional : bool
; with_migrate : bool [@default True;]
; with_q_ast : bool [@default False;]
; plugin_name : string
; module_name : uident
; primitive_types : list lident [@default [];]
; attribution_model : attributed_params_t
; axiom : lident
; attribute_types : (alist lident ctyp) [@name attribute_types;]
; node_attributes : (alist lident (list lident))
; production_attributes : (alist lident (list lident))
(*
; typed_attributes : (alist lident (alist lident ctyp))
      [@computed compute_typed_attributes loc attribute_types node_attributes production_attributes;]
*)
; raw_attribution: (alist lident expr) [@name attribution;]
; equations: (alist PN.t (list AEQ.t)) [@computed Demarshal.extract_attribute_equations loc raw_attribution;]
; side_effects: (alist PN.t (list ASide.t)) [@computed Demarshal.extract_attribute_side_effects loc raw_attribution;]
; name2nodename : (alist lident lident) [@computed Demarshal.compute_name2nodename type_decls;]
; rev_name2nodename : (alist lident lident) [@computed List.map (fun (a,b) -> (b,a)) name2nodename;]
; type_decls : list (string * MLast.type_decl) [@computed type_decls;]
} [@@deriving params {
    formal_args = {
      t = [ type_decls ]
    }
  };]
;

value compute_typed_attributes2 loc rc =
  compute_typed_attributes loc rc.attribute_types rc.node_attributes rc.production_attributes
;

value build_type_decls tdl =
  tdl |> List.map (fun (MLast.{tdNam=tdNam} as td) ->
      (tdNam |> uv |> snd |> uv, td)
    )
;

value update_type_decls rc tdl =
  let type_decls = build_type_decls tdl in
  let name2nodename = Demarshal.compute_name2nodename type_decls in
  let rev_name2nodename = List.map (fun (a,b) -> (b,a)) name2nodename in
  { (rc) with
    type_decls = type_decls
  ; name2nodename = name2nodename
  ; rev_name2nodename = rev_name2nodename
  }
;

value build_context loc ctxt tdl =
  let type_decls = build_type_decls tdl in
  let optarg =
    let l = List.map (fun (k, e) -> (<:patt< $lid:k$ >>, e)) (Ctxt.options ctxt) in
    <:expr< { $list:l$ } >> in
  params type_decls optarg
;

end;
module AGC = AGContext ;

value str_item_gen_decorated loc rc tdl =
  let open Pa_deriving_attributed in
  let typed_attributes = AGC.compute_typed_attributes2 loc rc in
  let aa = { (rc.attribution_model) with AC.typed_attributes = typed_attributes; type_decls = rc.AGC.type_decls } in
  let (aa_st, normal_tdl, new_tdl) = str_item_generate_attributed loc aa tdl in
  let rc = AGC.update_type_decls rc new_tdl in
  (rc, aa_st,
   <:str_item< open $uid:aa.AC.attributed_module_name$ >>,
   normal_tdl, new_tdl)
;

value apply_to_last f l =
  match l with [ [] -> [] | _ ->
    let (last, l) = sep_last l in
    l @ [f last]
  ]
;

value find_td loc tdl tn =
  match tdl |> List.find_map (fun td ->
    if (td.tdNam |> uv |> snd |> uv) = tn then Some td else None
  ) with [
    None -> Ploc.raise loc (Failure (Printf.sprintf "find_td: could not find %s" tn))
  | Some td -> td
  ]
;

value generate_normal_custom_branches loc arg rc (normal_module_name, new_module_name) tn node_td =
  match node_td with [
    <:type_decl:< $lid:_$ $list:_$ = [ $list:branches$ ] >>
  | <:type_decl:< $lid:_$ $list:_$ = $_$ == [ $list:branches$ ] >> ->
      branches |> List.filter_map (fun [
        <:constructor< $uid:ci$ of $list:tyl$ $algattrs:_$ >>
        when List.mem_assoc (tn^"__"^ci) rc.AGC.production_attributes ->
        let argpatts = List.mapi (fun i _ -> <:patt< $lid:(Printf.sprintf "v_%d" i)$ >>) tyl in
        let casepatt = Patt.applist <:patt< $uid:ci$ >> argpatts in
        let rhsexpr =
          let constrname = Printf.sprintf "make_%s__%s_0" tn ci in
          let argexprs = tyl |> List.mapi (fun i -> fun [
              <:ctyp< $lid:argtyna$ >> ->
              let v = Printf.sprintf "v_%d" i in
              let migfname = Printf.sprintf "migrate_%s" argtyna in
              <:expr< __dt__. $lid:migfname$ __dt__  $lid:v$ >>
            | _ -> Ploc.raise loc
                (Failure (Printf.sprintf "generate_custom_branches: bad arg type for type=%s constructor=%s" tn ci))
            ]) in
          Expr.applist <:expr< $uid:new_module_name$ . $lid:constrname$ >> argexprs in
        Some (casepatt, <:vala< None >>, rhsexpr)
      | _ -> None
      ])
  | _ -> []
  ]
;

value generate_normal_migrator loc arg rc normal_tdl (normal_module_name, new_module_name) td =
  let tn = match td with [
        <:type_decl:< $lid:tn$ $list:_$ = $_$ >> -> tn
      | _ -> Ploc.raise loc (Failure "generate_normal_migrator")
      ] in
  if List.mem_assoc tn rc.AGC.node_attributes then
    let nodename = tn^"_node" in
    let node_td = find_td loc normal_tdl nodename in
    let constrname = "make_"^tn in
    let migname = "migrate_"^tn in
    let mignodename = "migrate_"^tn^"_node" in
    let node_migrator = match generate_normal_custom_branches loc arg rc (normal_module_name, new_module_name) tn node_td with [
      [] ->
      (<:patt< $lid:mignodename$ >>,
       <:expr< {
               srctype = [%typ: $lid:nodename$ ]
               ; dsttype = [%typ: $uid:new_module_name$ . $lid:nodename$ ]
               } >>)
    | branches ->
      (<:patt< $lid:mignodename$ >>,
       <:expr< {
               srctype = [%typ: $lid:nodename$ ]
               ; dsttype = [%typ: $uid:new_module_name$ . $lid:nodename$ ]
               ; custom_branches_code = fun [ $list:branches$ ]
               } >>)
    ]
    in
    let it_migrator = (<:patt< $lid:migname$ >>,
     <:expr< {
          srctype = [%typ: $lid:tn$ ]
        ; dsttype = [%typ: $uid:new_module_name$ . $lid:tn$ ]
        ; code = (fun __dt__ x ->
            $uid:new_module_name$ . $lid:constrname$ (__dt__. $lid:mignodename$ __dt__ x)
          )
        } >>) in
    [node_migrator; it_migrator]
  else
    []
;

value generate_new_custom_branches loc arg rc (normal_module_name, new_module_name) tn node_td =
  match node_td with [
    <:type_decl:< $lid:_$ $list:_$ = [ $list:branches$ ] >>
  | <:type_decl:< $lid:_$ $list:_$ = $_$ == [ $list:branches$ ] >> ->
      branches |> List.filter_map (fun [
        <:constructor< $uid:ci$ of $list:tyl$ $algattrs:_$ >>
        when List.mem_assoc (tn^"__"^ci) rc.AGC.production_attributes ->
        let butlast_tyl = snd (sep_last tyl) in
        let argpatts = List.mapi (fun i _ -> <:patt< $lid:(Printf.sprintf "v_%d" i)$ >>) butlast_tyl in
        let argpatts = argpatts @ [<:patt< _ >>] in
        let casepatt = Patt.applist <:patt< $uid:ci$ >> argpatts in
        let rhsexpr =
          let argexprs = butlast_tyl |> List.mapi (fun i -> fun [
              <:ctyp< $lid:argtyna$ >> ->
              let v = Printf.sprintf "v_%d" i in
              let migfname = Printf.sprintf "migrate_%s" argtyna in
              <:expr< __dt__. $lid:migfname$ __dt__  $lid:v$ >>
            | _ -> Ploc.raise loc
                (Failure (Printf.sprintf "generate_custom_branches: bad arg type for type=%s constructor=%s" tn ci))
            ]) in
          Expr.applist <:expr< $uid:normal_module_name$ . $uid:ci$ >> argexprs in
        Some (casepatt, <:vala< None >>, rhsexpr)
      | _ -> None
      ])
  | _ -> []
  ]
;

value generate_new_migrator loc arg rc new_tdl (normal_module_name, new_module_name) td =
  let tn = match td with [
        <:type_decl:< $lid:tn$ $list:_$ = $_$ >> -> tn
      | _ -> Ploc.raise loc (Failure "generate_new_migrator")
      ] in
  if List.mem_assoc tn rc.AGC.node_attributes then
    let nodename = tn^"_node" in
    let node_td = find_td loc new_tdl nodename in
    let constrname = "make_"^tn in
    let migname = "migrate_"^tn in
    let mignodename = "migrate_"^tn^"_node" in
    let node_migrator = match generate_new_custom_branches loc arg rc (normal_module_name, new_module_name) tn node_td with [
      [] ->
      (<:patt< $lid:mignodename$ >>,
       <:expr< {
               srctype = [%typ: $lid:nodename$ ]
               ; dsttype = [%typ: $uid:normal_module_name$ . $lid:tn$ ]
               } >>)
    | branches ->
      (<:patt< $lid:mignodename$ >>,
       <:expr< {
               srctype = [%typ: $lid:nodename$ ]
               ; dsttype = [%typ: $uid:normal_module_name$ . $lid:tn$ ]
               ; custom_branches_code = fun [ $list:branches$ ]
               } >>)
    ]
    in
    let it_migrator = (<:patt< $lid:migname$ >>,
     <:expr< {
          srctype = [%typ: $lid:tn$ ]
        ; dsttype = [%typ: $uid:normal_module_name$ . $lid:tn$ ]
        ; code = (fun __dt__ x ->
            __dt__. $lid:mignodename$ __dt__ x.Pa_ppx_ag_runtime.Attributes.node
          )
        } >>) in
    [node_migrator; it_migrator]
  else
    []
;



value str_item_generate_migration loc arg rc normal_tdl new_tdl =
  let open Pa_deriving_unique in
  let open Pa_deriving_attributed in
  if not rc.AGC.with_migrate then <:str_item< declare end >>
  else
  let (normal_module_name, new_module_name) = 
    (rc.AGC.attribution_model.AC.normal_module_name, rc.AGC.attribution_model.AC.attributed_module_name) in
  let normal_module_name = mustSome "str_item_generate_migration" normal_module_name in
  let normal_tdl = normal_tdl |> List.map (fun [
        <:type_decl:< $lid:tn$ $list:pl$ = $_$ == $ty$ >> ->
        <:type_decl< $lid:tn$ $list:pl$ = $uid:normal_module_name$ . $lid:tn$ == $ty$ >>
      | <:type_decl:< $lid:tn$ $list:pl$ = $ty$ >> when is_generative_type ty ->
        <:type_decl< $lid:tn$ $list:pl$ = $uid:normal_module_name$ . $lid:tn$ == $ty$ >>
      | t -> t
      ]) in
  let normal_mig_l = normal_tdl |> List.concat_map (generate_normal_migrator loc arg rc normal_tdl (normal_module_name, new_module_name)) in
  let normal_mig_l = normal_mig_l @ [
        (<:patt< migrate_loc >>,
         <:expr< {
          srctype = [%typ: loc]
        ; dsttype = [%typ: loc]
        ; code = fun __dt__ x -> x
        } >>)
      ; (<:patt< migrate_string >>,
         <:expr< {
          srctype = [%typ: string]
        ; dsttype = [%typ: string]
        ; code = fun __dt__ x -> x
        } >>)
    ] in
  let normal_migrate_attribute =
    let b = <:attribute_body< deriving migrate
              { dispatch_type = dispatch_table_t
              ; dispatch_table_constructor = make_dt
              ; dispatchers = { $list:normal_mig_l$ }
              } ; >> in
    <:vala< b >> in
  let final_normal_tdl = normal_tdl |> apply_to_last (fun td -> { (td) with tdAttributes = <:vala< [normal_migrate_attribute] >> }) in
  let normal_st = <:str_item< type $list:final_normal_tdl$ >> in
  let normal_st =
    let arg = { (arg) with Ctxt.options = [] } in
    Pa_ppx_base.Pa_passthru.str_item arg normal_st in
  let new_tdl = new_tdl |> List.map (fun [
        <:type_decl:< $lid:tn$ $list:pl$ = $_$ == $ty$ >> ->
        <:type_decl< $lid:tn$ $list:pl$ = $uid:new_module_name$ . $lid:tn$ == $ty$ >>
      | <:type_decl:< $lid:tn$ $list:pl$ = $ty$ >> when is_generative_type ty ->
        <:type_decl< $lid:tn$ $list:pl$ = $uid:new_module_name$ . $lid:tn$ == $ty$ >>
      | t -> t
      ]) in

  let new_mig_l = new_tdl |> List.concat_map (generate_new_migrator loc arg rc new_tdl (normal_module_name, new_module_name)) in
  let new_mig_l = new_mig_l @ [
        (<:patt< migrate_loc >>,
         <:expr< {
          srctype = [%typ: loc]
        ; dsttype = [%typ: loc]
        ; code = fun __dt__ x -> x
        } >>)
      ; (<:patt< migrate_string >>,
         <:expr< {
          srctype = [%typ: string]
        ; dsttype = [%typ: string]
        ; code = fun __dt__ x -> x
        } >>)
    ] in

  let new_migrate_attribute =
    let b = <:attribute_body< deriving migrate
              { dispatch_type = dispatch_table_t
              ; dispatch_table_constructor = make_dt
              ; dispatchers = { $list:new_mig_l$ }
              } ; >> in
    <:vala< b >> in
  let new_tdl = apply_to_last (fun td -> { (td) with tdAttributes = <:vala< [new_migrate_attribute] >> }) new_tdl in

  let final_new_tdl = new_tdl |> apply_to_last (fun td -> { (td) with tdAttributes = <:vala< [new_migrate_attribute] >> }) in
  let new_st = <:str_item< type $list:final_new_tdl$ >> in
  let new_st =
    let arg = { (arg) with Ctxt.options = [] } in
    Pa_ppx_base.Pa_passthru.str_item arg new_st in

  <:str_item< module Migrate = struct
                open Pa_ppx_ag_runtime.Attributes ;
                type loc = Ploc.t ;
                module ToAttributed = struct
                  $stri:normal_st$ ;
                end ;
                module FromAttributed = struct
                  $stri:new_st$ ;
                end ;
              end >>
;

value str_item_gen_ag name arg = fun [
  <:str_item:< type $_flag:_$ $list:tdl$ >> as st ->
    let rc0 = AGC.build_context loc arg tdl in
    let (rc, uu_st, uu_open_st, normal_tdl, new_tdl) = str_item_gen_decorated loc rc0 tdl in
    let ag0 = AG.mk0 loc
        rc.AGC.primitive_types
        rc.AGC.axiom
        (List.map fst rc.AGC.name2nodename)
        (rc.AGC.attribute_types, rc.AGC.node_attributes, rc.AGC.production_attributes)
        rc.AGC.equations
        rc.AGC.side_effects in
    let ag = Demarshal.productions ag0 rc.AGC.type_decls in do {
    let ag = AGOps.SideEffect.rewrite_side_effects ag in
    let ag = AGOps.Chain.(augment_chains_with_copychains ag) in
    let ag = AGOps.Chain.(replace_chains_with_pre_post ag) in
    let ag = AGOps.RUA.replace_ruas ag in
    let ag = AGOps.Constituents.rewrite_crs ag in
    let (rc, uu_st, uu_open_st, normal_tdl, new_tdl) =
      let rc0 = AGC.{
          (rc0) with
          attribute_types = ag.attribute_types |> List.map (fun (attrna, aty) -> (attrna, aty.AT.ty))
        ; node_attributes = ag.node_attributes
        ; production_attributes = ag.production_attributes
        } in
      str_item_gen_decorated loc rc0 tdl in
    let memo = AGOps.NTOps.mk_memo ag in
      assert (AGOps.well_formed memo) ;
      assert (AGOps.complete memo) ;
      assert (AGOps.locally_acyclic memo) ;
    let migrate_st = str_item_generate_migration loc arg rc normal_tdl new_tdl in
    let q_ast_st = if rc.AGC.with_q_ast then
      <:str_item< module QAst = struct end >>
    else
      <:str_item< declare end >> in
    let (visitors,evaluate) = Ag_ordered.compute_evaluate memo in
      <:str_item< 
                declare
                  $stri:uu_st$ ;
                  module $uid:rc.AGC.module_name$ = struct
                  open Pa_ppx_utils ;
                  $stri:uu_open_st$ ;
                  $stri:migrate_st$ ;
                  $stri:q_ast_st$ ;
                  open $wrapper_module_module_expr$ ;
                  declare $list:[node_module_declaration memo
                                ;attr_type_declaration memo
                                ;nodeattr_type_declaration memo
                                ;node_attribute_table_declaration memo
                                ;lookup_parent_declaration memo]$ end ;
                  value $list:[synthesized_attribute_function memo
                              ;inherited_attribute_function memo
                              ]$ ;
                  value $list:[attribute_function memo]$ ;
                  module Topological = struct
                    module G = Graph.Persistent.Digraph.ConcreteBidirectional(NodeAttrVertex) ;
                    value edges_to_graph l =
                      List.fold_left (fun g (s,d) -> G.add_edge g s d) G.empty l ;
                    module TSort = Graph.Topological.Make_stable(G) ;
                    module Dfs = Graph.Traverse.Dfs(G) ;
                    value rec $list:actual_dep_function_declarations memo$ ;
                    value rec $list:eval_functions memo$ ;
                  end ;
                  module Ordered = struct
                    value rec $list:visitors$ ;
                    value $list:[evaluate]$ ;
                  end ;
                  end ;
                end
      >>
    }
| _ -> assert False ]
;

Pa_deriving.(Registry.add PI.{
  name = "ag"
; alternates = []
; options = ["optional"
            ; "axiom"
            ; "attribution_model"
            ; "with_migrate"
            ; "with_q_ast"
            ; "primitive_types"
            ; "attribute_types"
            ; "node_attributes"
            ; "production_attributes"
            ; "attribution"
            ; "module_name"]
; default_options = let loc = Ploc.dummy in [
    ("optional", <:expr< False >>)
  ]
; alg_attributes = []
; expr_extensions = []
; ctyp_extensions = []
; expr = (fun arg e -> assert False)
; ctyp = (fun arg e -> assert False)
; str_item = str_item_gen_ag
; sig_item = (fun arg e -> assert False)
})
;

