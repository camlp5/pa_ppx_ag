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

type storage_mode_t = Ag_types.storage_mode_t == [ Hashtables | Records ] [@@deriving params;] ;

type unique_params_t = Pa_deriving_unique.UC.t ;
value params_unique_params_t arg = Pa_deriving_unique.UC.params [] arg ;
type attributed_params_t = Pa_deriving_attributed.AC.t ;
value params_attributed_params_t arg = Pa_deriving_attributed.AC.params [] arg ;

type attribution_model_t = [
    Unique of unique_params_t
  | Attributed of attributed_params_t
] [@@deriving params;]
;

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
; plugin_name : string
; module_name : uident
; storage_mode : storage_mode_t
; attribution_model : option attribution_model_t
; axiom : lident
; attribute_types : (alist lident ctyp) [@name attribute_types;]
; node_attributes : (alist lident (list lident))
; production_attributes : (alist lident (list lident))
(*
; typed_attributes : (alist lident (alist lident ctyp))
      [@computed compute_typed_attributes loc attribute_types node_attributes production_attributes;]
*)
; raw_attribution: (alist lident expr) [@name attribution;]
; equations: (alist AG.PN.t (list AG.AEQ.t)) [@computed Demarshal.extract_attribute_equations loc raw_attribution;]
; conditions: (alist AG.PN.t (list AG.AEQ.t)) [@computed Demarshal.extract_attribute_conditions loc raw_attribution;]
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
  let open Pa_deriving_unique in
  let open Pa_deriving_attributed in
  match rc.AGC.attribution_model with [
    Some (AGC.Unique uu) ->
    let uu = { (uu) with UC.type_decls = rc.AGC.type_decls } in
    let (uu_st, normal_tdl, new_tdl) = str_item_generate_unique loc uu tdl in
    let rc = AGC.update_type_decls rc new_tdl in
    (rc, uu_st,
     <:str_item< open $uid:uu.UC.uniqified_module_name$ >>)
  | Some (AGC.Attributed aa) ->
    let typed_attributes = AGC.compute_typed_attributes2 loc rc in
    let aa = { (aa) with AC.typed_attributes = typed_attributes; type_decls = rc.AGC.type_decls } in
    let (aa_st, normal_tdl, new_tdl) = str_item_generate_attributed loc aa tdl in
    let rc = AGC.update_type_decls rc new_tdl in
    (rc, aa_st,
     <:str_item< open $uid:aa.AC.attributed_module_name$ >>)
  | None ->
    (rc, <:str_item< declare end >>,
     <:str_item< declare end >>)
  ]
;
value str_item_gen_ag name arg = fun [
  <:str_item:< type $_flag:_$ $list:tdl$ >> as st ->
    let rc = AGC.build_context loc arg tdl in
    let (rc, uu_st, uu_open_st) = str_item_gen_decorated loc rc tdl in
    let (wrapper_module_longid, wrapper_module_module_expr) = storage_mode_wrapper_modules rc.AGC.storage_mode in
    let ag0 = AG.mk0 loc
        rc.AGC.storage_mode
        rc.AGC.axiom
        (List.map fst rc.AGC.name2nodename)
        (rc.AGC.attribute_types, rc.AGC.node_attributes, rc.AGC.production_attributes)
        rc.AGC.equations
        rc.AGC.conditions in
    let ag = Demarshal.productions ag0 rc.AGC.type_decls in do {
    let ag = AGOps.(augment_chain_with_copychains ag) in
    let memo = AGOps.NTOps.mk_memo ag in
      assert (AGOps.well_formed memo) ;
      assert (AGOps.complete memo) ;
      assert (AGOps.locally_acyclic memo) ;
    let memo = AGOps.NTOps.mk_memo ag in
      <:str_item< 
                declare
                  $stri:uu_st$ ;
                  module $uid:rc.AGC.module_name$ = struct
                  open Pa_ppx_utils ;
                  $stri:uu_open_st$ ;
                  open $wrapper_module_module_expr$ ;
                  declare $list:[node_module_declaration memo
                                ;attr_type_declaration memo
                                ;nodeattr_type_declaration memo
                                ;node_attribute_table_declaration memo
                                ;lookup_parent_declaration memo]$ end ;
                  module G = Graph.Persistent.Digraph.ConcreteBidirectional(NodeAttr) ;
                  value edges_to_graph l =
                    List.fold_left (fun g (s,d) -> G.add_edge g s d) G.empty l ;
                  module TSort = Graph.Topological.Make_stable(G) ;
                  value rec $list:actual_dep_function_declarations memo$ ;
                  value $list:[synthesized_attribute_function memo
                              ;inherited_attribute_function memo
                              ]$ ;
                  value $list:[attribute_function memo]$ ;
                  value $list:[eval_function memo]$ ;
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
            ; "storage_mode"
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

