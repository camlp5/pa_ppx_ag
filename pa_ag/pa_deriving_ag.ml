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

value demarshal_raw_storage_mode loc = fun [
    "Hashtables" -> Hashtables
  | "Records" -> Records
  | s -> Ploc.raise loc (Failure Fmt.(str "demarshal_raw_storage_mode: unrecognized mode %s (must be either Hashtables or Records)" s))
]
;

type t = {
  optional : bool
; plugin_name : string
; module_name : uident
; raw_storage_mode: uident [@name storage_mode;]
; storage_mode : storage_mode_t [@computed demarshal_raw_storage_mode loc raw_storage_mode;]
; axiom : lident
; typed_attributes : (alist lident (alist lident ctyp)) [@name attributes;]
; raw_attribution: (alist lident expr) [@name attribution;]
; equations: (alist AG.PN.t (list AG.AEQ.t)) [@computed Demarshal.extract_attribute_equations loc raw_attribution;]
; conditions: (alist AG.PN.t (list AG.Cond.t)) [@computed Demarshal.extract_attribute_conditions loc raw_attribution;]
; name2nodename : (alist lident lident) [@computed Demarshal.compute_name2nodename type_decls;]
; rev_name2nodename : (alist lident lident) [@computed List.map (fun (a,b) -> (b,a)) name2nodename;]
; type_decls : list (string * MLast.type_decl) [@computed type_decls;]
} [@@deriving params {
    formal_args = {
      t = [ type_decls ]
    }
  };]
;

value build_context loc ctxt tdl =
  let type_decls = List.map (fun (MLast.{tdNam=tdNam} as td) ->
      (tdNam |> uv |> snd |> uv, td)
    ) tdl in
  let optarg =
    let l = List.map (fun (k, e) -> (<:patt< $lid:k$ >>, e)) (Ctxt.options ctxt) in
    <:expr< { $list:l$ } >> in
  params type_decls optarg
;

end;
module AGC = AGContext ;

value str_item_gen_ag name arg = fun [
  <:str_item:< type $_flag:_$ $list:tdl$ >> ->
    let rc = AGC.build_context loc arg tdl in
    let (wrapper_module_longid, wrapper_module_module_expr) = storage_mode_wrapper_modules rc.AGC.storage_mode in
    let ag0 = AG.mk0 loc
        rc.AGC.axiom
        (List.map fst rc.AGC.name2nodename)
        rc.AGC.typed_attributes
        rc.AGC.equations
        rc.AGC.conditions in
    let ag = Demarshal.productions ag0 rc.AGC.type_decls in do {
    let memo = AGOps.NTOps.mk_memo ag in
      assert (AGOps.well_formed memo) ;
      assert (AGOps.complete memo) ;
      assert (AGOps.locally_acyclic memo) ;
      <:str_item< module $uid:rc.AGC.module_name$ = struct
                  open Pa_ppx_utils ;
                  open $wrapper_module_module_expr$ ;
                  declare $list:[node_module_declaration memo
                                ;attr_type_declaration memo
                                ;nodeattr_type_declaration memo
                                ;node_attribute_table_declaration rc.AGC.storage_mode memo
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
                  end >>
    }
| _ -> assert False ]
;

Pa_deriving.(Registry.add PI.{
  name = "ag"
; alternates = []
; options = ["optional"
            ; "axiom"
            ; "storage_mode"
            ; "attributes"
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

