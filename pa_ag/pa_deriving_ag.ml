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

value debug = Pa_passthru.debug ;

module AGContext = struct

open Pa_ppx_params.Runtime ;

type t = {
  optional : bool
; plugin_name : string
; module_name : uident
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
      <:str_item< module $uid:rc.AGC.module_name$ = struct
                    value x = 1 ;
                  end >>
    }
| _ -> assert False ]
;

Pa_deriving.(Registry.add PI.{
  name = "ag"
; alternates = []
; options = ["optional"
            ; "axiom"
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

