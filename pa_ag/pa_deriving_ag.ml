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

value debug = Pa_passthru.debug ;

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

open Pa_ppx_params.Runtime ;

module AGC = struct

type pertype_customization_t = {
  unique_constructor : option lident
} [@@deriving params;]
;

type t = {
  optional : bool
; module_name : uident
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

value str_item_gen_ag name arg = fun [
  <:str_item:< type $_flag:_$ $list:tdl$ >> ->
    let rc = AGC.build_context loc arg tdl in
      <:str_item< module $uid:rc.AGC.module_name$ = struct
                    value x = 1 ;
                  end>>
| _ -> assert False ]
;

Pa_deriving.(Registry.add PI.{
  name = "ag"
; alternates = []
; options = ["optional"
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

