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

module AG = struct
  type node_reference_t = [
      PARENT of option string
    | CHILD of option string and int
    | PRIM of int
    ] ;
  module AEQ = struct
    type t = {
      lhs : (node_reference_t * string)
    ; rhs_nodes : list (node_reference_t * string)
    ; rhs_expr : MLast.expr
    }
    ;
  end ;
end ;

module AGContext = struct

open Pa_ppx_params.Runtime ;

value expr_to_attribute_reference e =
  let open AG in
  let open AEQ in
  match e with [
    <:expr< [%attr $lid:tyname$;] . $lid:attrna$ >> -> 
    (PARENT (Some tyname), attrna)
  | <:expr< [%attr 0;] . $lid:attrna$ >> ->
    (PARENT None, attrna)
  | <:expr< [%attr $int:n$;] . $lid:attrna$ >> ->
    (CHILD None (int_of_string n), attrna)
  | <:expr< [%attr $lid:tyname$ . ( $int:n$ );] . $lid:attrna$ >> ->
    (CHILD (Some tyname) (int_of_string n), attrna)
  | <:expr< [%prim $int:n$;] . $lid:attrna$ >> ->
    (PRIM (int_of_string n), attrna)
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

value assignment_to_equation e = match e with [
    <:expr< $lhs$ . val := $rhs$ >> ->
    { AG.AEQ.lhs = expr_to_attribute_reference lhs
    ; rhs_nodes = extract_attribute_references rhs
    ; rhs_expr = rhs }
  | <:expr< $lhs$ := $rhs$ >> ->
    { AG.AEQ.lhs = expr_to_attribute_reference lhs
    ; rhs_nodes = extract_attribute_references rhs
    ; rhs_expr = rhs }
  | _ -> Ploc.raise (MLast.loc_of_expr e) (Failure Fmt.(str "assignment_to_equation: not an assignment@ %a"
                                                          Pp_MLast.pp_expr e))
]
;

value extract_attribute_equations l : (alist lident (list AG.AEQ.t)) =
  l |> List.map (fun (prodname, e) ->
                  match e with [
                    <:expr< do { $list:l$ } >> ->
                    (prodname, List.map assignment_to_equation l)
                  | <:expr< $_$ . val := $_$ >> ->
                    (prodname, [assignment_to_equation e])
                  ])
;

type t = {
  optional : bool
; plugin_name : string
; module_name : uident
; attributes : (alist lident (alist lident ctyp))
; raw_attribution: (alist lident expr) [@name attribution;]
; attribution: (alist lident (list AG.AEQ.t)) [@computed extract_attribute_equations raw_attribution;]
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
    let rc = AGContext.build_context loc arg tdl in
      <:str_item< module $uid:rc.AGContext.module_name$ = struct
                    value x = 1 ;
                  end>>
| _ -> assert False ]
;

Pa_deriving.(Registry.add PI.{
  name = "ag"
; alternates = []
; options = ["optional"
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

