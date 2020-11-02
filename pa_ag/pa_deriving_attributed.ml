(* camlp5r *)
(* pa_deriving_attributed.ml,v *)

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

module AC = struct

type t = {
  optional : bool
; plugin_name : string
; normal_module_name : uident
; attributed_module_name : uident
; typed_attributes : (alist lident (alist lident ctyp)) [@name attributes;]
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

value strip_deriving_attributes td =
  { (td) with
    tdAttributes =
      vala_map (Std.filter (fun a ->
          not (List.mem (a |> uv |> fst |> uv |> snd)
            ["deriving"])))
        td.tdAttributes }
;

value constructor_name rc name = "make_"^name ;

value make_rho loc name td =
  let tyvars = td.tdPrm |> uv in
  List.mapi (fun i -> fun [
      (<:vala< None >>, _) ->
      Ploc.raise loc (Failure Fmt.(str "make_rho: %s: formal type-vars must all be named"
                                     name))
    | (<:vala< Some id >>, _) -> (id, Printf.sprintf "sub_%d" i)
    ]) tyvars
;

value abstract_function_body loc typemaker rho fbody =
  let args = List.map (fun (id, fname) ->
    let argty = typemaker <:ctyp< $lid:id$ >> in
    <:patt< ( $lid:fname$ : $argty$)>>) rho in
  let typeargs = List.map (fun (id, _) ->
      <:patt< (type $lid:id$) >>) rho in
  Expr.abstract_over (typeargs@args) fbody
;

value create_function_type loc typemaker rho name =
  if rho = [] then
    typemaker <:ctyp< $lid:name$ >>
  else
    let typevars = List.map (fun (id, _) -> <:ctyp< ' $id$ >>) rho in
    let thety = Ctyp.applist <:ctyp< $lid:name$ >> typevars in
    let argtypes = List.map typemaker typevars in
    let rhsty = Ctyp.arrows_list loc argtypes (typemaker thety) in
    <:ctyp< ! $list:List.map fst rho$ . $rhsty$ >>
;

value ctyp_make_tuple loc l =
  match l with [
    [] -> Ploc.raise loc (Failure "ctyp_make_tuple: invalid empty-list arg")
  | [t] -> t
  | l -> <:ctyp< ( $list:l$ ) >>
  ]
;

value expr_make_tuple loc l =
  match l with [
    [] -> Ploc.raise loc (Failure "expr_make_tuple: invalid empty-list arg")
  | [t] -> t
  | l -> <:expr< ( $list:l$ ) >>
  ]
;

value patt_make_tuple loc l =
  match l with [
    [] -> Ploc.raise loc (Failure "patt_make_tuple: invalid empty-list arg")
  | [t] -> t
  | l -> <:patt< ( $list:l$ ) >>
  ]
;

value to_expr loc (v, (_, _)) = <:expr< $lid:v$ >> ;
value to_patt loc (v, (_, _)) = <:patt< $lid:v$ >> ;
value to_typatt loc (v, (_, ty)) = <:patt< ( $lid:v$ : $ty$ ) >> ;

value flatten_str_items sil =
  let rec flatrec = fun [
    <:str_item< declare $list:l$ end >> ->
    List.concat (List.map flatrec l)
  | si -> [si]
  ]
  in List.concat (List.map flatrec sil)
;

value separate_bindings l =
  let (ml, vl)  = List.fold_left (fun (mb,vb) -> fun [
      <:str_item< module $uid:_$ = $_$ >> as z -> ([ z :: mb ], vb)
    | <:str_item< value $list:l$ >> -> (mb, l @ vb)
    ]) ([], []) l in
  (List.rev ml, List.rev vl)
;

value generate_attributed_constructor ctxt rc (name, td) =
  let loc = loc_of_type_decl td in
  if uv td.tdPrm <> [] || not (List.mem_assoc name rc.typed_attributes) then <:str_item< declare end >> else
  let attributes = match List.assoc name rc.typed_attributes with [
    x -> x
    | exception Not_found -> assert False
    ] in
  let attribute_initializer =
    let lel = attributes |> List.map (fun (aname, _) ->
        (<:patt< $lid:name^"__"^aname$ >>, <:expr< None >>)) in
    <:expr< { $list:lel$ } >> in
  let consname = constructor_name rc name in
  <:str_item< value $lid:consname$ x =
              Pa_ppx_ag_runtime.Attributes.attributed ~{attributes = $attribute_initializer$} x >>
;

end
;


value make_twolevel_type_decl ctxt rc ~{preserve_manifest} ~{skip_attributed} td =
  let loc = loc_of_type_decl td in
  let name = td.tdNam |> uv |> snd |> uv in
  let (skip_attributed, attributes) =
    if skip_attributed then (True, []) else
    match List.assoc name rc.AC.typed_attributes with [
      x -> (False, x)

    | exception Not_found -> (True, [])
    ] in
  let data_name = name^"_node" in
  let tyargs =
    let tyvars = td.tdPrm |> uv in
    List.map (fun [
        (<:vala< None >>, _) ->
        Ploc.raise loc (Failure Fmt.(str "make_two_level_type_decl: %s: formal type-vars must all be named"
                                       name))
      | (<:vala< Some id >>, _) -> <:ctyp< ' $id$ >>
      ]) tyvars in
  let wrapped_type_decls =
    let data_type = <:ctyp< $lid:data_name$ >> in
    if skip_attributed then
      [<:type_decl< $lid:name$ $_list:td.tdPrm$ = $Ctyp.applist data_type tyargs$ >>]
    else
      let ltl = attributes |> List.map (fun (aname, ty) ->
          (loc, name^"__"^aname, True, <:ctyp< option $ty$ >>, <:vala< [] >>)) in
      let attr_type = <:ctyp< { $list:ltl$ } >> in
      let attr_type_name = name^"_attributes" in
      let tdDef =
        <:ctyp< attributed $Ctyp.applist data_type tyargs$ $lid:attr_type_name$ >> in
      [<:type_decl< $lid:name$ $_list:td.tdPrm$ = $tdDef$ >>
      ;<:type_decl< $lid:attr_type_name$ = $attr_type$ >>
      ] in

  [ { (td) with
      tdNam =
        let n = <:vala< data_name >> in
        <:vala< (loc, n) >>
      ; tdDef = match td.tdDef with [
          <:ctyp< $_$ == $t$ >> when not preserve_manifest -> t
        | t -> t
        ]
    } ]@
  wrapped_type_decls
;

value normal_type_decl ctxt rc td =
  let skip_attributed = True in
  let preserve_manifest = True in
  make_twolevel_type_decl ctxt rc ~{preserve_manifest=preserve_manifest} ~{skip_attributed=skip_attributed} td
;

value attributed_type_decl ctxt rc td =
  let preserve_manifest = False in
  make_twolevel_type_decl ctxt rc ~{preserve_manifest=preserve_manifest} ~{skip_attributed=False} td
;

value str_item_gen_attributed name arg = fun [
  <:str_item:< type $_flag:_$ $list:tdl$ >> ->
    let rc = AC.build_context loc arg tdl in
    let new_tdl =
      tdl
      |> List.map (attributed_type_decl arg rc)
      |> List.concat
      |> List.map AC.strip_deriving_attributes in
    let normal_tdl =
      tdl
      |> List.map (normal_type_decl arg rc)
      |> List.concat
      |> List.map AC.strip_deriving_attributes in
    let attributed_constructors = List.map (AC.generate_attributed_constructor arg rc) rc.AC.type_decls in
      <:str_item< declare
                  module $uid:rc.normal_module_name$ = struct
                  type $list:normal_tdl$ ;
                  end ;
                  module $uid:rc.attributed_module_name$ = struct
                  open Pa_ppx_ag_runtime.Attributes ;
                  type $list:new_tdl$ ;
                  declare $list:attributed_constructors$ end ;
                  end ;
                end>>
| _ -> assert False ]
;

Pa_deriving.(Registry.add PI.{
  name = "attributed"
; alternates = []
; options = ["optional";"plugin_name";"normal_module_name";"attributed_module_name";"attributes"]
; default_options = let loc = Ploc.dummy in [
    ("optional", <:expr< False >>)
  ]
; alg_attributes = []
; expr_extensions = []
; ctyp_extensions = []
; expr = (fun arg e -> assert False)
; ctyp = (fun arg e -> assert False)
; str_item = str_item_gen_attributed
; sig_item = (fun arg e -> assert False)
})
;

