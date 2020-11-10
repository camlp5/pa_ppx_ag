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
  optional : bool [@default False;]
; plugin_name : string [@default "attributed";]
; normal_module_name : option uident
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

value make_attribute_initializer loc name attributes =
  let lel = attributes |> List.map (fun (aname, _) ->
    (<:patt< $lid:name^"__"^aname$ >>, <:expr< None >>)) in
  <:expr< { $list:lel$ } >>
;

value to_expr loc v = <:expr< $lid:v$ >> ;

value generate_attributed_constructor rc (name, td) =
  let loc = loc_of_type_decl td in
  if uv td.tdPrm <> [] || not (List.mem_assoc name rc.typed_attributes) then <:str_item< declare end >> else
  let attributes = List.assoc name rc.typed_attributes in
  let attribute_initializer = make_attribute_initializer loc name attributes in
  let consname = constructor_name rc name in
  let top_cons =
    <:str_item< value $lid:consname$ x =
                Pa_ppx_ag_runtime.Attributes.attributed ~{attributes = $attribute_initializer$} x >> in
  let prod_cons_list = match td.tdDef with [
    <:ctyp:< $_$ == [ $list:branches$ ] >> | <:ctyp:< [ $list:branches$ ] >> ->
      branches |> List.map (fun [
        <:constructor:< $uid:ci$ of $list:tl$ $algattrs:_$ >> ->
          if List.mem_assoc (name^"__"^ci) rc.typed_attributes then
            let attributes = List.assoc (name^"__"^ci) rc.typed_attributes in
            let attribute_initializer = make_attribute_initializer loc (name^"__"^ci) attributes in
            let consname = constructor_name rc (name^"__"^ci) in
            let argvars = List.mapi (fun i _ -> Printf.sprintf "v_%d" i) tl in
            let consbody = Expr.applist <:expr< $uid:ci$ >> (List.map (to_expr loc) argvars) in
            let consbody = <:expr< $consbody$ $attribute_initializer$ >> in
            let consexp = List.fold_right
                (fun v rhs -> <:expr< fun $lid:v$ -> $rhs$ >>)
                argvars consbody in
            [<:str_item< value $lid:consname$ = $consexp$ >>]
          else
            []
      ]) |> List.concat
  ] in
  <:str_item< declare $list:[top_cons]@prod_cons_list$ end >>
;

end
;


value make_twolevel_type_decl rc ~{with_manifest} ~{skip_attributed} td =
  let open Ag_types in
  let open AG.PN in
  let loc = loc_of_type_decl td in
  let name = td.tdNam |> uv |> snd |> uv in
  let (skip_attributed, attributes) =
    if skip_attributed then (True, []) else
      match List.assoc name rc.AC.typed_attributes with [
        x -> (False, x)
      | exception Not_found ->
        match List.find_opt (fun (name', _) ->
          let pn = Demarshal.parse_prodname loc name' in
          name = pn.nonterm_name) rc.AC.typed_attributes with [
          None -> (True, [])
        | Some (name',_) ->
          Ploc.raise loc
            (Failure Fmt.(str "make_twolevel_type_decl: skipping attribution of type %s but production %s is attributed"
                            name name'))
        ]
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

  let prod_tdl = ref [] in
  let data_tdDef =
    let tdDef = match td.tdDef with [
      <:ctyp< $_$ == $t$ >> when not with_manifest -> t
    | <:ctyp< $_$ == $t$ >> when with_manifest -> td.tdDef
    | t when is_generative_type t && with_manifest ->
      Ploc.raise (loc_of_type_decl td)
        (Failure Fmt.(str "cannot generate requested \"normal\" type declaration b/c original type is not manifest: %s"
                        name))
    | t -> t
    ] in
    if skip_attributed then tdDef else
    match tdDef with [
      <:ctyp:< [ $list:branches$ ] >> ->
        let branches = branches |> List.map (fun [
              <:constructor:< $uid:ci$ of $list:tl$ $algattrs:algattrs$ >> as gc ->
                if List.mem_assoc (name^"__"^ci) rc.AC.typed_attributes then
                  let al = List.assoc (name^"__"^ci) rc.AC.typed_attributes in
                  let prod_attr_type_name = name^"__"^ci^"_attributes" in
                  let ltl = al |> List.map (fun (aname, ty) ->
                      (loc, name^"__"^ci^"__"^aname, True, <:ctyp< option $ty$ >>, <:vala< [] >>)) in
                  let prod_attr_type = <:ctyp< $lid:prod_attr_type_name$ >> in
                  let prod_attr_type_tdDef = <:ctyp< { $list:ltl$ } >> in do {
                    Std.push prod_tdl <:type_decl< $lid:prod_attr_type_name$ = $prod_attr_type_tdDef$ >> ;
                    <:constructor< $uid:ci$ of $list:tl@[prod_attr_type]$ $algattrs:algattrs$ >>
                  }
                else gc
              ]) in
        <:ctyp< [ $list:branches$ ] >>
      | ty ->
        Ploc.raise (MLast.loc_of_ctyp ty)
          (Failure Fmt.(str "Internal Error constructing data_tdDef for %s:@ ty = %a"
                          name Pp_MLast.pp_ctyp ty))

    ] in

  [ { (td) with
      tdNam =
        let n = <:vala< data_name >> in
        <:vala< (loc, n) >>
      ; tdDef = data_tdDef
    } ]@
  prod_tdl.val@
  wrapped_type_decls
;

value normal_type_decl rc td =
  let skip_attributed = True in
  let with_manifest = True in
  make_twolevel_type_decl rc ~{with_manifest=with_manifest} ~{skip_attributed=skip_attributed} td
;

value attributed_type_decl rc td =
  let with_manifest = False in
  make_twolevel_type_decl rc ~{with_manifest=with_manifest} ~{skip_attributed=False} td
;

value str_item_generate_attributed loc rc tdl =
  let new_tdl =
    tdl
    |> List.map (attributed_type_decl rc)
    |> List.concat
    |> List.map AC.strip_deriving_attributes in
  let (normal_tdl, normal_module) = match rc.normal_module_name with [
    None -> (tdl, <:str_item< declare end >>)
  | Some normname ->
    let normal_tdl =
      tdl
      |> List.map (normal_type_decl rc)
      |> List.concat
      |> List.map AC.strip_deriving_attributes in
    (normal_tdl,
     <:str_item< module $uid:normname$ = struct
                  type $list:normal_tdl$ ;
                  end >>)
  ] in
  let attributed_constructors = List.map (AC.generate_attributed_constructor rc) rc.AC.type_decls in
  let aa_st = <:str_item< declare
                  $stri:normal_module$ ;
                  module $uid:rc.attributed_module_name$ = struct
                  open Pa_ppx_ag_runtime.Attributes ;
                  type $list:new_tdl$ ;
                  declare $list:attributed_constructors$ end ;
                  end ;
                end >> in
  (aa_st, normal_tdl, new_tdl)
;

value str_item_gen_attributed name arg = fun [
  <:str_item:< type $_flag:_$ $list:tdl$ >> ->
    let rc = AC.build_context loc arg tdl in
    let (aa_st, _, _) = str_item_generate_attributed loc rc tdl in
    aa_st

| _ -> assert False ]
;

Pa_deriving.(Registry.add PI.{
  name = "attributed"
; alternates = []
; options = ["optional";"plugin_name";"normal_module_name";"attributed_module_name";"attributes"]
; default_options = []
; alg_attributes = []
; expr_extensions = []
; ctyp_extensions = []
; expr = (fun arg e -> assert False)
; ctyp = (fun arg e -> assert False)
; str_item = str_item_gen_attributed
; sig_item = (fun arg e -> assert False)
})
;

