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

module PP_hum = struct
value ctyp pps ty = Fmt.(pf pps "%s" (Eprinter.apply Pcaml.pr_ctyp Pprintf.empty_pc ty));
value expr pps ty = Fmt.(pf pps "%s" (Eprinter.apply Pcaml.pr_expr Pprintf.empty_pc ty));
value patt pps ty = Fmt.(pf pps "%s" (Eprinter.apply Pcaml.pr_patt Pprintf.empty_pc ty));

end
;
module AG = struct

module NodeReference = struct
  type t = [
      PARENT of option string
    | CHILD of option string and int
    | PRIM of option string and int
    ] ;
  value pp_hum pps = fun [
    PARENT (Some name) -> Fmt.(pf pps "[%%nterm %s ;]" name)
  | PARENT None -> Fmt.(pf pps "[%%nterm 0 ;]")
  | CHILD (Some name) i -> Fmt.(pf pps "[%%nterm %s.(%d) ;]" name i)
  | CHILD None i -> Fmt.(pf pps "[%%nterm %d ;]" i)
  | PRIM (Some name) i -> Fmt.(pf pps "[%%prim %s.(%d) ;]" name i)
  | PRIM None i -> Fmt.(pf pps "[%%nterm %d ;]" i)
  ]
  ;
  value to_patt loc = fun [
    PARENT (Some name) -> <:patt< [%nterm $lid:name$ ;] >>
  | PARENT None -> <:patt< [%nterm 0 ;] >>
  | CHILD (Some name) i -> <:patt< [%nterm $lid:name$ . ( $int:string_of_int i$ ) ;] >>
  | CHILD None i -> <:patt< [%nterm $int:string_of_int i$ ;] >>
  | PRIM (Some name) i -> <:patt< [%prim $lid:name$ . ( $int:string_of_int i$ ) ;] >>
  | PRIM None i -> <:patt< [%prim $int:string_of_int i$ ;] >>
  ]
  ;
  value to_expr loc = fun [
    PARENT (Some name) -> <:expr< [%nterm $lid:name$ ;] >>
  | PARENT None -> <:expr< [%nterm 0 ;] >>
  | CHILD (Some name) i -> <:expr< [%nterm $lid:name$ . ( $int:string_of_int i$ ) ;] >>
  | CHILD None i -> <:expr< [%nterm $int:string_of_int i$ ;] >>
  | PRIM (Some name) i -> <:expr< [%prim $lid:name$ . ( $int:string_of_int i$ ) ;] >>
  | PRIM None i -> <:expr< [%prim $int:string_of_int i$ ;] >>
  ]
  ;

end ;
module NR = NodeReference ;

  module ProductionName = struct
  type t = {
    nonterm_name: string
  ; case_name: option string
  } ;
  value pp_hum pps = fun [
    {nonterm_name=nonterm_name; case_name = None} -> Fmt.(pf pps "%s" nonterm_name)
  | {nonterm_name=nonterm_name; case_name = Some case_name} -> Fmt.(pf pps "%s__%s" nonterm_name case_name)
  ]
  ;
  end ;
  module PN = ProductionName ;
  module AEQ = struct
    type t = {
      lhs : (NR.t * string)
    ; rhs_nodes : list (NR.t * string)
    ; rhs_expr : MLast.expr
    }
    ;
    value pp_hum pps x = Fmt.(pf pps "%a.%s := %a\n" NR.pp_hum (fst x.lhs) (snd x.lhs) PP_hum.expr x.rhs_expr) ;
  end ;
  module Production = struct
    type t = {
      name : PN.t
    ; node_aliases : list (NR.t * NR.t)
    ; equations : list AEQ.t
    ; patt : MLast.patt
    } ;
    value pp_hum pps x = Fmt.(pf pps "%a : %a\n%a" PN.pp_hum x.name PP_hum.patt x.patt (list AEQ.pp_hum) x.equations) ;
  end ;
  module P = Production ;
end ;

module AGContext = struct

open Pa_ppx_params.Runtime ;

value expr_to_attribute_reference e =
  let open AG in
  let open AEQ in
  match e with [
    <:expr< [%nterm $lid:tyname$;] . $lid:attrna$ >> -> 
    (NR.PARENT (Some tyname), attrna)
  | <:expr< [%nterm 0;] . $lid:attrna$ >> ->
    (NR.PARENT None, attrna)
  | <:expr< [%nterm $int:n$;] . $lid:attrna$ >> ->
    (NR.CHILD None (int_of_string n), attrna)
  | <:expr< [%nterm $lid:tyname$ . ( $int:n$ );] . $lid:attrna$ >> ->
    (NR.CHILD (Some tyname) (int_of_string n), attrna)
  | <:expr< [%prim $int:n$;] . $lid:attrna$ >> ->
    (NR.PRIM None (int_of_string n), attrna)
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

value name_re = Pcre.regexp "^(.*)__((?:_?[^_])+_?)$" ;
value parse_prodname loc s =
  let open AG in
  match Pcre.extract ~{rex=name_re} ~{pos=0} s with [
    [|_;lhs;rhs|] ->
    { PN.nonterm_name = lhs; case_name = Some rhs }
  | exception Not_found ->
    { PN.nonterm_name = s ; case_name = None }
  ]
;

value extract_attribute_equations loc l : (alist AG.PN.t (list AG.AEQ.t)) =
  l |> List.map (fun (prodname, e) ->
    let prodname = parse_prodname loc prodname in
    match e with [
      <:expr< do { $list:l$ } >> ->
      (prodname, List.map assignment_to_equation l)
    | <:expr< $_$ . val := $_$ >> ->
      (prodname, [assignment_to_equation e])
    ])
;

value compute_name2nodename type_decls =
  type_decls |> List.map (fun (name, td) ->
     match td.tdDef with [
       (<:ctyp< unique $lid:nodename$ >>
       | <:ctyp< Unique.unique $lid:nodename$ >>
       | <:ctyp< Pa_ppx_unique_runtime.Unique.unique $lid:nodename$ >>) ->
       [(name,nodename)]
     | _ -> []
     ]
    ) |> List.concat
;

type t = {
  optional : bool
; plugin_name : string
; module_name : uident
; attributes : (alist lident (alist lident ctyp))
; raw_attribution: (alist lident expr) [@name attribution;]
; attribution: (alist AG.PN.t (list AG.AEQ.t)) [@computed extract_attribute_equations loc raw_attribution;]
; name2nodename : (alist lident lident) [@computed compute_name2nodename type_decls;]
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

module NodeAliases = struct
  open AG ;
  value mk () = ref [] ;
  value get x = x.val ;
  value next_nterm_number node_aliases name =
    match List.find_map (fun [
        (NR.CHILD (Some n) i, _) when n = name -> Some i
      | _ -> None
      ]) node_aliases.val with [
        Some n -> n+1
      | None -> 1
      ]
  ;
  value next_prim_number node_aliases name =
    match List.find_map (fun [
        (NR.PRIM (Some n) i, _) when n = name ->
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

value branch2production loc rc lhs_name b =
  let open AG in
  match b with [
  <:constructor< $uid:ci$ of $list:tl$ $_algattrs:_$ >> ->
  let node_aliases = NA.mk() in
  let patl = tl |> List.mapi (fun i -> fun [
      <:ctyp:< $lid:tyname$ >> when List.mem_assoc tyname rc.name2nodename -> do {
        let aliasnum = NA.next_nterm_number node_aliases tyname in
        NA.add node_aliases (NR.CHILD (Some tyname) aliasnum, NR.CHILD None (i+1)) ;
        NR.to_patt loc (NR.CHILD None (i+1))
      }
    | <:ctyp:< $lid:tyname$ >> as z when List.mem (canon_ctyp z) builtin_types -> do {
        let aliasnum = NA.next_prim_number node_aliases tyname in
        NA.add node_aliases (NR.PRIM (Some tyname) aliasnum, NR.PRIM None (i+1)) ;
        NR.to_patt loc (NR.PRIM None (i+1))
      }
    | ty ->
      Ploc.raise (MLast.loc_of_ctyp ty)
        (Failure Fmt.(str "productions: unsupported rhs-of-production type: %s@ %a"
                        lhs_name Pp_MLast.pp_ctyp ty))
  ]) in
  let pn = { PN.nonterm_name = lhs_name ; case_name = Some ci } in
  { P.name = pn
  ; node_aliases = [(NR.PARENT (Some lhs_name), NR.PARENT None) :: NA.get node_aliases]
  ; equations = match List.assoc pn rc.attribution with [ x -> x | exception Not_found -> [] ]
  ; patt = Patt.applist <:patt< $uid:ci$ >> patl
  }
]
;

value tuple2production loc rc lhs_name tl =
  let open AG in
  let node_aliases = NA.mk() in
  let patl = tl |> List.mapi (fun i -> fun [
      <:ctyp:< $lid:tyname$ >> when List.mem_assoc tyname rc.name2nodename -> do {
        let aliasnum = NA.next_nterm_number node_aliases tyname in
        NA.add node_aliases (NR.CHILD (Some tyname) aliasnum, NR.CHILD None (i+1)) ;
        NR.to_patt loc (NR.CHILD None (i+1))
      }
    | <:ctyp:< $lid:tyname$ >> as z when List.mem (canon_ctyp z) builtin_types -> do {
        let aliasnum = NA.next_prim_number node_aliases tyname in
        NA.add node_aliases (NR.PRIM (Some tyname) aliasnum, NR.PRIM None (i+1)) ;
        NR.to_patt loc (NR.PRIM None (i+1))
      }
    | ty ->
      Ploc.raise (MLast.loc_of_ctyp ty)
        (Failure Fmt.(str "productions: unsupported rhs-of-production type: %s@ %a"
                        lhs_name Pp_MLast.pp_ctyp ty))
  ]) in
  let pn = { PN.nonterm_name = lhs_name ; case_name = None } in
  { P.name = pn
  ; node_aliases = [(NR.PARENT (Some lhs_name), NR.PARENT None) :: NA.get node_aliases]
  ; equations = match List.assoc pn rc.attribution with [ x -> x | exception Not_found -> [] ]
  ; patt = Patt.tuple loc patl
  }
;

value productions rc =
  rc.type_decls |>
  List.map (fun (name, td) ->
    if List.mem_assoc name rc.name2nodename then
      let node_name = List.assoc name rc.name2nodename in
      let td = match List.assoc node_name rc.type_decls with [
        x -> x
      | exception Not_found -> assert False
      ] in
      match td.tdDef with [
        (<:ctyp:< [ $list:branches$ ] >> | <:ctyp:< $_$ == [ $list:branches$ ] >>) ->
          List.map (branch2production loc rc name) branches
      | <:ctyp:< ( $list:tl$ ) >> ->
          [tuple2production loc rc name tl]
      | <:ctyp:< $lid:_$ >> as z ->
        [tuple2production loc rc name [z]]
      | ty ->
        Ploc.raise (MLast.loc_of_ctyp ty) (Failure Fmt.(str "productions: extraction from type %s failed" name))
      ]
    else []
  )
  |> List.concat
;
end;

value str_item_gen_ag name arg = fun [
  <:str_item:< type $_flag:_$ $list:tdl$ >> ->
    let rc = AGContext.build_context loc arg tdl in
    let _ = AGContext.productions rc in
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

