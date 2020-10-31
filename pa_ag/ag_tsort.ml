(* camlp5r *)
(* ag_tsort.ml,v *)

open Asttools;
open MLast;
open Pa_ppx_base ;
open Pa_passthru ;
open Ppxutil ;
open Surveil ;
open Pa_deriving_base ;
open Pa_ppx_utils ;
open Ag_types ;

value node_hash_module nt = Printf.sprintf "HTAttr_%s" nt ;

value node_attribute_table_declaration memo =
  let open AGOps.NTOps in
  let open AG in
  let ag = memo.ag in
  let loc = ag.loc in
  (ag.typed_attributes |> List.map (fun (nt,_) ->
      Reloc.str_item (fun _ -> Ploc.dummy) 0
      <:str_item< module $uid:node_hash_module nt$ = Hashtbl.Make(struct
                    type t = $lid:nt$ ;
                    open Pa_ppx_unique_runtime.Unique ;
                    value equal a b = a.id = b.id ;
                    value hash x = x.id ;
                  end) >>
    ))@
  (ag.typed_attributes |> List.map (fun (nt, attrs) ->
      let attr_type_name = Printf.sprintf "%s_attrs_t" nt in
      let ltl = attrs |> List.map (fun (aname, aty) ->
          let ht_ty = <:ctyp< $uid:node_hash_module nt$ . t $aty$ >> in
          (MLast.loc_of_ctyp aty, aname, False, ht_ty, <:vala< [] >>)) in
      let ltl = [(loc, "parent",False, <:ctyp< $uid:node_hash_module nt$ . t (node_t * int) >>, <:vala< [] >>)::ltl] in
      <:str_item< type $lid:attr_type_name$ = { $list:ltl$ } >>
     ))@
  [let ltl = ag.typed_attributes |> List.map (fun (nt, _) ->
       let attr_type_name = Printf.sprintf "%s_attrs_t" nt in
       (loc, nt, False, <:ctyp< $lid:attr_type_name$ >>, <:vala< [] >>)
     ) in
   <:str_item< type attributes_t = { $list:ltl$ } >> ;
   let lel = ag.typed_attributes |> List.map (fun (nt, al) ->
       let lel = al |> List.map (fun (aname, _) ->
           (<:patt< $lid:aname$ >>, <:expr< $uid:node_hash_module nt$ . create 23 >>)) in
       let lel = lel @ [(<:patt< parent >>, <:expr< $uid:node_hash_module nt$ . create 23 >>)] in
       (<:patt< $lid:nt$ >>, <:expr< { $list:lel$ } >>)) in
   Reloc.str_item (fun _ -> Ploc.dummy) 0
   <:str_item< value make_attributes_t () = { $list:lel$ } >>]
;

value node_constructor nt = Printf.sprintf "Node_%s" nt ;
value attr_constructor attrna = Printf.sprintf "Attr_%s" attrna ;
value preprocess_fname nt = Printf.sprintf "preprocess_%s" nt ;

value node_type_declaration memo =
  let open AGOps.NTOps in
  let open AG in
  let ag = memo.ag in
  let loc = ag.loc in
  let branches = ag.nonterminals |> List.map (fun nt ->
      (loc, <:vala< node_constructor nt >>, <:vala< [<:ctyp< $lid:nt$ >>] >>, <:vala< None >>, <:vala< [] >>)
    ) in
  <:str_item< type node_t = [ $list:branches$ ] >>
;

value attr_type_declaration memo =
  let open AGOps.NTOps in
  let open AG in
  let ag = memo.ag in
  let loc = ag.loc in
  let branches =
    ag.typed_attributes
    |> List.map (fun (nt, al) -> al)
    |> List.concat
    |> List.map fst
    |> Std2.hash_uniq
    |> List.sort Stdlib.compare
    |> List.map (fun attrna ->
        (loc, <:vala< attr_constructor attrna >>, <:vala< [] >>, <:vala< None >>, <:vala< [] >>)) in
  <:str_item< type attrname_t = [ $list:branches$ ] >>
;

value typed_equation_to_deps taeq =
  let open AG in
  let open TAEQ in
  taeq.rhs_nodes |> List.map (fun rhs -> (rhs, taeq.lhs))
  |> Std.filter (fun [
      ((TNR.PRIM _ _, _), _) -> False
    | (_, (TNR.PRIM _ _, _)) -> assert False
    | _ -> True ])
;

value actual_dep_function_declarations memo =
  let open AGOps.NTOps in
  let open AG in
  let ag = memo.ag in
  let loc = ag.loc in
  (ag.productions |> List.map (fun (nt, pl) ->
       let branches = pl |> List.map (fun p ->
           let rev_patt_var_to_noderef = List.map (fun (a,b) -> (b,a)) p.P.patt_var_to_noderef in
           let deps = p.P.typed_equations |> List.map typed_equation_to_deps |> List.concat in
           let deps = Std2.hash_uniq deps in
           let aref_to_exp = fun [
             (TNR.PARENT tyname, aname) -> <:expr< ($uid:node_constructor tyname$ lhs, $uid:attr_constructor aname$) >>
           | (((TNR.CHILD tyname i) as nr), aname) ->
              let v = match List.assoc nr rev_patt_var_to_noderef with [
                x -> x
              | exception Not_found ->
                Ploc.raise loc
                  (Failure "actual_dep_function_declarations: cannot map attribute-ref back to variable")
              ] in
              <:expr< ($uid:node_constructor tyname$ $lid:v$, $uid:attr_constructor aname$) >>
           | _ -> assert False
           ] in
           let deps = List.map (fun (a, b) -> (aref_to_exp a, aref_to_exp b)) deps in
           let depacts = deps |> List.map (fun (a,b) -> <:expr< Std.push acc ($a$, $b$) >>) in
           let child_node_acts = rev_patt_var_to_noderef |> List.filter_map (fun [
             (TNR.CHILD tyname i, v) ->
             let abs_childnum = match List.assoc v p.P.patt_var_to_childnum with [
               x -> x | exception Not_found -> assert False
             ] in
             let fname = preprocess_fname tyname in
             Some <:expr< do {
                          $uid:node_hash_module tyname$ . add
                            attrs . $lid:tyname$ . parent
                            $lid:v$
                            ($uid:node_constructor nt$ lhs, $int:string_of_int abs_childnum$) ;
                          $lid:fname$ attrs acc $lid:v$
                          } >>
           | (TNR.PRIM _ _, _) -> None
           ]) in
           (p.P.patt, <:vala< None >>,
            <:expr< do { $list:depacts@child_node_acts$ } >>)
         ) in
       (<:patt< $lid:preprocess_fname nt$ >>,
        Reloc.expr (fun _ -> Ploc.dummy) 0
        <:expr< fun attrs -> fun acc -> fun lhs -> match lhs.node with [ $list:branches$ ] >>,
        <:vala< [] >>)
     ))
;

value compile_teqn_body p teqn =
  let open AG in
  let open P in
  let open TAEQ in
  let open TNR in
  let loc = teqn.loc in
  <:expr< assert False >>
;

(** generate synthesized-attribute branches

    (1) args are noderef+attrname

    (2) for each equation that is for a synthesized attribute, we
   generate code to check that all required attributes are defined,
   that the specified attribute is *not* defined, and then execute the
   equation, define the attribute's entry.
*)
value synthesized_attribute_branch p teqn = do {
  let open AG in
  let open P in
  let open TAEQ in
  let open TNR in
  let loc = teqn.loc in
  let rev_patt_var_to_noderef = List.map (fun (a,b) -> (b,a)) p.patt_var_to_noderef in
  match teqn.lhs with [
    (PARENT nt, attrna) ->
    let attrcons = attr_constructor attrna in
    let ntcons = node_constructor nt in
    let nthash = node_hash_module nt in
    let patt = <:patt< ($uid:ntcons$ ({node= $p.patt$ } as lhs), $uid:attrcons$) >> in
    let check_parent_unset = <:expr< assert (not ($uid:nthash$ . mem attrs . $lid:nt$ . $lid:attrna$ lhs)) >> in
    let check_deps_set = teqn.rhs_nodes |> List.filter_map (fun [
        (((CHILD dnt _) as dnr), dattr) ->
        let v = match List.assoc dnr rev_patt_var_to_noderef with [ x -> x | exception Not_found -> assert False ] in
        Some <:expr< assert ($uid:node_hash_module dnt$ . mem attrs . $lid:dnt$ . $lid:dattr$ $lid:v$) >>
      | (PARENT dnt, dattr) ->
        Some <:expr< assert ($uid:nthash$ . mem attrs . $lid:nt$ . $lid:dattr$ lhs) >>
      | (PRIM _ _, _) -> None
      ]) in
    let body = compile_teqn_body p teqn in
    let l = [check_parent_unset]@check_deps_set@[body] in
    (patt, <:vala< None >>, <:expr< do { $list:l$ } >>)
  | _ -> assert False
  ]
}
;