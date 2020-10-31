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

value node_attribute_table_declaration memo =
  let open AGOps.NTOps in
  let open AG in
  let ag = memo.ag in
  let loc = ag.loc in
  (ag.typed_attributes |> List.map (fun (nt,_) ->
      let mname = Printf.sprintf "HTAttr_%s" nt in
      <:str_item< module $uid:mname$ = Hashtbl.Make(struct
                    type t = $lid:nt$ ;
                    open Pa_ppx_unique_runtime.Unique ;
                    value equal a b = a.id = b.id ;
                    value hash x = x.id ;
                  end) >>
    ))@
  (ag.typed_attributes |> List.map (fun (nt, attrs) ->
      let attr_type_name = Printf.sprintf "%s_attrs_t" nt in
      let ltl = attrs |> List.map (fun (aname, aty) ->
          let ht_name = Printf.sprintf "HTAttr_%s" nt in
          let ht_ty = <:ctyp< $uid:ht_name$ . t $aty$ >> in
          (MLast.loc_of_ctyp aty, aname, False, ht_ty, <:vala< [] >>)) in
      <:str_item< type $lid:attr_type_name$ = { $list:ltl$ } >>
     ))@
  [let ltl = ag.typed_attributes |> List.map (fun (nt, _) ->
       let attr_type_name = Printf.sprintf "%s_attrs_t" nt in
       (loc, nt, False, <:ctyp< $lid:attr_type_name$ >>, <:vala< [] >>)
     ) in
   <:str_item< type attributes_t = { $list:ltl$ } >>]
;

value node_type_declaration memo =
  let open AGOps.NTOps in
  let open AG in
  let ag = memo.ag in
  let loc = ag.loc in
  let branches = ag.nonterminals |> List.map (fun nt ->
      (loc, <:vala< Printf.sprintf "Node_%s" nt >>, <:vala< [<:ctyp< $lid:nt$ >>] >>, <:vala< None >>, <:vala< [] >>)
    ) in
  <:str_item< type node_type_t = [ $list:branches$ ] >>
;
(*  
value actual_dep_function_declarations memo =
  let open AGOps.NTOps in
  let open AG in
  let ag = memo.ag in
  let loc = ag.loc in
  (ag.productions |> List.map (fun (nt, pl) ->
       let branches = pl |> List.map (fun p ->
           (p.P.patt, <:vala< None >>,
            
         ) in
     ))
*)
