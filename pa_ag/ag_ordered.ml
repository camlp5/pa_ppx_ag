
open Pa_ppx_utils ;
open Pa_ppx_base ;
open Ppxutil ;

open Ag_types ;
open AG ;
open AGOps ;

value nddp p =
  p
  |> P.ddp
  |> of_list
  |> TAROps.transitive_closure
  |> g_filter_edges (let open TAR in fun s d -> match (s,d) with [
      (NT nt1 _, NT nt2 _) -> nt1 = nt2
    | _ -> False
    ])
  |> to_list
;

(*

1. For all p in P , IDP (p) := NDDP (p).

2. For all X in the vocabulary of G,
    IDS(X) := { (X.a, X.b) | exists q such that (X.a, X.b) in IDP(q)+ }

3. For all p : [X_0 -> X_1 ... X_n] in P ,
    IDP (p) := IDP (p) union IDS(X_0) union ... union IDS(X_n)

4. Repeat (2) and (3) until there is no change in any IDP or IDS

*)

value tar_map_nt_to_parent = fun [
  (TAR.NT (TNR.PARENT _) _) as tar -> tar
| (TAR.NT (TNR.CHILD nterm _) attrna) as tar -> TAR.NT(TNR.PARENT nterm) attrna
]
;

value tar_map_nt_to_child i = fun [
  (TAR.NT (TNR.PARENT nterm) attrna) -> (TAR.NT (TNR.CHILD nterm i) attrna)
| _ -> assert False
]
;

type ids_t = list (string * (list (string * string))) [@@deriving show;] ;
type idp_t = list (PN.t[@printer PN.pp_hum;] * (list (TAR.t[@printer TAR.pp_hum;] * TAR.t[@printer TAR.pp_hum;]))) [@@deriving show;] ;

value new_ids (idp_plus : idp_t) =
  let open TAR in
  let open TNR in
  idp_plus
  |> List.concat_map snd
  |> List.filter (fun [
      (NT nt1 _, NT nt2 _) -> nt1=nt2
    | _ -> False
    ])
  |> List.map (fun (tar1, tar2) -> (tar_map_nt_to_parent tar1, tar_map_nt_to_parent tar2))
  |> canon
  |> Std.nway_partition (fun tar1 tar2 -> match (tar1, tar2) with [
      ((NT nt1  _, _), (NT nt2 _, _)) -> nt1=nt2
    | _ -> assert False
    ]) 
  |> List.map (fun l ->
      let nt = match l with [ [(NT (PARENT nterm) _, _)::_] -> nterm | _ -> assert False ] in
      let nt_proj_attrna = fun [ NT _ attrna -> attrna | _ -> assert False ] in
      (nt, l |> List.map (fun (a,b) -> (nt_proj_attrna a, nt_proj_attrna b)))
    )
;

value add_idp ag new_ids =
  let open TAR in
  let open TNR in
  let lookup_in_new_ids nt = match List.assoc nt new_ids with [
    x -> x | exception Not_found -> [] ] in
  ag
  |> AG.all_productions
  |> List.map (fun p ->
      let nl = LSet.toList p.P.typed_nodes in
      (p.P.name, 
           nl
           |> List.concat_map (fun [
               (PARENT nterm | CHILD nterm _) as nt ->
               let l = lookup_in_new_ids nterm in
               List.map (fun (a,b) -> (NT nt a, NT nt b)) l
             | _ -> []
             ])
           |> canon
      )
    )
;

value idp_ids_step ag ((idp : idp_t), (ids : ids_t)) = do {
  let open TAR in
  let open TNR in
  let idp_plus = List.map (fun (pn, idp_p) ->
      (pn, idp_p |> tclos)
    ) idp in
  let _ = new_ids idp_plus in
  let new_ids = new_ids idp_plus in
  let lookup_in_new_ids nt = match List.assoc nt new_ids with [
    x -> x | exception Not_found -> [] ] in
    let add_idp = add_idp ag new_ids in
    let new_idp = idp |> List.map (fun (pn, idp_p) ->
      (pn, canon (idp_p@(List.assoc pn add_idp)))) in
    (canon new_idp, canon new_ids)
}
;
    
value idp_ids ag =
  let idp0 =
    ag
    |> AG.all_productions
    |> List.map (fun p -> (p.P.name, p |> P.ddp |> of_list |> TAROps.transitive_closure |> to_list)) in
  let rec iterate arg =
    let arg' = idp_ids_step ag arg in
    if arg = arg' then arg
    else iterate arg'
  in iterate (idp0, [])
;

value check_idp_ids (idp,ids) = do {
  let failed = ref False in
  idp |> List.iter (fun (pn, _idp) ->
      if TARDfs.has_cycle (_idp |> of_list) then do {
        Fmt.(pf stderr "IDP(%a) has cycle:@ %a\n%!" PN.pp_hum pn pp_idp_t [(pn,_idp)]) ;
        failed.val := True ;
      }
      else ()
    ) ;
  ids |> List.iter (fun (nt, _ids) ->
      if StrDfs.has_cycle (_ids |> strg_of_list) then do {
        Fmt.(pf stderr "IDS(%s) has cycle:@ %a\n%!" nt pp_ids_t [(nt,_ids)]) ;
        failed.val := True ;
      }
      else ()
    ) ;
    if failed.val then failwith "cycles found in IDP/IDS" else () ;
}
;

(*
From Waite:

Here m is the smallest n such that T_{n-1}(X) union T_{n}(X) = A(X), T_{-1}(X) = T_{0}(X) = {},
and for k > 0:
T_{2k-1}(X) = { a in AS(X) | a -> b in IDS(X) implies b in union(T_{j}(X), j <= (2k - 1)) }
T_{2k}(X) =   { a in AI(X) | a -> b in IDS(X) implies b in union(T_{j}(X), j <= 2k) }

================================================================

Well use Kastens' formulation.

From Kastens:

A_{X,1} =  { X.a in AS | there is no X.b such that (X.a, X.b) in IDS+ }
A_{X, 2n} = { X.a in AI | for all X.b in A(X):
                            (X.a, X.b) in IDS+ implies
                            X.b in union{m <= 2n}(A_{X,m}) } - union{k<=2n-1}(A_{X,k})

A_{X, 2n+1} = { X.a in AS | for all X.b in A(X):
                            (X.a, X.b) in IDS+ implies
                            X.b in union{m <= 2n+1}(A_{X,m}) } - union{k<=2n}(A_{X,k})

*)

value compute_t_sofar t =
  t |> List.map (fun (a,b) -> a@b) |> List.concat |> canon
;

value compute_ti_inh_step (_as, _ai, _a, _ids_plus) t_sofar ti_sofar =
  let added =
    _ai
    |> List.filter (fun a ->
        let succl = match StrG.succ _ids_plus a with [ x -> x | exception Invalid_argument _ -> [] ] in
        succl |> List.for_all (fun b ->
          List.mem b ti_sofar || List.mem b t_sofar
        )
    ) in
  canon (added @ ti_sofar)
;

value compute_ti_inh (_as, _ai, _a, _ids_plus) t_sofar =
  let rec crec sofar =
    let sofar' = compute_ti_inh_step (_as, _ai, _a, _ids_plus) t_sofar sofar in
    if sofar = sofar' then sofar
    else crec sofar' in
  Std.subtract (crec []) t_sofar
;

value compute_ti_syn_step (_as, _ai, _a, _ids_plus) t_sofar ti_sofar =
  let added =
    _as
    |> List.filter (fun a ->
        let succl = match StrG.succ _ids_plus a with [ x -> x | exception Invalid_argument _ -> [] ] in
        succl |> List.for_all (fun b ->
          List.mem b ti_sofar || List.mem b t_sofar
        )
    ) in
  canon (added @ ti_sofar)
;

value compute_ti_syn (_as, _ai, _a, _ids_plus) t_sofar =
  let rec crec sofar =
    let sofar' = compute_ti_syn_step (_as, _ai, _a, _ids_plus) t_sofar sofar in
    if sofar = sofar' then sofar
    else crec sofar' in
  Std.subtract (crec []) t_sofar
;

value compute_t1 (_as, _ai, _a, _ids_plus) =
  compute_ti_syn (_as, _ai, _a, _ids_plus) []
;

value compute_pass (_as, _ai, _a, _ids_plus) t =
  let t0 = compute_ti_syn (_as, _ai, _a, _ids_plus) (compute_t_sofar t) in
  let t1 = compute_ti_inh (_as, _ai, _a, _ids_plus) (compute_t_sofar [([], t0) :: t]) in
  (t1, t0)
;

value compute_all_passes (_as, _ai, _a, _ids_plus) =
  let rec crec t =
    let (inh,syn) = compute_pass (_as, _ai, _a, _ids_plus) t in
    if [] = inh && [] = syn then
      t
    else crec [(inh,syn) :: t] in
  crec []
;

value compute_t_for_nt memo (idp, ids) nt =
  let _as = NTOps._AS memo nt in
  let _ai = NTOps._AI memo nt in
  let _a = NTOps._A memo nt in
  let _ids = match List.assoc nt ids with [ x -> x | exception Not_found -> [] ] in
  let _ids_plus = _ids |> strg_of_list |> StrOps.transitive_closure in
  let _t = compute_all_passes (_as,_ai,_a, _ids_plus) in do {
    assert (canon _a = (compute_t_sofar _t)) ;
    _t
  }
;

value compute_t memo =
  let (idp, ids) = idp_ids memo.NTOps.ag in do {
    check_idp_ids (idp,ids) ;
    memo.ag |> AG.nonterminals |> List.map (fun nt -> (nt, compute_t_for_nt memo (idp, ids) nt))
  }
;

value must_lookup_t nt _t =
  match List.assoc nt _t with [ x -> x | exception Not_found -> assert False ]
;

  value rec find_mapi f i = fun [
    [] -> None
  | [x :: l] ->
    match f i x with [
        Some _ as result -> result
      | None -> find_mapi f (i+1) l
    ]
  ]
  ;
  value find_mapi f l = find_mapi f 0 l ;

module VS = struct
  type tar_t = [
      EXTERNAL of (TNR.t [@printer (TNR.pp_hum ~{is_chainstart=False});]) and int
    | AR of (TAR.t [@printer TAR.pp_hum;])
  ] [@@deriving show;]
  ;

module G = Graph.Persistent.Digraph.ConcreteBidirectional(
  struct
    type t = tar_t ;
      value equal = (=) ;
      value compare = Stdlib.compare ;
      value hash = Hashtbl.hash ;
  end) ;
module TSort = Graph.Topological.Make_stable(G) ;
module Ops = Graph.Oper.Make(Graph.Builder.P(G)) ;
module Dfs = Graph.Traverse.Dfs(G) ;

value of_list l =
  List.fold_left (fun g (s,d) -> G.add_edge g s d) G.empty l
;
    
value to_list g =
  (G.fold_edges (fun s d acc -> [(s, d) :: acc]) g [])
  |> canon
;

  value find_partition_number loc _t attrna =
    match _t |> find_mapi (fun i (inh, syn) ->
      if List.mem attrna inh then Some (True, i)
      else if List.mem attrna syn then Some (False, i)
      else None) with [
      Some n -> n
    | None -> Ploc.raise loc
        (Failure Fmt.(str "find_partition_number: cannot find attr %s in partition %s" attrna
                        ([%show: list (list string * list string)] _t)))
    ]
  ;

  value upconvert_tar loc _t tar = match tar with [
    TAR.PROD _ _ -> AR tar
  | TAR.NT (PARENT nt as nr) attrna ->
    let _t = must_lookup_t nt _t in
    let (is_inh, partn) = find_partition_number loc _t attrna in
    if is_inh then EXTERNAL nr partn else AR tar

  | TAR.NT (CHILD nt i as nr) attrna ->
    let _t = must_lookup_t nt _t in
    let (is_inh, partn) = find_partition_number loc _t attrna in
    if not is_inh then EXTERNAL nr partn else AR tar

  | TAR.CHAINSTART _ _ _ | TAR.REMOTE _ | TAR.CONSTITUENTS _ _ _ -> assert False
  ]
  ;

  value upconvert_edge loc _t (a,b) =
    (upconvert_tar loc _t a, upconvert_tar loc _t b)
  ;

  value add_edges tnr l1 l2 =
    l1 |> List.concat_map (fun a1 ->
      l2 |> List.map (fun a2 -> (TAR.NT tnr a1, TAR.NT tnr a2)))
  ;

  value upconverted_map_for_tnr tnr _t =
    match tnr with [
      TNR.PARENT _ ->
        _t
        |> List.mapi (fun i (inh, _) ->
            let upc_tar = EXTERNAL tnr i in
            inh |> List.map (fun attrna -> (TAR.NT tnr attrna, upc_tar)))
        |> List.concat

      | TNR.CHILD _ _ ->
        _t
        |> List.mapi (fun i (_, syn) ->
            let upc_tar = EXTERNAL tnr i in
            syn |> List.map (fun attrna -> (TAR.NT tnr attrna, upc_tar)))
        |> List.concat

    | _ -> assert False
    ]
  ;

  value partition_edges_for_tnr tnr _t =
    match tnr with [
      TNR.PARENT _ ->
      let rec addrec i = fun [
        [] -> []
      | [(inh,[])] -> []

      | [(inh,[]) :: tl] ->
        let upc_tar = EXTERNAL tnr i in
        let next_tar = EXTERNAL tnr (i+1) in
        [(upc_tar, next_tar)] @ (addrec (i+1) tl)

      | [(inh,syn)] ->
        let upc_tar = EXTERNAL tnr i in
        (syn |> List.map (fun attrna -> (upc_tar, AR (TAR.NT tnr attrna))))

      | [(inh,syn) :: tl] ->
        let upc_tar = EXTERNAL tnr i in
        let next_tar = EXTERNAL tnr (i+1) in
        (syn |> List.map (fun attrna -> (upc_tar, AR (TAR.NT tnr attrna)))) @
        (syn |> List.map (fun attrna -> (AR (TAR.NT tnr attrna), next_tar))) @
        (addrec (i+1) tl)

      ] in
      addrec 0 _t

      | TNR.CHILD _ _ ->
      let rec addrec i = fun [
        [] -> []

      | [([], syn) :: tl] ->
        let upc_tar = EXTERNAL tnr i in
        if i > 0 then
          let prev_tar = EXTERNAL tnr (i-1) in
          [(prev_tar, upc_tar)] @ (addrec (i+1) tl)
        else addrec (i+1) tl

      | [(inh,syn) :: tl] ->
        let upc_tar = EXTERNAL tnr i in
        if i > 0 then
          let prev_tar = EXTERNAL tnr (i-1) in
          (inh |> List.map (fun attrna -> (prev_tar, AR (TAR.NT tnr attrna)))) @
          (inh |> List.map (fun attrna -> (AR (TAR.NT tnr attrna), upc_tar))) @
          (addrec (i+1) tl)
        else 
          (inh |> List.map (fun attrna -> (AR (TAR.NT tnr attrna), upc_tar))) @
          (addrec (i+1) tl)

      ] in
      addrec 0 _t

    | _ -> assert False
    ]
  ;

  value upconverted_map p _t =
    p.P.typed_nodes |> LSet.toList |> List.concat_map (fun tnr -> match tnr with [
      (TNR.PARENT nt | TNR.CHILD nt _) ->
      let _t = must_lookup_t nt _t in
      upconverted_map_for_tnr tnr _t

    | TNR.PRIM _ _ -> []
    ])
  ;

  value partition_edges p _t =
    p.P.typed_nodes |> LSet.toList |> List.concat_map (fun tnr -> match tnr with [
      (TNR.PARENT nt | TNR.CHILD nt _) ->
      let _t = must_lookup_t nt _t in
      partition_edges_for_tnr tnr _t

    | TNR.PRIM _ _ -> []
    ])
  ;

  value vs_ddp p _t =
    let ddp = P.ddp p in
    let upc_map = upconverted_map p _t in
    let upc_tar tar = (match List.assoc tar upc_map with [ x -> x | exception Not_found -> AR tar ]) in
    let upc_edge (a,b) = (upc_tar a, upc_tar b) in
    let added_edges = partition_edges p _t in
    ((ddp |> List.map upc_edge)@added_edges)
    |> canon
  ;

  value split_list_at_pred pred l = do {
    assert (l <> [] ) ;
    assert (pred (List.hd l)) ;
    let rec splitrec doneacc curacc = fun [
      [] ->
      let doneacc =
        if curacc <> [] then [List.rev curacc :: doneacc] else doneacc in
      List.rev doneacc
    | [h :: t] when pred h -> splitrec [List.rev curacc :: doneacc] [h] t
    | [h :: t] -> splitrec doneacc [h :: curacc] t
    ] in
    splitrec [] [List.hd l] (List.tl l)
  }
  ;

  value visit_sequence_passes l =
    let pred = fun [ EXTERNAL (TNR.PARENT _) _ -> True | _ -> False ] in
    split_list_at_pred pred l
  ;

  value check1_vs (_t : list (list string * list string)) ((pn : PN.t), ll) = do {
    assert (ll <> []) ;
    assert (List.length _t = List.length ll) ;
    assert (ll |> List.for_all (fun [ [ EXTERNAL (TNR.PARENT _) _ :: _] -> True | _ -> False ])) ;
  }
  ;

  value compute1_vs ag _t p =
    let ddp_plus = (vs_ddp p _t) |> of_list in
    let l = TSort.fold (fun v l -> [v::l]) ddp_plus [] in
    let l = List.rev l in
    let ll = visit_sequence_passes l in do {
      check1_vs (must_lookup_t p.P.name.PN.nonterm_name _t) (p.P.name, ll) ;
      (p.P.name, ll) ;
    }
  ;

  value compute_vs ag _t =
    ag |> AG.all_productions |> List.map (compute1_vs ag _t)
  ;

  value visit_nonterminal_fname nt passnum =
    Fmt.(str "visit_%s__%d" nt passnum)
  ;

  value instruction p x =
  let loc = p.P.loc in
  match x with [
    EXTERNAL (TNR.PARENT _ | TNR.PRIM _ _) _ -> assert False
  | EXTERNAL (TNR.CHILD cnt childnum as cnr) passnum ->
    let fname = visit_nonterminal_fname cnt passnum in
    let cv = match LMap.assoc cnr p.P.rev_patt_var_to_noderef with [ x -> x | exception Not_found -> assert False ] in
    <:expr< $lid:fname$ attrs $lid:cv$ >>

  | AR (TAR.PROD pn attrna) ->
    let prodname = PN.unparse pn in
    let pnt = pn.PN.nonterm_name in
    let pntcons = Ag_tsort.node_constructor pnt in
    let attrcons = Ag_tsort.attr_constructor ~{prodname=prodname} attrna in
    <:expr< compute_attribute attrs (Node . $uid:pntcons$ parent, $uid:attrcons$) >>

  | AR (TAR.NT (TNR.PARENT pnt) attrna) ->
    let pntcons = Ag_tsort.node_constructor pnt in
    let pattrcons = Ag_tsort.attr_constructor attrna in
    <:expr< compute_attribute attrs (Node . $uid:pntcons$ parent, $uid:pattrcons$) >>

  | AR (TAR.NT (TNR.CHILD cnt childnum as cnr) attrna) ->
    let cntcons = Ag_tsort.node_constructor cnt in
    let cattrcons = Ag_tsort.attr_constructor attrna in
    let cv = match LMap.assoc cnr p.P.rev_patt_var_to_noderef with [ x -> x | exception Not_found -> assert False ] in
    <:expr< compute_attribute attrs (Node . $uid:cntcons$ $lid:cv$, $uid:cattrcons$) >>

  | _ -> assert False
  ]
  ;

  value visit_sequence1 p pnum l : MLast.case_branch =
    let loc = p.P.loc in
    let (pnt, passnum) = match l with [
      [ EXTERNAL (TNR.PARENT pnt) passnum :: _ ] -> (pnt, passnum)
    | _ -> assert False ] in
    let parent_setters = if pnum <> 0 then [] else
        p.P.typed_nodes |> LSet.toList |> List.filter_map (fun [
            TNR.CHILD cnt _ as cnr ->
            let cv = match LMap.assoc cnr p.P.rev_patt_var_to_noderef with [ x -> x | exception Not_found -> assert False ] in
             let abs_childnum = match LMap.assoc cv p.P.patt_var_to_childnum with [
               x -> x | exception Not_found -> assert False
             ] in
            Some <:expr< AttrTable . $lid:Ag_tsort.parent_setter_name cnt$
                            attrs
                            $lid:cv$
                            (Node . $uid:Ag_tsort.node_constructor pnt$ parent, $int:string_of_int abs_childnum$) >>
          | _ -> None
          ]) in
    let code = List.map (instruction p) (List.tl l) in
    (<:patt< ({ node = $p.P.patt$ } as parent) >>,
     <:vala< None >>,
     <:expr< do { $list:parent_setters@code$ } >>)
  ;

  value visitors_production (p, ll) : list (int * MLast.case_branch) =
    ll |> List.mapi (fun pnum l -> (pnum, visit_sequence1 p pnum l))
  ;

  value visitors_nonterminal _t all_vs (nt, pl) =
    let _t = must_lookup_t nt _t in
    let pn_passes = pl |> List.map (fun p ->
      let vs = match List.assoc p.P.name all_vs with [ x -> x | exception Not_found -> assert False ] in
      (p.P.name, visitors_production (p, vs))) in
    _t |> List.mapi (fun i _ ->
      let branches = pl |> List.map (fun p ->
        List.assoc i (List.assoc p.P.name pn_passes)) in
      let fname = visit_nonterminal_fname nt i in
      let loc = Ploc.dummy in
      (<:patt< $lid:fname$ >>,
       <:expr< fun attrs -> fun [ $list:branches$ ] >>,
       <:vala< [] >>)
    )
  ;

  value visitors ag _t all_vs =
    ag.AG.productions |> List.concat_map (visitors_nonterminal _t all_vs)
  ;
end
;
module VisitSequence = VS ;

value compute_visitors ag _t all_vs =
  VisitSequence.visitors ag _t all_vs
;

value compute_evaluate memo =
  let ag = memo.NTOps.ag in
  let loc = ag.AG.loc in
  let _t = compute_t memo in
  let all_vs = VS.compute_vs ag _t in
  let visitors = compute_visitors ag _t all_vs in
  let axiom = ag.AG.axiom in
  let axiom_t = must_lookup_t axiom _t in
  let result_expr =
    match List.assoc axiom memo._AS with [
      x -> x
    | exception Not_found -> assert False
    ]
    |> List.map (fun attrna ->
         <:expr< AttrTable. $lid:Ag_tsort.attr_accessor_name axiom attrna$ attrs parent >>
       ) |> (fun l -> Expr.tuple loc l) in
  let code =
    axiom_t |> List.mapi (fun i _ ->
        let fname = VS.visit_nonterminal_fname axiom i in
        <:expr< $lid:fname$ attrs parent >>
      ) in
  (visitors,
   (<:patt< evaluate >>,
    <:expr< fun parent ->
            let attrs = AttrTable.mk () in
            do { $list:code@[result_expr]$ } >>,
    <:vala< [] >>))
;
  
