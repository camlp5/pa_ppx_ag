
open Ag_types ;
open AG ;
open AGOps ;
open Pa_ppx_utils ;

value nddp p =
  p
  |> ddp
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
type idp_t = list (AG.PN.t[@printer PN.pp_hum;] * (list (TAR.t[@printer TAR.pp_hum;] * TAR.t[@printer TAR.pp_hum;]))) [@@deriving show;] ;

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
      let nl = p.P.typed_nodes in
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
    |> List.map (fun p -> (p.P.name, p |> ddp |> to_list)) in
  let rec iterate arg =
    let arg' = idp_ids_step ag arg in
    if arg = arg' then arg
    else iterate arg'
  in iterate (idp0, [])
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

value compute_t memo (idp, ids) nt =
  let _as = NTOps._AS memo nt in
  let _ai = NTOps._AI memo nt in
  let _a = NTOps._A memo nt in
  let _ids = match List.assoc nt ids with [ x -> x | exception Not_found -> [] ] in
  let _ids_plus = _ids |> strg_of_list |> StrOps.transitive_closure in
  compute_all_passes (_as,_ai,_a, _ids_plus)
;

value compute_ordering memo = do {
  let (idp, ids) = idp_ids memo.NTOps.ag in
  Fmt.(pf stderr "STEP IDP=%a\nIDS=%a\n%!" pp_idp_t idp pp_ids_t ids) ;
  let _t = memo.ag |> AG.nonterminals |> List.map (fun nt -> (nt, compute_t memo (idp, ids) nt)) in
  Fmt.(pf stderr "T: %s\n%!" ([%show: list (string * list (list string * list string))] _t)) ;
  ()
}
;
