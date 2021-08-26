(**************************************************************************)
(*                                                                        *)
(*  Ocamlgraph: a generic graph library for OCaml                         *)
(*  Copyright (C) 2004-2010                                               *)
(*  Sylvain Conchon, Jean-Christophe Filliatre and Julien Signoles        *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Graph ;

module Make(G: Sig.I with type E.label = unit) = struct

  module S = Set.Make(G.V) ;
  module HT = Hashtbl.Make(G.V) ;
  module Scc = Components.Make(G) ;

  value fold f g acc = do {
    (* verify no cycles *)
    if g |> Scc.scc_list |> List.exists (fun [ [_ ; _ :: _] -> True | _ -> False ]) then
      failwith "ImperativeTopological.fold: graph has cycles: unsupported by imperative tsort"
    else ();

    let indegree = HT.create 23 in
    let update_indegree s d =
      if G.V.equal s d then failwith "ImperativeTopological.fold: graph has self-loop, unsupported: "
      else match (HT.find_opt indegree s, HT.find_opt indegree d) with [
             (None, None) -> do {
               HT.add indegree s 0 ;
               HT.add indegree d 1
             }
           | (Some _, None) ->
             HT.add indegree d 1
           | (None, Some n) -> do {
                HT.add indegree s 0 ;
                HT.replace indegree d (n+1)
              }
           | (Some _, Some n) ->
              HT.replace indegree d (n+1) ] in

    G.iter_edges update_indegree g ;
    let todo = ref S.empty in
    let mem_todo v = S.mem v todo.val in
    let add_todo v = todo.val := S.add v todo.val in
    let remove_todo v = todo.val := S.remove v todo.val in
    G.iter_vertex (fun v ->
        if HT.find indegree v = 0 then
          add_todo v
        else ()) g ;

    let visited = ref S.empty in
    let mem_visited v = S.mem v visited.val in
    let add_visited v = visited.val := S.add v visited.val in

    let add_edge (i, j) = do {
      if mem_visited j then
        failwith "ImperativeTopological.fold: cannot add edges to an already-visited node"
      else () ;
      if mem_todo j then remove_todo j else ();
      G.add_edge g i j ;
      update_indegree i j ;
      if HT.find indegree j = 0 then
        add_todo j
      else ()
    }
    in

    let rec walk acc =
      match S.choose_opt todo.val with [
        None -> acc
      | Some i -> do {
          if mem_visited i then
            failwith "ImperativeTopological.fold: graph has an unexpected loop"
          else () ;
          remove_todo i ;
          add_visited i ;
          let acc = f add_edge i acc in
          G.fold_succ (fun j acc ->
              let d = HT.find indegree j in do {
                assert (d > 0) ;
                HT.replace indegree j (d-1) ;
                if d = 1 then
                  add_todo j
                else () ;
                acc
              }) g i acc ;
          walk acc
        } ]
    in
    walk acc
  }
  ;
  value iter f g = fold (fun add_edge v () -> f add_edge v) g () ;

end
;
                        
