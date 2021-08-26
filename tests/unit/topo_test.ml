open OUnit2 ;

module StringVertex = struct
  include String ;
  value hash = Hashtbl.hash ;
end ;

module G = Graph.Imperative.Digraph.ConcreteBidirectional(StringVertex) ;
module TSort = Graph.Topological.Make(G) ;
module ITSort = ImperativeTopological.Make(G) ;

value test0 ctxt =
  let edges = [("a","b"); ("b","c"); ("b","d"); ("c","e"); ("d","e")] in
  let g = G.create () in do {
    edges |> List.iter (fun (a,b) ->
                 G.add_edge g a b) ;
    let l = TSort.fold (fun v acc -> [v::acc]) g [] in
    assert_equal ~{printer=[%show: (list string)]}  ["e"; "d"; "c"; "b"; "a"] l
  }
;

value test1 ctxt =
  let edges = [("a","b"); ("b","c"); ("b","d"); ("c","e"); ("d","e")] in
  let g = G.create () in do {
    edges |> List.iter (fun (a,b) ->
                 G.add_edge g a b) ;
    let l = ITSort.fold (fun add_edge v acc -> [v::acc]) g [] in
    assert_equal ~{printer=[%show: (list string)]}  ["e"; "d"; "c"; "b"; "a"] l
  }
;

value added_edges = [("b",[("c","c1");("c1","c2");("c1","d")])] ;

value visit g add_edge v acc = do {
    match List.assoc v added_edges with [
        el -> List.iter add_edge el
      | exception Not_found -> ()
      ] ;
    [v :: acc]
  } ;

value test2 ctxt =
  let edges = [("a","b"); ("b","c"); ("b","d"); ("c","e"); ("d","e")] in
  let added_edges = [("b",[("c","c1");("c1","c2");("c1","d")])] in
  let visit add_edge v acc = do {
    match List.assoc v added_edges with [
        el -> List.iter add_edge el
      | exception Not_found -> ()
      ] ;
    [v :: acc]
  } in
  let g = G.create () in do {
    edges |> List.iter (fun (a,b) ->
                 G.add_edge g a b) ;
    let l = ITSort.fold visit g [] in
    assert_equal ~printer:[%show: (list string)]  ["e"; "d"; "c2"; "c1"; "c"; "b"; "a"] l
  }
;

value suite = "ImperativeTopological sort test" >::: [
  "test0"           >:: test1
  ; "test1"           >:: test1
  ; "test2"           >:: test2
  ]
;

value _ = 
if not Sys.interactive.val then
  run_test_tt_main suite
else ()
;
