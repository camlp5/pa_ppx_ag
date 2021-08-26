module T =
  struct
    type one = ONE
    and root = ROOT
  end;;
type one = T.one = ONE
and root =
  T.root = ROOT[@@deriving ag
    {optional = true; module_name = AG;
     attribution_model =
       {attributed_module_name = AT; normal_module_name = OK};
     primitive_types = []; axiom = root;
     attribute_types = {localn = [%typ: one]; n = [%typ: int]};
     node_attributes = {one = [n]; root = [n]};
     production_attributes = {root__ROOT = [localn]};
     attribution =
       {one__ONE = [%nterm 0].n <- 1;
        root__ROOT =
          begin
            [%nterm 0].n <- [%nta localn.n];
            [%local localn] :=
              Migrate.ToAttributed.(migrate_one (make_dt ())) ONE
          end}}];;
open OUnit2;;
let test1_topological ctxt =
  let ok = OK.ROOT in
  let at = AG.Migrate.ToAttributed.(migrate_root (make_dt ())) ok in
  assert_equal 1 (AG.Topological.evaluate at);;
let test1_ordered ctxt =
  let ok = OK.ROOT in
  let at = AG.Migrate.ToAttributed.(migrate_root (make_dt ())) ok in
  assert_equal 1 (AG.Ordered.evaluate at);;
let suite =
  "simple_hoag" >:::
    ["test1_topological" >:: test1_topological;
     "test1_ordered" >:: test1_ordered];;
let _ = if not !(Sys.interactive) then run_test_tt_main suite;;
