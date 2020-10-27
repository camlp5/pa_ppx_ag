(* camlp5o *)
(* test_ag.ml *)

[%%import: Test1_variants.Unique.expr]
  [@@deriving ag {
    module_name = AG
  }]
