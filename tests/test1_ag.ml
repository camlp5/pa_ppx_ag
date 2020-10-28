(* camlp5o *)
(* test_ag.ml *)

[%%import: Test1_variants.Unique.expr]
  [@@deriving ag {
    module_name = AG
  ; attributes = {
      expr = {
        inh_env = [%typ: (string * int) list]
      ; syn_env = [%typ: (string * int) list]
      ; value_ = [%typ: int]
      }
    ; prog = {
        value_ = [%typ: int]
      }
    }
  ; attribution = {
      expr_INT = (
        [%attr 0].syn_env := [%attr 0].inh_env ;
        [%attr 0].value_ := [%prim 1]
      )
    ; expr_PLUS = (
        [%attr 1].inh_env := [%attr 0].inh_env ;
        [%attr 2].inh_env := [%attr 1].syn_env ;
        [%attr 0].syn_env := [%attr 2].syn_env ;
        [%attr 0].value_ := [%attr 1].value_ + [%attr 2].value_
      )
    ; prog = (
        [%attr 1].inh_env := [] ;
        [%attr 0].value_ := [%attr 1].value_
      )
    }
  }]
