(* camlp5o *)
(* test_ag.ml *)

[%%import: Test1_variants.Unique.UN.expr]
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
      expr__INT = (
        [%nterm 0].syn_env := [%nterm 0].inh_env ;
        [%nterm 0].value_ := [%prim 1].intval
      )
    ; expr__PLUS = (
        [%nterm 1].inh_env := [%nterm 0].inh_env ;
        [%nterm 2].inh_env := [%nterm 1].syn_env ;
        [%nterm 0].syn_env := [%nterm 2].syn_env ;
        [%nterm 0].value_ := [%nterm 1].value_ + [%nterm 2].value_
      )
    ; expr__REF = (
        [%nterm 0].syn_env := [%nterm 0].inh_env ;
        [%nterm 0].value_ := List.assoc [%prim 1].stringval [%nterm 0].inh_env
      )
    ; expr__ASSIGN = (
        [%nterm 0].syn_env := ([%prim 1].stringval, [%nterm expr.(1)].value_) :: [%nterm expr.(1)].syn_env ;
        [%nterm expr.(1)].inh_env := [%nterm 0].inh_env ;
        [%nterm 0].value_ := [%nterm expr.(1)].value_
      )
    ; expr__SEQ = (
        [%nterm 1].inh_env := [%nterm 0].inh_env ;
        [%nterm 2].inh_env := [%nterm 1].syn_env ;
        [%nterm 0].syn_env := [%nterm 2].syn_env ;
        [%nterm 0].value_ := [%nterm 2].value_
      )
    ; prog = (
        [%nterm 1].inh_env := [] ;
        [%nterm 0].value_ := [%nterm 1].value_
      )
    }
  }]
