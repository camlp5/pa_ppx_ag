(* camlp5o *)
(* test_ag.ml *)

type expr =
    INT of int
  | PLUS of expr * expr
  | REF of string
and prog = PROG of expr
  [@@deriving ag {
    module_name = AG
  ; attribution_model = Attributed {
    attributed_module_name = AT
  ; attributes = ()
  }
  ; storage_mode = Records
  ; axiom = prog
  ; attribute_types = {
      env = [%typ: (string * int) list]
    ; value_ = [%typ: int]
    ; result = [%typ: int]
    ; condition = [%typ: bool]
    ; rpn = [%typ: (string list [@chain])]
    ; rpn_notation = [%typ: string list]
    }
  ; node_attributes = {
      expr = [env; value_; rpn]
    ; prog = [value_; rpn_notation]
    }
  ; production_attributes = {
      expr__PLUS = [result]
    ; prog__PROG = [condition]
    }
  ; attribution = {
      expr__INT = (
        [%nterm 0].value_ := [%prim 1]
      ; [%nterm 0].rpn := (string_of_int [%prim 1]) :: [%nterm 0].rpn
      )
    ; expr__PLUS = (
        [%nterm expr.(1)].env := [%nterm expr].env
      ; [%nterm expr.(2)].env := [%nterm expr].env
      ; [%nterm expr].value_ := [%local result]
      ; [%local result] := [%nterm expr.(1)].value_ + [%nterm expr.(2)].value_
      ; [%nterm expr].rpn := "+" :: [%nterm expr.(2)].rpn
      )
    ; expr__REF = (
        [%nterm 0].value_ := List.assoc [%prim 1] [%nterm 0].env
      ; [%nterm 0].rpn := [%prim 1] :: [%nterm 0].rpn
      )
    ; prog__PROG = (
        [%nterm 1].env := [("x", 1); ("y", 2); ("z", 3); ("w", 4)]
      ; [%nterm 0].value_ := [%nterm 1].value_
      ; condition true
      ; [%chainstart expr.(1)].rpn := []
      ; [%nterm prog].rpn_notation := [%nterm expr.(1)].rpn
      )
    }
  }]