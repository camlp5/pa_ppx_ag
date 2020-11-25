(* camlp5o *)
(* test_ag.ml *)

type expr =
    INT of int
  | BINOP of binop * expr * expr
  | UNOP of unop * expr
  | REF of string
  | SEQ of expr * expr
and unop = UPLUS | UMINUS
and binop = PLUS | MINUS | STAR | SLASH | PERCENT
and block1 = BLOCK1 of block2
and block2 = BLOCK2 of expr
and prog = PROG of block1
  [@@deriving ag {
    module_name = AG
  ; attribution_model = Attributed {
    attributed_module_name = AT
  }
  ; storage_mode = Records
  ; axiom = prog
  ; attribute_types = {
      bin_oper = [%typ: int -> int -> int]
    ; inh_env = [%typ: (string * int) list]
    ; result = [%typ: int]
    ; rhs_must_be_nonzero = [%typ: bool]
    ; un_oper = [%typ: int -> int]
    ; value_ = [%typ: int]
    ; rpn = [%typ: (string list [@chain])]
    ; rpn_notation = [%typ: string list]
    ; operator_text = [%typ: string]
    }
  ; node_attributes = {
      expr = [value_; rpn]
    ; block1 = [inh_env; value_; rpn]
    ; block2 = [value_]
    ; prog = [value_; rpn_notation]
    ; binop = [bin_oper;rhs_must_be_nonzero; operator_text]
    ; unop = [un_oper; operator_text]
    }
  ; production_attributes = {
      expr__BINOP = [result]
    }
  ; attribution = {
      expr__INT = (
        [%nterm 0].value_ := [%prim 1]
      ; [%nterm 0].rpn := (string_of_int [%prim 1]) :: [%nterm 0].rpn
      )
    ; expr__BINOP = (
        [%nterm expr].value_ := [%local result]
      ; [%local result] := [%nterm binop.(1)].bin_oper [%nterm expr.(1)].value_ [%nterm expr.(2)].value_
      ; [%nterm expr].rpn := [%nterm binop.(1)].operator_text :: [%nterm expr.(2)].rpn
      ; condition "rhs must be nonzero"
          (if [%nterm binop.(1)].rhs_must_be_nonzero then
             0 <> [%nterm expr.(2)].value_
           else true)
      )
    ; expr__UNOP = (
        [%nterm expr].value_ := [%nterm unop.(1)].un_oper [%nterm expr.(1)].value_
      ; [%nterm expr].rpn := [%nterm unop.(1)].operator_text :: [%nterm expr.(1)].rpn
      )
    ; expr__REF = (
        [%nterm 0].value_ := List.assoc [%prim 1] [%remote block1.inh_env]
      ; [%nterm expr].rpn := [%prim 1] :: [%nterm expr].rpn
      )
    ; expr__SEQ = (
        [%nterm 0].value_ := [%nterm 2].value_
      ; [%nterm expr].rpn := ";" :: [%nterm expr.(2)].rpn
      )
    ; prog__PROG = (
        [%nterm 1].inh_env := [("x", 1); ("y", 2); ("z", 3); ("w", 4)]
      ; [%nterm 0].value_ := [%nterm 1].value_
      ; [%chainstart 1].rpn := []
      ; [%nterm prog].rpn_notation := List.rev [%nterm 1].rpn
      )
    ; block1__BLOCK1 = (
        [%nterm 0].value_ := [%nterm 1].value_
      )
    ; block2__BLOCK2 = (
        [%nterm 0].value_ := [%nterm 1].value_
      )
    ; unop__UPLUS = (
        [%nterm unop].un_oper := (fun x -> x)
      ; [%nterm unop].operator_text := "unary+"
      )
    ; unop__UMINUS = (
        [%nterm unop].un_oper := (fun x -> (- x))
      ; [%nterm unop].operator_text := "unary-"
      )
    ; binop__PLUS = (
        [%nterm binop].bin_oper := (+)
      ; [%nterm binop].rhs_must_be_nonzero := false
      ; [%nterm 0].operator_text := "+"
      )
    ; binop__MINUS = (
        [%nterm binop].bin_oper := (-)
      ; [%nterm binop].rhs_must_be_nonzero := false
      ; [%nterm 0].operator_text := "-"
      )
    ; binop__STAR = (
        [%nterm binop].bin_oper := (fun a b -> a*b)
      ; [%nterm binop].rhs_must_be_nonzero := false
      ; [%nterm 0].operator_text := "*"
      )
    ; binop__SLASH = (
        [%nterm binop].bin_oper := (fun a b -> if b = 0 then 0 else a / b)
      ; [%nterm binop].rhs_must_be_nonzero := true
      ; [%nterm 0].operator_text := "/"
      )
    ; binop__PERCENT = (
        [%nterm binop].bin_oper := (mod)
      ; [%nterm binop].rhs_must_be_nonzero := true
      ; [%nterm 0].operator_text := "%"
      )
    }
  }]
