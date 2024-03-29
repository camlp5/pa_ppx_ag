(* camlp5o *)
(* test_ag.ml *)

type loc = Ploc.t
let global_ref = ref [] ;;

module T = struct
type expr =
    INT of int
  | BINOP of loc * binop * expr * expr
  | UNOP of unop * expr
  | REF of ref_expr
  | SEQ of expr * expr
  | LET of let_expr
and let_expr = LET_BINDING of string * expr * let_body
and let_body = LET_BODY of expr
and ref_expr = REF_EXPR of string
and unop = UPLUS | UMINUS
and binop = PLUS | MINUS | STAR | SLASH | PERCENT
and block1 = BLOCK1 of block2
and block2 = BLOCK2 of expr
and prog = PROG of block1
end

type expr = T.expr =
    INT of int
  | BINOP of loc * binop * expr * expr
  | UNOP of unop * expr
  | REF of ref_expr
  | SEQ of expr * expr
  | LET of let_expr
and let_expr = T.let_expr = LET_BINDING of string * expr * let_body
and let_body = T.let_body = LET_BODY of expr
and ref_expr = T.ref_expr = REF_EXPR of string
and unop = T.unop = UPLUS | UMINUS
and binop = T.binop = PLUS | MINUS | STAR | SLASH | PERCENT
and block1 = T.block1 = BLOCK1 of block2
and block2 = T.block2 = BLOCK2 of expr
and prog = T.prog = PROG of block1
  [@@deriving ag {
    module_name = AG
  ; attribution_model = {
    normal_module_name = OK
  ; attributed_module_name = AT
  }
  ; with_migrate = true
  ; with_q_ast = true
  ; primitive_types = [loc]
  ; axiom = prog
  ; attribute_types = {
      bin_oper = [%typ: int -> int -> int]
    ; env = [%typ: (string * int) list]
    ; result = [%typ: int]
    ; rhs_must_be_nonzero = [%typ: bool]
    ; un_oper = [%typ: int -> int]
    ; value_ = [%typ: int]
    ; rpn = [%typ: ((string list) [@chain])]
    ; rpn_notation = [%typ: string list]
    ; operator_text = [%typ: string]
    ; freevars = [%typ: string list]
    }
  ; node_attributes = {
      expr = [value_; rpn]
    ; let_expr = [value_; rpn; freevars]
    ; let_body = [env; value_; rpn]
    ; ref_expr = [value_; rpn; freevars]
    ; block1 = [env; value_; rpn]
    ; block2 = [value_]
    ; prog = [value_; rpn_notation; freevars]
    ; binop = [bin_oper;rhs_must_be_nonzero; operator_text]
    ; unop = [un_oper; operator_text]
    }
  ; production_attributes = {
      expr__BINOP = [result]
    }
  ; attribution = {
      let_expr__LET_BINDING = (
        [%nterm let_expr].value_ := [%nterm let_body.(1)].value_
      ; [%nterm let_body.(1)].rpn := (Printf.sprintf "bind %s" [%prim 1]) :: [%nterm expr.(1)].rpn
      ; [%nterm let_body.(1)].env := ([%prim 1], [%nterm expr.(1)].value_) :: [%remote (block1.env, let_body.env)]
      ; [%nterm 0].freevars :=
          Std.union
            [%constituents { nodes = [%nterm 2]; attributes = [ref_expr.freevars; let_expr.freevars]}]
            (Std.except [%prim 1] [%constituents { nodes = [ [%nterm 3] ]; attributes = [ref_expr.freevars; let_expr.freevars]}])
      )
    ; let_body__LET_BODY = (
          [%nterm 0].value_ := [%nterm 1].value_ ;
          [%nterm 0].rpn := [%nterm 1].rpn ;
      )
    ; expr__INT = (
        [%nterm 0].value_ := [%prim 1]
      ; [%nterm 0].rpn := (string_of_int [%prim 1]) :: [%nterm 0].rpn
      )
    ; expr__BINOP = (
        [%nterm expr].value_ := [%local result]
      ; [%local result] := [%nterm binop.(1)].bin_oper [%nterm expr.(1)].value_ [%nterm expr.(2)].value_
      ; [%nterm expr].rpn := [%nterm binop.(1)].operator_text :: [%nterm expr.(2)].rpn
      ; condition Fmt.(str "%srhs must be nonzero" (Ploc.string_of_location [%prim 1]))
          (if [%nterm binop.(1)].rhs_must_be_nonzero then
             0 <> [%nterm expr.(2)].value_
           else true)
      )
    ; expr__LET = (
        [%nterm expr].value_ := [%nterm let_expr.(1)].value_
      ; [%nterm expr].rpn := [%nterm let_expr.(1)].rpn
      )
    ; expr__UNOP = (
        [%nterm expr].value_ := [%nterm unop.(1)].un_oper [%nterm expr.(1)].value_
      ; [%nterm expr].rpn := [%nterm unop.(1)].operator_text :: [%nterm expr.(1)].rpn
      )
    ; expr__REF = (
        [%nterm 0].value_ := [%nterm 1].value_
      )
    ; ref_expr__REF_EXPR = (
        [%nterm 0].value_ := List.assoc [%prim 1] [%remote (block1.env, let_body.env)]
      ; [%nterm 0].rpn := [%prim 1] :: [%nterm 0].rpn
      ; [%nterm 0].freevars := [[%prim 1]]
      )
    ; expr__SEQ = (
        [%nterm 0].value_ := [%nterm 2].value_
      ; [%nterm expr].rpn := ";" :: [%nterm expr.(2)].rpn
      )
    ; prog__PROG = (
        [%nterm 1].env := [("x", 1); ("y", 2); ("z", 3); ("w", 4)]
      ; [%nterm 0].value_ := [%nterm 1].value_
      ; [%chainstart 1].rpn := []
      ; [%nterm prog].rpn_notation := List.rev [%nterm 1].rpn
      ; [%nterm 0].freevars := [%constituents { nodes = [ [%nterm 1] ]; attributes = [ref_expr.freevars; let_expr.freevars]}]
      ; Std.push global_ref "before"
      ; let _ = [%nterm 0].value_ in Std.push global_ref "after"
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
