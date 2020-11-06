(* camlp5o *)
(* test_ag.ml *)

module HT = struct
module _ = Test1_variants
[%%import: Test1_variants.Unique.UN.expr]
  [@@deriving ag {
    module_name = AG
  ; storage_mode = Hashtables
  ; axiom = prog
  ; attributes = {
      expr = {
        inh_env = [%typ: (string * int) list]
      ; syn_env = [%typ: (string * int) list]
      ; value_ = [%typ: int]
      }
    ; expr__BINOP = {
        condition = [%typ: bool]
      }
    ; prog = {
        value_ = [%typ: int]
      }
    ; prog__PROG = {
        condition = [%typ: bool]
      }
    ; binop = {
        oper = [%typ: int -> int -> int]
      ; rhs_must_be_nonzero = [%typ: bool]
      }
    ; unop = {
        oper = [%typ: int -> int]
      }
    }
  ; attribution = {
      expr__INT = (
        [%nterm 0].syn_env := [%nterm 0].inh_env ;
        [%nterm 0].value_ := [%prim 1]
      )
    ; expr__BINOP = (
        [%nterm expr.(1)].inh_env := [%nterm expr].inh_env ;
        [%nterm expr.(2)].inh_env := [%nterm expr.(1)].syn_env ;
        [%nterm expr].syn_env := [%nterm expr.(2)].syn_env ;
        [%nterm expr].value_ := [%nterm binop.(1)].oper [%nterm expr.(1)].value_ [%nterm expr.(2)].value_ ;
        condition "rhs must be nonzero"
          (if [%nterm binop.(1)].rhs_must_be_nonzero then
             0 <> [%nterm expr.(2)].value_
           else true)
      )
    ; expr__UNOP = (
        [%nterm expr.(1)].inh_env := [%nterm expr].inh_env ;
        [%nterm expr].syn_env := [%nterm expr.(1)].syn_env ;
        [%nterm expr].value_ := [%nterm unop.(1)].oper [%nterm expr.(1)].value_
      )
    ; expr__REF = (
        [%nterm 0].syn_env := [%nterm 0].inh_env ;
        [%nterm 0].value_ := List.assoc [%prim 1] [%nterm 0].inh_env
      )
    ; expr__ASSIGN = (
        [%nterm 0].syn_env := ([%prim 1], [%nterm expr.(1)].value_) :: [%nterm expr.(1)].syn_env ;
        [%nterm expr.(1)].inh_env := [%nterm 0].inh_env ;
        [%nterm 0].value_ := [%nterm expr.(1)].value_
      )
    ; expr__SEQ = (
        [%nterm 1].inh_env := [%nterm 0].inh_env ;
        [%nterm 2].inh_env := [%nterm 1].syn_env ;
        [%nterm 0].syn_env := [%nterm 2].syn_env ;
        [%nterm 0].value_ := [%nterm 2].value_
      )
    ; prog__PROG = (
        [%nterm 1].inh_env := [] ;
        [%nterm 0].value_ := [%nterm 1].value_
      )
    ; unop__UPLUS = (
        [%nterm unop].oper := fun x -> x
      )
    ; unop__UMINUS = (
        [%nterm unop].oper := fun x -> (- x)
      )
    ; binop__PLUS = (
        [%nterm binop].oper := (+)
      ; [%nterm binop].rhs_must_be_nonzero := false
      )
    ; binop__MINUS = (
        [%nterm binop].oper := (-)
      ; [%nterm binop].rhs_must_be_nonzero := false
      )
    ; binop__STAR = (
        [%nterm binop].oper := (fun a b -> a*b)
      ; [%nterm binop].rhs_must_be_nonzero := false
      )
    ; binop__SLASH = (
        [%nterm binop].oper := (fun a b -> if b = 0 then 0 else a / b)
      ; [%nterm binop].rhs_must_be_nonzero := true
      )
    ; binop__PERCENT = (
        [%nterm binop].oper := (mod)
      ; [%nterm binop].rhs_must_be_nonzero := true
      )
    }
  }]
end

module REC = struct
module _ = Test1_variants
[%%import: Test1_variants.Attributed.AT.expr]
  [@@deriving ag {
    module_name = AG
  ; storage_mode = Records
  ; axiom = prog
  ; attributes = {
      expr = {
        inh_env = [%typ: (string * int) list]
      ; syn_env = [%typ: (string * int) list]
      ; value_ = [%typ: int]
      }
    ; expr__BINOP = {
        condition = [%typ: bool]
      }
    ; prog = {
        value_ = [%typ: int]
      }
    ; prog__PROG = {
        condition = [%typ: bool]
      }
    ; binop = {
        oper = [%typ: int -> int -> int]
      ; rhs_must_be_nonzero = [%typ: bool]
      }
    ; unop = {
        oper = [%typ: int -> int]
      }
    }
  ; attribution = {
      expr__INT = (
        [%nterm 0].syn_env := [%nterm 0].inh_env ;
        [%nterm 0].value_ := [%prim 1]
      )
    ; expr__BINOP = (
        [%nterm expr.(1)].inh_env := [%nterm expr].inh_env ;
        [%nterm expr.(2)].inh_env := [%nterm expr.(1)].syn_env ;
        [%nterm expr].syn_env := [%nterm expr.(2)].syn_env ;
        [%nterm expr].value_ := [%nterm binop.(1)].oper [%nterm expr.(1)].value_ [%nterm expr.(2)].value_ ;
        condition "rhs must be nonzero"
          (if [%nterm binop.(1)].rhs_must_be_nonzero then
             0 <> [%nterm expr.(2)].value_
           else true)
      )
    ; expr__UNOP = (
        [%nterm expr.(1)].inh_env := [%nterm expr].inh_env ;
        [%nterm expr].syn_env := [%nterm expr.(1)].syn_env ;
        [%nterm expr].value_ := [%nterm unop.(1)].oper [%nterm expr.(1)].value_
      )
    ; expr__REF = (
        [%nterm 0].syn_env := [%nterm 0].inh_env ;
        [%nterm 0].value_ := List.assoc [%prim 1] [%nterm 0].inh_env
      )
    ; expr__ASSIGN = (
        [%nterm 0].syn_env := ([%prim 1], [%nterm expr.(1)].value_) :: [%nterm expr.(1)].syn_env ;
        [%nterm expr.(1)].inh_env := [%nterm 0].inh_env ;
        [%nterm 0].value_ := [%nterm expr.(1)].value_
      )
    ; expr__SEQ = (
        [%nterm 1].inh_env := [%nterm 0].inh_env ;
        [%nterm 2].inh_env := [%nterm 1].syn_env ;
        [%nterm 0].syn_env := [%nterm 2].syn_env ;
        [%nterm 0].value_ := [%nterm 2].value_
      )
    ; prog__PROG = (
        [%nterm 1].inh_env := [] ;
        [%nterm 0].value_ := [%nterm 1].value_
      )
    ; unop__UPLUS = (
        [%nterm unop].oper := fun x -> x
      )
    ; unop__UMINUS = (
        [%nterm unop].oper := fun x -> (- x)
      )
    ; binop__PLUS = (
        [%nterm binop].oper := (+)
      ; [%nterm binop].rhs_must_be_nonzero := false
      )
    ; binop__MINUS = (
        [%nterm binop].oper := (-)
      ; [%nterm binop].rhs_must_be_nonzero := false
      )
    ; binop__STAR = (
        [%nterm binop].oper := (fun a b -> a*b)
      ; [%nterm binop].rhs_must_be_nonzero := false
      )
    ; binop__SLASH = (
        [%nterm binop].oper := (fun a b -> if b = 0 then 0 else a / b)
      ; [%nterm binop].rhs_must_be_nonzero := true
      )
    ; binop__PERCENT = (
        [%nterm binop].oper := (mod)
      ; [%nterm binop].rhs_must_be_nonzero := true
      )
    }
  }]
end
