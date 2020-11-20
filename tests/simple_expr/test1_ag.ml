(* camlp5o *)
(* test_ag.ml *)

module UN = struct
module _ = Test1_ast
[%%import: Test1_ast.expr]
  [@@deriving ag {
    module_name = AG
  ; attribution_model = Unique {
        optional = false
      ; uniqified_module_name = UN
      ; normal_module_name = OK
      }
  ; storage_mode = Hashtables
  ; axiom = prog
  ; attribute_types = {
      bin_oper = [%typ: int -> int -> int]
    ; condition = [%typ: bool]
    ; inh_env = [%typ: (string * int) list]
    ; result = [%typ: int]
    ; rhs_must_be_nonzero = [%typ: bool]
    ; syn_env = [%typ: (string * int) list]
    ; un_oper = [%typ: int -> int]
    ; value_ = [%typ: int]
    }
  ; node_attributes = {
      expr = [inh_env; syn_env; value_]
    ; prog = [value_]
    ; binop = [bin_oper;rhs_must_be_nonzero]
    ; unop = [un_oper]
    }
  ; production_attributes = {
      expr__BINOP = [condition; result]
    ; prog__PROG = [condition]
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
        [%nterm expr].value_ := [%local result] ;
        [%local result] := [%nterm binop.(1)].bin_oper [%nterm expr.(1)].value_ [%nterm expr.(2)].value_ ;
        condition "rhs must be nonzero"
          (if [%nterm binop.(1)].rhs_must_be_nonzero then
             0 <> [%nterm expr.(2)].value_
           else true)
      )
    ; expr__UNOP = (
        [%nterm expr.(1)].inh_env := [%nterm expr].inh_env ;
        [%nterm expr].syn_env := [%nterm expr.(1)].syn_env ;
        [%nterm expr].value_ := [%nterm unop.(1)].un_oper [%nterm expr.(1)].value_
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
        [%nterm unop].un_oper := fun x -> x
      )
    ; unop__UMINUS = (
        [%nterm unop].un_oper := fun x -> (- x)
      )
    ; binop__PLUS = (
        [%nterm binop].bin_oper := (+)
      ; [%nterm binop].rhs_must_be_nonzero := false
      )
    ; binop__MINUS = (
        [%nterm binop].bin_oper := (-)
      ; [%nterm binop].rhs_must_be_nonzero := false
      )
    ; binop__STAR = (
        [%nterm binop].bin_oper := (fun a b -> a*b)
      ; [%nterm binop].rhs_must_be_nonzero := false
      )
    ; binop__SLASH = (
        [%nterm binop].bin_oper := (fun a b -> if b = 0 then 0 else a / b)
      ; [%nterm binop].rhs_must_be_nonzero := true
      )
    ; binop__PERCENT = (
        [%nterm binop].bin_oper := (mod)
      ; [%nterm binop].rhs_must_be_nonzero := true
      )
    }
  }]
end

module REC = struct
module _ = Test1_ast
[%%import: Test1_ast.expr]
  [@@deriving ag {
    module_name = AG
  ; attribution_model = Attributed {
    attributed_module_name = AT
  ; normal_module_name = OK
  ; attributes = ()
  }
  ; storage_mode = Records
  ; axiom = prog
  ; attribute_types = {
      bin_oper = [%typ: int -> int -> int]
    ; condition = [%typ: bool]
    ; inh_env = [%typ: (string * int) list]
    ; result = [%typ: int]
    ; rhs_must_be_nonzero = [%typ: bool]
    ; syn_env = [%typ: (string * int) list]
    ; un_oper = [%typ: int -> int]
    ; value_ = [%typ: int]
    }
  ; node_attributes = {
      expr = [inh_env; syn_env; value_]
    ; prog = [value_]
    ; binop = [bin_oper;rhs_must_be_nonzero]
    ; unop = [un_oper]
    }
  ; production_attributes = {
      expr__BINOP = [condition; result]
    ; prog__PROG = [condition]
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
        [%nterm expr].value_ := [%local result] ;
        [%local result] := [%nterm binop.(1)].bin_oper [%nterm expr.(1)].value_ [%nterm expr.(2)].value_ ;
        condition "rhs must be nonzero"
          (if [%nterm binop.(1)].rhs_must_be_nonzero then
             0 <> [%nterm expr.(2)].value_
           else true)
      )
    ; expr__UNOP = (
        [%nterm expr.(1)].inh_env := [%nterm expr].inh_env ;
        [%nterm expr].syn_env := [%nterm expr.(1)].syn_env ;
        [%nterm expr].value_ := [%nterm unop.(1)].un_oper [%nterm expr.(1)].value_
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
        [%nterm unop].un_oper := fun x -> x
      )
    ; unop__UMINUS = (
        [%nterm unop].un_oper := fun x -> (- x)
      )
    ; binop__PLUS = (
        [%nterm binop].bin_oper := (+)
      ; [%nterm binop].rhs_must_be_nonzero := false
      )
    ; binop__MINUS = (
        [%nterm binop].bin_oper := (-)
      ; [%nterm binop].rhs_must_be_nonzero := false
      )
    ; binop__STAR = (
        [%nterm binop].bin_oper := (fun a b -> a*b)
      ; [%nterm binop].rhs_must_be_nonzero := false
      )
    ; binop__SLASH = (
        [%nterm binop].bin_oper := (fun a b -> if b = 0 then 0 else a / b)
      ; [%nterm binop].rhs_must_be_nonzero := true
      )
    ; binop__PERCENT = (
        [%nterm binop].bin_oper := (mod)
      ; [%nterm binop].rhs_must_be_nonzero := true
      )
    }
  }]
end
