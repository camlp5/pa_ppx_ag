(* camlp5o *)
(* test1_variants.ml *)

let preeq_list f l1 l2 =
  List.length l1 = List.length l2 &&
  List.for_all2 f l1 l2

let prehash_list f l =
  Hashtbl.hash (List.map f l)
let hash_list = prehash_list

module Hashcons = struct
  module _ = Test1_ast
  [%%import: Test1_ast.expr]
  [@@deriving hashcons {
    hashconsed_module_name = HC
  ; normal_module_name = OK
  }]
end

module Unique = struct
  module _ = Test1_ast
  [%%import: Test1_ast.expr]
  [@@deriving unique {
    uniqified_module_name = UN
  ; normal_module_name = OK
  }]
end

module Attributed = struct
  module _ = Test1_ast
  [%%import: Test1_ast.expr]
  [@@deriving attributed {
    attributed_module_name = AT
  ; normal_module_name = OK
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
  }]
end
