(* camlp5o *)
(* test1_variants.ml *)

let preeq_list f l1 l2 =
  List.length l1 = List.length l2 &&
  List.for_all2 f l1 l2

let prehash_list f l =
  Hashtbl.hash (List.map f l)
let hash_list = prehash_list

module Hashcons = struct
  [%%import: Test1_ast.expr]
  [@@deriving hashcons {
    hashconsed_module_name = HC
  ; normal_module_name = OK
  }]
end

module Unique = struct
  [%%import: Test1_ast.expr]
  [@@deriving unique {
    uniqified_module_name = UN
  ; normal_module_name = OK
  }]
end
