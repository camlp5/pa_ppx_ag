(* camlp5o *)
(* test1_ast.ml *)

type expr =
    INT of int
  | PLUS of expr * expr
  | REF of string
  | ASSIGN of string * expr
  | SEQ of expr * expr
and prog = expr
