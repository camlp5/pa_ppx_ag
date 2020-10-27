(* camlp5o *)
(* test1_ast.ml *)

type expr =
    INT of int
  | PLUS of expr * expr
  | VAR of string
  | ASSIGN of string * expr
  | SEQ of expr list

