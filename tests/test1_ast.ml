(* camlp5o *)
(* test1_ast.ml *)

type expr =
    INT of int
  | BINOP of binop * expr * expr
  | UNOP of unop * expr
  | REF of string
  | ASSIGN of string * expr
  | SEQ of expr * expr
and unop = UPLUS | UMINUS
and binop = PLUS | MINUS | STAR | SLASH | PERCENT
and prog = expr
