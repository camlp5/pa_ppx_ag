(* camlp5r *)
(* test1_pa.ml,v *)

open Asttools;
open MLast;
open Pcaml;
open Test1_ast ;

value prog_eoi = Grammar.Entry.create gram "prog_eoi";
(*
value prog_hashcons_eoi = Grammar.Entry.create gram "prog_hashcons_eoi";
*)
value prog_unique_eoi = Grammar.Entry.create gram "prog_unique_eoi";
value prog_attributed_eoi = Grammar.Entry.create gram "prog_attributed_eoi";

EXTEND
  GLOBAL: prog_eoi (* prog_hashcons_eoi *) prog_unique_eoi prog_attributed_eoi;

  expr: [
    [ e1 = expr ; ";" ; e2 = expr -> SEQ e1 e2 ]
  | [ e1 = expr ; "+" ; e2 = expr -> BINOP PLUS e1 e2
    | e1 = expr ; "-" ; e2 = expr -> BINOP MINUS e1 e2
    ]
  | [ e1 = expr ; "*" ; e2 = expr -> BINOP STAR e1 e2
    | e1 = expr ; "/" ; e2 = expr -> BINOP SLASH e1 e2
    | e1 = expr ; "%" ; e2 = expr -> BINOP PERCENT e1 e2
    ]
  | [ "+" ; e = expr -> UNOP UPLUS e
    | "-" ; e = expr -> UNOP UMINUS e
    ]
  | [ n = INT -> INT (int_of_string n)
    | id = LIDENT -> REF id
    | id = LIDENT ; ":=" ; e = expr -> ASSIGN id e
    | "(" ; e = expr ; ")" -> e
    ]
  ]
  ;

  prog_eoi: [ [ x = expr; EOI -> PROG x ] ];
(*
  prog_hashcons_eoi: [ [ x = prog_eoi -> Test1_migrate.ToHC.prog x ] ];
*)
  prog_unique_eoi: [ [ x = prog_eoi -> Test1_migrate.ToUnique.prog x ] ];
  prog_attributed_eoi: [ [ x = prog_eoi -> Test1_migrate.ToAttributed.prog x ] ];

END;

value pr_expr = Eprinter.make "expr";
value expr = Eprinter.apply pr_expr;

EXTEND_PRINTER
  pr_expr:
    [ "semi"
      [ SEQ e1 e2 -> pprintf pc "%p; %p" curr e1 next e2 ]
    | "add"
      [ BINOP PLUS e1 e2 -> pprintf pc "%p + %p" curr e1 next e2
      | BINOP MINUS e1 e2 -> pprintf pc "%p - %p" curr e1 next e2
      ]
    | "mul"
      [ BINOP STAR e1 e2 -> pprintf pc "%p * %p" curr e1 next e2
      | BINOP SLASH e1 e2 -> pprintf pc "%p / %p" curr e1 next e2
      | BINOP PERCENT e1 e2 -> pprintf pc "%p %% %p" curr e1 next e2
      ]
    | "unop"
      [ UNOP UPLUS e -> pprintf pc "+ %p" curr e
      | UNOP UMINUS e -> pprintf pc "- %p" curr e
      ]
    | "simple"
      [ INT n -> pprintf pc "%d" n
      | REF id -> pprintf pc "%s" id
      | ASSIGN id e -> pprintf pc "%s := %p" id expr e
      | e -> pprintf pc "(%p)" expr e
      ]
    ] ;
END;
