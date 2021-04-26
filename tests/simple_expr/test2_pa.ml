(* camlp5r *)
(* test2_pa.ml,v *)

open Asttools;
open MLast;
open Pcaml;
open Test2_ag ;

value expr = Grammar.Entry.create gram "expr";
value prog = Grammar.Entry.create gram "prog";
value prog_eoi = Grammar.Entry.create gram "prog_eoi";
value prog_attributed_eoi = Grammar.Entry.create gram "prog_attributed_eoi";

EXTEND
  GLOBAL: expr prog prog_eoi prog_attributed_eoi;

  expr: [
    "top" [ e1 = expr ; ";" ; e2 = expr -> SEQ e1 e2 ]
  | [ e1 = expr ; "+" ; e2 = expr -> BINOP loc PLUS e1 e2
    | e1 = expr ; "-" ; e2 = expr -> BINOP loc MINUS e1 e2
    ]
  | [ e1 = expr ; "*" ; e2 = expr -> BINOP loc STAR e1 e2
    | e1 = expr ; "/" ; e2 = expr -> BINOP loc SLASH e1 e2
    | e1 = expr ; "%" ; e2 = expr -> BINOP loc PERCENT e1 e2
    ]
  | [ "+" ; e = expr -> UNOP UPLUS e
    | "-" ; e = expr -> UNOP UMINUS e
    ]
  | [ n = INT -> INT (int_of_string n)
    | id = LIDENT -> REF (REF_EXPR id)
    | "(" ; e = expr ; ")" -> e
    | "let" ; id = LIDENT ; "=" ; e1 = expr LEVEL "top" ; "in" ; e2 = expr LEVEL "top" -> LET (LET_BINDING id e1 (LET_BODY e2))
    ]
  ]
  ;
  prog: [ [ x = expr; EOI -> PROG (BLOCK1 (BLOCK2 x)) ] ];

  prog_eoi: [ [ x = prog; EOI -> x ] ];
  prog_attributed_eoi: [ [ x = prog_eoi -> Test2_migrate.ToAttributed.prog x ] ];

END;

module Pr = struct
value pr_expr = Eprinter.make "expr";
value expr = Eprinter.apply pr_expr;
value pr_prog = Eprinter.make "prog";
value prog = Eprinter.apply pr_prog;

EXTEND_PRINTER
  pr_prog: [ [ PROG (BLOCK1 (BLOCK2 e)) -> pprintf pc "%p" expr e ] ] ;
  pr_expr:
    [ "semi"
      [ SEQ e1 e2 -> pprintf pc "%p; %p" curr e1 next e2 ]
    | "add"
      [ BINOP _ PLUS e1 e2 -> pprintf pc "%p + %p" curr e1 next e2
      | BINOP _ MINUS e1 e2 -> pprintf pc "%p - %p" curr e1 next e2
      ]
    | "mul"
      [ BINOP _ STAR e1 e2 -> pprintf pc "%p * %p" curr e1 next e2
      | BINOP _ SLASH e1 e2 -> pprintf pc "%p / %p" curr e1 next e2
      | BINOP _ PERCENT e1 e2 -> pprintf pc "%p %% %p" curr e1 next e2
      ]
    | "unop"
      [ UNOP UPLUS e -> pprintf pc "+ %p" curr e
      | UNOP UMINUS e -> pprintf pc "- %p" curr e
      ]
    | "simple"
      [ INT n -> pprintf pc "%d" n
      | REF (REF_EXPR id) -> pprintf pc "%s" id
      | LET (LET_BINDING id e1 (LET_BODY e2)) -> pprintf pc "let %s = %p in %p" id expr e1 expr e2
      | e -> pprintf pc "(%p)" expr e
      ]
    ] ;
END;
end
;
