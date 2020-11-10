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
    [ e1 = expr ; "+" ; e2 = expr -> PLUS e1 e2
    ]
  | [ n = INT -> INT (int_of_string n)
    | id = LIDENT -> REF id
    | "(" ; e = expr ; ")" -> e
    ]
  ]
  ;
  prog: [ [ x = expr; EOI -> PROG x ] ];

  prog_eoi: [ [ x = prog; EOI -> x ] ];
  prog_attributed_eoi: [ [ x = prog_eoi -> Test2_migrate.ToAttributed.prog x ] ];

END;

module Pr = struct
value pr_expr = Eprinter.make "expr";
value expr = Eprinter.apply pr_expr;
value pr_prog = Eprinter.make "prog";
value prog = Eprinter.apply pr_prog;

EXTEND_PRINTER
  pr_prog: [ [ PROG e -> pprintf pc "%p" expr e ] ] ;
  pr_expr:
    [ "add"
      [ PLUS e1 e2 -> pprintf pc "%p + %p" curr e1 next e2
      ]
    | "simple"
      [ INT n -> pprintf pc "%d" n
      | REF id -> pprintf pc "%s" id
      | e -> pprintf pc "(%p)" expr e
      ]
    ] ;
END;
end
;
