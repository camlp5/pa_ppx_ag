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

EXTEND
  GLOBAL: prog_eoi (* prog_hashcons_eoi *) prog_unique_eoi;

  test1: [
    [ e1 = test1 ; ";" ; e2 = test1 -> SEQ e1 e2 ]
  | [ e1 = test1 ; "+" ; e2 = test1 -> PLUS e1 e2 ]
  | [ n = INT -> INT (int_of_string n)
    | id = LIDENT -> REF id
    | id = LIDENT ; ":=" ; e = test1 -> ASSIGN id e
    | "(" ; e = test1 ; ")" -> e
    ]
  ]
  ;

  prog_eoi: [ [ x = test1; EOI -> x ] ];
(*
  prog_hashcons_eoi: [ [ x = test1; EOI -> Test1_migrate.ToHC.prog x ] ];
*)
  prog_unique_eoi: [ [ x = test1; EOI -> Test1_migrate.ToUnique.prog x ] ];

END;
