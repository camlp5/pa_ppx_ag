(* camlp5r *)
(* Lax_pa.ml,v *)

open Asttools;
open MLast;
open Lax_ast ;

value gram = Grammar.gcreate (Plexer.gmake ());

value block = Grammar.Entry.create gram "block" ;
value bound_pair = Grammar.Entry.create gram "bound_pair" ;
value clause = Grammar.Entry.create gram "clause" ;
value declaration = Grammar.Entry.create gram "declaration" ;
value expression = Grammar.Entry.create gram "expression";
value iteration = Grammar.Entry.create gram "iteration" ;
value jump = Grammar.Entry.create gram "jump" ;
value loop = Grammar.Entry.create gram "loop" ;
value procedure = Grammar.Entry.create gram "procedure" ;
value program = Grammar.Entry.create gram "program" ;
value record_type = Grammar.Entry.create gram "record_type" ;
value statement = Grammar.Entry.create gram "statement" ;
value statement_list = Grammar.Entry.create gram "statement_list" ;
value type_specification = Grammar.Entry.create gram "type_specification" ;

open Lax_ast ;

EXTEND
  GLOBAL:
  block
  bound_pair
  clause
  declaration
  expression 
  iteration
  jump
  loop
  procedure
  program
  record_type
  statement
  statement_list
  type_specification
  ;

  program: [ [ x = block -> x ] ] ;
  block: [
    [ "declare" ; dl = LIST0 declaration SEP ";" ; "begin" ; sl = LIST1 statement SEP ";" ; "end" -> (dl, sl)
    | "begin" ; sl = LIST1 statement SEP ";" ; "end" -> ([], sl)
    ]
  ]
  ;
  statement_list: [ [ sl = LIST1 statement SEP ";" -> sl ] ] ;
  statement: [
    [ ldl = LIST0 [ id = LIDENT ; ":" -> id ] ; st = bare_statement -> (ldl, st) ]
  ]
  ;
  bare_statement: [
    [ e = expression -> STMT_EXPR loc e
    | i = iteration -> STMT_ITER loc i
    | j = jump -> STMT_JUMP loc j
    ]
  ]
  ;
  iteration: [
    [ "while" ; e = expression ; l = loop -> ITER_WHILE loc e l
    | "for" ; id = LIDENT ; "from" ; e1 = expression ; "to" ; e2 = expression ; l = loop -> ITER_FOR loc id e1 e2 l
    ]
  ]
  ;
  loop: [ [ "do" ; l = statement_list ; "end" -> l ] ] ;
  jump: [ [ "goto" ; id = LIDENT -> id ] ] ;

  declaration: [
    [ id = LIDENT ; rhs = variable_declaration_rhs -> DECL_VARIABLE loc id rhs
    | id = LIDENT ; "is" ; e = expression ; ":" ; ts = type_specification -> DECL_IDENTITY loc id e ts
    | "procedure" ; id = LIDENT ; p = procedure -> DECL_PROCEDURE loc id p
    | "type" ; id = LIDENT ; "=" ; ts = record_type -> DECL_TYPE loc id ts
    ]
  ]
  ;
  variable_declaration_rhs: [
    [ ":" ; ts = type_specification -> VAR_TYPE loc ts
    | ":" ; "array" ; "[" ; bpl = LIST1 bound_pair SEP "," ; "]" ; "of" ; ts = type_specification ->
      VAR_ARRAY loc bpl ts
    ]
  ]
  ;
  bound_pair: [
    [ e1 = expression ; ":" ; e2 = expression -> (e1, e2) ]
  ]
  ;
  record_type: [
    [ "record" ; fl = LIST1 [ id = LIDENT ; ":" ; ts = type_specification -> (id, ts) ] SEP ";" ; "end" -> fl ]
  ]
  ;
  type_specification: [
    [ id = LIDENT -> TYPE_ID loc id
    | pty = prim_type -> TYPE_PRIM loc pty
    | "ref" ; ts = type_specification -> TYPE_REF loc ts
    | "ref" ; aty = array_type ->  TYPE_REFARRAY loc aty
    | "procedure" ; pl = OPT [ "(" ; pl = LIST1 type_specification SEP "," ; ")" -> pl ] ; rty = OPT type_specification ->
      let pl = match pl with [ None -> [] | Some pl -> pl ] in
      TYPE_PROC loc (pl, rty)
    ]
  ]
  ;
  array_type: [
    [ "array" ; "[" ; l = LIST0 "," ; "]" ; "of" ; ts = type_specification -> (List.length l, ts) ]
  ]
  ;
  prim_type: [
    [ "boolean" -> PRIMTYPE_boolean loc
    | "integer" -> PRIMTYPE_integer loc
    | "real" -> PRIMTYPE_real loc
    ]
  ]
  ;
  expression: [
    [ e1 = expression ; "or" ; e2 = expression -> ExDISJ loc e1 e2 ]

  | [ e1 = expression ; "and" ; e2 = expression -> ExCONJ loc e1 e2 ]

  | [ e1 = expression ; "=" ; e2 = expression -> ExEQOP loc EQ e1 e2
    | e1 = expression ; "==" ; e2 = expression -> ExEQOP loc EQEQ e1 e2 ]
  | [ e1 = expression ; "<" ; e2 = expression -> ExRELOP loc LT e1 e2
    | e1 = expression ; ">" ; e2 = expression -> ExRELOP loc GT e1 e2 ]

  | [ e1 = expression ; "+" ; e2 = expression -> ExADDOP loc PLUS e1 e2
    | e1 = expression ; "-" ; e2 = expression -> ExADDOP loc PLUS e1 e2 ]

  | [ e1 = expression ; "*" ; e2 = expression -> ExMULOP loc STAR e1 e2
    | e1 = expression ; "/" ; e2 = expression -> ExMULOP loc SLASH e1 e2
    | e1 = expression ; "div" ; e2 = expression -> ExMULOP loc DIV e1 e2
    | e1 = expression ; "mod" ; e2 = expression -> ExMULOP loc MOD e1 e2 ]

  | [ "-" ; e = expression -> ExUNOP loc UN_MINUS e
    | "+" ; e = expression -> ExUNOP loc UN_PLUS e
    | "not" ; e = expression -> ExUNOP loc UN_NOT e ]

  | [ n = name ; ":=" ; e2 = expression -> ExASSIGN loc n e2
    | n = name -> ExNAME loc n
    | c = constant -> ExCONSTANT loc c
    | b = block -> ExBLOCK loc b
    | c = clause -> ExCLAUSE loc c
    | "(" ; e = expression ; ")" -> e
    ]
  ]
  ;
  name: [
    [ n = name ; "." ; id = LIDENT -> NameACC loc n id
    | n = name ; "[" ; el = LIST1 expression SEP "," ; "]" -> NameSUB loc n el
    | n = name ; "^" -> NameDEREF loc n
    | n = name ; "(" ; el = LIST1 expression SEP "," ; ")" -> NameCALL loc n el
    ]
  | [ id = LIDENT -> NameIDENT loc id
    | "new" ; id = LIDENT -> NameNEW loc id ]
  ]
  ;
  clause: [
    [ "if" ; e = expression ; "then" ; sl1 = statement_list ; "end" ->
      CLAUSE_IF loc e sl1 []
    |  "if" ; e = expression ; "then" ; sl1 = statement_list ; "else" ; sl2 = statement_list ; "end" ->
      CLAUSE_IF loc e sl1 sl2
    | "case" ; e = expression ; "of" ;
      l = LIST1 [ n = INT ; ":" ; sl = statement_list -> (int_of_string n,sl) ] SEP "//" ;
      "else" ; sl = statement_list ; "end" ->
      CLAUSE_CASE loc e l sl
    ]
  ]
  ;
  constant: [
    [ i = INT -> CONST_int loc (int_of_string i)
    | f = FLOAT -> CONST_float loc (float_of_string f)
    | "true" -> CONST_bool loc True
    | "false" -> CONST_bool loc False
    | "nil" -> CONST_nil loc ]
  ]
  ;
END;
