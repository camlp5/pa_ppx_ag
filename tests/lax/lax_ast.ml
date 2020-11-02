(* camlp5o *)
(* lax_ast.ml *)

(** LAX AST (from Goos & Waite compilers book)

================================================================

A.2 Program Structure
A.2.0.1   program ::= block ;;
A.2.0.2 * range ::= block | statement list | iteration | record type | procedure ;;
A.2.0.3   block ::= 'declare' (declaration || ';') 'begin'(statement || ';') 'end' ;;
A.2.0.4   statement_list ::= statement || ';' ;;
A.2.0.5   statement ::= label_definition* (expression | iteration | jump) ;;
A.2.0.6   label_definition ::= identifier ':' ;;
A.2.0.7   iteration ::= 'while' expression loop
          | 'for' identifier 'from' expression 'to' expression loop ;;
A.2.0.8   loop ::= 'do' statement_list 'end' ;;
A.2.0.9   jump ::= 'goto'  identifier ;;

================================================================

declare standard declarations begin program end

The standard declarations provide de ning occurrences of the prede ned identi ers given
in Table A.1. These declarations cannot be expressed in LAX.

Identifier  Meaning
boolean    Logical type
false      Falsity
integer    Integer type
nil        Reference to no object
real       Floating point type
true       Truth

================================================================

A.3        Declarations
A.3.0.1    declaration ::= variable_declaration
           | identity_declaration
           | procedure_declaration
           | type_declaration ;;
A.3.0.2    variable_declaration ::= identifier ':'type_specification
           | identifier ':'
           'array' '[' (bound_pair || ';') ']' 'of' type_specification ;;
A.3.0.3    type_specification ::= identifier
           | 'ref' type_specification
           | 'ref' array_type
           | procedure_type ;;
A.3.0.4    bound_pair ::= expression ':' expression ;;
A.3.0.5    array_type ::= 'array' '[' ','* ']' 'of' type_specification ;;
A.3.0.6    procedure_type ::=
           'procedure' [ '(' (type_specification || ',') ')' ] [result_type] ;;
A.3.0.7    identity_declaration ::=
           identifier 'is' expression ':' type_specification ;;
A.3.0.8    procedure_declaration ::= 'procedure' identifier procedure ;;
A.3.0.9    procedure ::= [ '(' (parameter || ';') ')' ] [result_type] ';' expression ;;
A.3.0.10   parameter ::= identifier ':' type_specification ;;
A.3.0.11   result_type ::= ':' type_specification ;;
A.3.0.12   type_declaration ::= 'type' identifier '=' record_type ;;
A.3.0.13   record_type ::= 'record' (field || ';') 'end' ;;
A.3.0.14   field ::= identifier ':' type_specification ;;
A.3.0.15 * type ::= type_specification | array_type | procedure_type ;;

================================================================

A.4 Expressions
A.4.0.1     expression ::= assignment | disjunction ;;
A.4.0.2     assignment ::= name ':=' expression ;;
A.4.0.3     disjunction ::= conjunction | disjunction 'or' conjunction ;;
A.4.0.4     conjunction ::= comparison | conjunction 'and' comparison ;;
A.4.0.5     comparison ::= relation [eqop relation] ;;
A.4.0.6     eqop ::= '=' | '=='  ;;
A.4.0.7     relation ::= sum [relop sum] ;;
A.4.0.8     relop ::= '<' | '>'  ;;
A.4.0.9     sum ::= term | sum addop term ;;
A.4.0.10    addop ::= '+' | '-'  ;;
A.4.0.11    term ::= factor | term mulop factor ;;
A.4.0.12    mulop ::= '*' | '/' | 'div' | 'mod'  ;;
A.4.0.13    factor ::= primary | unop factor ;;
A.4.0.14    unop ::= '+' | '-' | 'not'  ;;
A.4.0.15    primary ::= constant | name | '(' expression ')' | block | clause ;;
A.4.0.16    name ::= identifier
            | name '.' identifier
            | name '[' (expression || ',' ) ']'
            | name '^'
            | 'new' identifier
            | procedure_call ;;

A.4.0.17    procedure_call ::= name '(' (argument || ',' ) ')'  ;;
A.4.0.18    argument ::= expression ;;
A.4.0.19    clause ::= conditional_clause | case_clause ;;
A.4.0.20    conditional_clause ::= 'if' expression 'then' statement_list 'end'
            | 'if' expression 'then' statement_list 'else' statement_list 'end'  ;;
A.4.0.21    case_clause ::=
            'case' expression 'of'
            (case_label ':' statement_list || '//' )
            'else' statement_list 'end'  ;;
A.4.0.22    case_label ::= integer ;;

================================================================



================================================================
================================================================

*)

type loc = Ploc.t
open Ploc

type identifier = string
type constant =
    CONST_int of loc * int
  | CONST_float of loc * float
  | CONST_bool of loc * bool
  | CONST_nil of loc

type prim_type =
    PRIMTYPE_integer of loc
  | PRIMTYPE_real of loc
  | PRIMTYPE_boolean of loc

type expression =
    ExASSIGN of loc * name * expression
  | ExDISJ of loc * expression * expression
  | ExCONJ of loc * expression * expression
  | ExRELOP of loc * relop * expression * expression
  | ExEQOP of loc * eqop * expression * expression
  | ExADDOP of loc * addop * expression * expression
  | ExMULOP of loc * mulop * expression * expression
  | ExUNOP of loc * unop * expression
  | ExCONSTANT of loc * constant
  | ExNAME of loc * name
  | ExBLOCK of loc * block
  | ExCLAUSE of loc * clause

and name =
    NameIDENT of loc * identifier
  | NameACC of loc * name * identifier
  | NameSUB of loc * name * expression list
  | NameDEREF of loc * name
  | NameNEW of loc * identifier
  | NameCALL of loc * name * expression list

and clause =
    CLAUSE_IF of loc * expression * statement list * statement list
  | CLAUSE_CASE of loc * expression * (case_label * statement list) list * statement list

and case_label = int
and relop = GT | LT
and eqop = EQ | EQEQ
and addop = PLUS | MINUS
and mulop = STAR | SLASH | DIV | MOD
and unop = UN_PLUS | UN_MINUS | UN_NOT

and declaration =
    DECL_VARIABLE of loc * identifier * variable_declaration_rhs
  | DECL_IDENTITY of loc * identifier * expression * type_specification
  | DECL_PROCEDURE of loc * identifier * procedure
  | DECL_TYPE of loc * identifier * record_type

and variable_declaration_rhs =
    VAR_TYPE of loc * type_specification
  | VAR_ARRAY of loc * (expression * expression) list * type_specification

and type_specification =
    TYPE_ID of loc * identifier
  | TYPE_PRIM of loc * prim_type
  | TYPE_REF of loc * type_specification
  | TYPE_REFARRAY of loc * array_type
  | TYPE_PROC of loc * procedure_type

and array_type = (int * type_specification)
and procedure_type = (type_specification list * type_specification option)
and procedure = (parameter list * type_specification option * expression)
and parameter = (identifier * type_specification)
and record_type = (identifier * type_specification) list

and program = block
and block = (declaration list * statement list)
and statement = (identifier list * bare_statement)
and bare_statement =
    STMT_EXPR of loc * expression
  | STMT_ITER of loc * iteration
  | STMT_JUMP of loc * identifier

and iteration =
    ITER_WHILE of loc * expression * statement list
  | ITER_FOR of loc * identifier * expression * expression * statement list
