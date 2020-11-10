(* camlp5o *)
(* test1_migrate.ml *)

exception Migration_error of string

let migration_error feature =
  raise (Migration_error feature)

let _migrate_list subrw0 __dt__ l =
  List.map (subrw0 __dt__) l

let _migrate_option subrw0 __dt__ x =
  Option.map (subrw0 __dt__) x

module OK = struct
  module _ = Test2_ag
  [%%import: Test2_ag.expr]
  [@@deriving migrate
    { dispatch_type = dispatch_table_t
    ; dispatch_table_constructor = make_dt
    ; default_open_recursion = false
    ; open_recursion_dispatchers = [ expr ]
    ; default_dispatchers = [
        {
          srcmod = Test2_ag
        ; dstmod = Test2_ag
        ; types = [
            prog
          ; expr
          ]
        }
      ]
    ; dispatchers = {
        migrate_list = {
          srctype = [%typ: 'a list]
        ; dsttype = [%typ: 'b list]
        ; code = _migrate_list
        ; subs = [ ([%typ: 'a], [%typ: 'b]) ]
        }
      }
    }
  ]
end

module Attributed = struct
  module _ = Test2_ag
  [%%import: Test2_ag.AT.expr]
  [@@deriving migrate
    { dispatch_type = dispatch_table_t
    ; dispatch_table_constructor = make_dt
    ; default_open_recursion = false
    ; open_recursion_dispatchers = [ expr ]
    ; default_dispatchers = [
        {
          srcmod = Test2_ag.AT
        ; dstmod = Test2_ag.AT
        ; types = [
            prog_node
          ; expr_node
          ; expr__PLUS_attributes
          ; prog__PROG_attributes
          ]
        }
      ]
    ; dispatchers = {
        migrate_list = {
          srctype = [%typ: 'a list]
        ; dsttype = [%typ: 'b list]
        ; code = _migrate_list
        ; subs = [ ([%typ: 'a], [%typ: 'b]) ]
        }
      ; migrate_option = {
          srctype = [%typ: 'a option]
        ; dsttype = [%typ: 'b option]
        ; subs = [ ([%typ: 'a], [%typ: 'b]) ]
        ; code = _migrate_option
        }
      ; migrate_expr = {
          srctype = [%typ: expr]
        ; dsttype = [%typ: expr]
        ; code = fun __dt__ -> fun { Pa_ppx_ag_runtime.Attributes.node = node } ->
            Test2_ag.AT.make_expr (migrate_expr_node __dt__ node)
        }
      ; migrate_prog = {
          srctype = [%typ: prog]
        ; dsttype = [%typ: prog]
        ; code = fun __dt__ -> fun { Pa_ppx_ag_runtime.Attributes.node = node } ->
            Test2_ag.AT.make_prog (migrate_prog_node __dt__ node)
        }
      }
    }
  ]
end

module ToAttributed = struct
module _ = Test2_ag
type expr = expr_node
and expr_node = [%import: Test2_ag.expr]
and prog = prog_node
and prog_node = [%import: Test2_ag.prog]
[@@deriving migrate
    { dispatch_type = dispatch_table_t
    ; dispatch_table_constructor = make_dt
    ; dispatchers = {
        migrate_expr_node = {
          srctype = [%typ: expr_node]
        ; dsttype = [%typ: Test2_ag.AT.expr_node]
        ; custom_branches_code = (function
              PLUS (x, y) ->
              Test2_ag.AT.make_expr__PLUS
                (__dt__.migrate_expr __dt__ x)
                (__dt__.migrate_expr __dt__ y)
          )
        }
      ; migrate_expr = {
          srctype = [%typ: expr]
        ; dsttype = [%typ: Test2_ag.AT.expr]
        ; code = (fun __dt__ x ->
            Test2_ag.AT.make_expr (__dt__.migrate_expr_node __dt__ x)
          )
        }
      ; migrate_prog_node = {
          srctype = [%typ: prog_node]
        ; dsttype = [%typ: Test2_ag.AT.prog_node]
        ; code = (fun __dt__ -> function PROG x ->
            Test2_ag.AT.make_prog__PROG (__dt__.migrate_expr __dt__ x)
          )
        }
      ; migrate_prog = {
          srctype = [%typ: prog]
        ; dsttype = [%typ: Test2_ag.AT.prog]
        ; code = (fun __dt__ x ->
            Test2_ag.AT.make_prog (__dt__.migrate_prog_node __dt__ x)
          )
        }
      }
    }
]

let dt = make_dt ()
let expr x = dt.migrate_expr dt x
let prog x = dt.migrate_prog dt x

end

module FromAttributed = struct
module _ = Test2_ag
[%%import: Test2_ag.AT.expr]
[@@deriving migrate
    { dispatch_type = dispatch_table_t
    ; dispatch_table_constructor = make_dt
    ; dispatchers = {
        migrate_option = {
          srctype = [%typ: 'a option]
        ; dsttype = [%typ: 'b option]
        ; subs = [ ([%typ: 'a], [%typ: 'b]) ]
        ; code = _migrate_option
        }
      ; migrate_expr_node = {
          srctype = [%typ: expr_node]
        ; dsttype = [%typ: Test2_ag.expr]
        ; custom_branches_code = (function
              PLUS (x, y, _) ->
              Test2_ag.PLUS
                (__dt__.migrate_expr __dt__ x,
                 __dt__.migrate_expr __dt__ y)
          )
        }
      ; migrate_expr = {
          srctype = [%typ: expr]
        ; dsttype = [%typ: Test2_ag.expr]
        ; code = (fun __dt__ x ->
            __dt__.migrate_expr_node __dt__ x.Pa_ppx_ag_runtime.Attributes.node
          )
        }
      ; migrate_prog_node = {
          srctype = [%typ: prog_node]
        ; dsttype = [%typ: Test2_ag.prog]
        ; custom_branches_code = (function
              PROG (e, _) ->
              Test2_ag.PROG (__dt__.migrate_expr __dt__ e)
          )
        }
      ; migrate_prog = {
          srctype = [%typ: prog]
        ; dsttype = [%typ: Test2_ag.prog]
        ; code = (fun __dt__ x ->
            __dt__.migrate_prog_node __dt__ x.Pa_ppx_ag_runtime.Attributes.node
          )
        }
      }
    }
]

let dt = make_dt ()
let expr x = dt.migrate_expr dt x
let prog x = dt.migrate_prog dt x

end
