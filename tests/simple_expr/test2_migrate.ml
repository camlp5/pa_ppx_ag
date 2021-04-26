(* camlp5o *)
(* test2_migrate.ml *)

type loc = Ploc.t
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
          ; block1
          ; block2
          ; expr
          ; let_expr
          ; let_body
          ; ref_expr
          ; binop
          ; unop
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
      ; migrate_loc = {
          srctype = [%typ: loc]
        ; dsttype = [%typ: loc]
        ; code = fun __dt__ x -> x
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
          ; block1_node
          ; block2_node
          ; expr_node
          ; let_expr_node
          ; let_body_node
          ; ref_expr_node
          ; binop_node
          ; unop_node
          ; expr__BINOP_attributes
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
      ; migrate_let_expr = {
          srctype = [%typ: let_expr]
        ; dsttype = [%typ: let_expr]
        ; code = fun __dt__ -> fun { Pa_ppx_ag_runtime.Attributes.node = node } ->
            Test2_ag.AT.make_let_expr (migrate_let_expr_node __dt__ node)
        }
      ; migrate_let_body = {
          srctype = [%typ: let_body]
        ; dsttype = [%typ: let_body]
        ; code = fun __dt__ -> fun { Pa_ppx_ag_runtime.Attributes.node = node } ->
            Test2_ag.AT.make_let_body (migrate_let_body_node __dt__ node)
        }
      ; migrate_ref_expr = {
          srctype = [%typ: ref_expr]
        ; dsttype = [%typ: ref_expr]
        ; code = fun __dt__ -> fun { Pa_ppx_ag_runtime.Attributes.node = node } ->
            Test2_ag.AT.make_ref_expr (migrate_ref_expr_node __dt__ node)
        }
      ; migrate_prog = {
          srctype = [%typ: prog]
        ; dsttype = [%typ: prog]
        ; code = fun __dt__ -> fun { Pa_ppx_ag_runtime.Attributes.node = node } ->
            Test2_ag.AT.make_prog (migrate_prog_node __dt__ node)
        }
      ; migrate_block1 = {
          srctype = [%typ: block1]
        ; dsttype = [%typ: block1]
        ; code = fun __dt__ -> fun { Pa_ppx_ag_runtime.Attributes.node = node } ->
            Test2_ag.AT.make_block1 (migrate_block1_node __dt__ node)
        }
      ; migrate_block2 = {
          srctype = [%typ: block2]
        ; dsttype = [%typ: block2]
        ; code = fun __dt__ -> fun { Pa_ppx_ag_runtime.Attributes.node = node } ->
            Test2_ag.AT.make_block2 (migrate_block2_node __dt__ node)
        }

      ; migrate_binop = {
          srctype = [%typ: binop]
        ; dsttype = [%typ: binop]
        ; code = fun __dt__ -> fun { Pa_ppx_ag_runtime.Attributes.node = node } ->
            Test2_ag.AT.make_binop (migrate_binop_node __dt__ node)
        }
      ; migrate_unop = {
          srctype = [%typ: unop]
        ; dsttype = [%typ: unop]
        ; code = fun __dt__ -> fun { Pa_ppx_ag_runtime.Attributes.node = node } ->
            Test2_ag.AT.make_unop (migrate_unop_node __dt__ node)
        }
      ; migrate_loc = {
          srctype = [%typ: loc]
        ; dsttype = [%typ: loc]
        ; code = fun __dt__ x -> x
        }
      }
    }
  ]
end

module ToAttributed = struct
module _ = Test2_ag
type let_expr = let_expr_node
and let_expr_node = [%import: Test2_ag.let_expr]
and let_body = let_body_node
and let_body_node = [%import: Test2_ag.let_body]
and ref_expr = ref_expr_node
and ref_expr_node = [%import: Test2_ag.ref_expr]
and expr = expr_node
and expr_node = [%import: Test2_ag.expr]
and binop = binop_node
and binop_node = [%import: Test2_ag.binop]
and unop = unop_node
and unop_node = [%import: Test2_ag.unop]
and prog = prog_node
and prog_node = [%import: Test2_ag.prog]
and block1 = block1_node
and block1_node = [%import: Test2_ag.block1]
and block2 = block2_node
and block2_node = [%import: Test2_ag.block2]
[@@deriving migrate
    { dispatch_type = dispatch_table_t
    ; dispatch_table_constructor = make_dt
    ; dispatchers = {
        migrate_expr_node = {
          srctype = [%typ: expr_node]
        ; dsttype = [%typ: Test2_ag.AT.expr_node]
        ; custom_branches_code = (function
              BINOP (loc, bop, x, y) ->
              Test2_ag.AT.make_expr__BINOP_0
                loc
                (__dt__.migrate_binop __dt__ bop)
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
      ; migrate_let_expr_node = {
          srctype = [%typ: let_expr_node]
        ; dsttype = [%typ: Test2_ag.AT.let_expr_node]
        }
      ; migrate_let_expr = {
          srctype = [%typ: let_expr]
        ; dsttype = [%typ: Test2_ag.AT.let_expr]
        ; code = (fun __dt__ x ->
            Test2_ag.AT.make_let_expr (__dt__.migrate_let_expr_node __dt__ x)
          )
        }
      ; migrate_let_body_node = {
          srctype = [%typ: let_body_node]
        ; dsttype = [%typ: Test2_ag.AT.let_body_node]
        }
      ; migrate_let_body = {
          srctype = [%typ: let_body]
        ; dsttype = [%typ: Test2_ag.AT.let_body]
        ; code = (fun __dt__ x ->
            Test2_ag.AT.make_let_body (__dt__.migrate_let_body_node __dt__ x)
          )
        }
      ; migrate_ref_expr_node = {
          srctype = [%typ: ref_expr_node]
        ; dsttype = [%typ: Test2_ag.AT.ref_expr_node]
        }
      ; migrate_ref_expr = {
          srctype = [%typ: ref_expr]
        ; dsttype = [%typ: Test2_ag.AT.ref_expr]
        ; code = (fun __dt__ x ->
            Test2_ag.AT.make_ref_expr (__dt__.migrate_ref_expr_node __dt__ x)
          )
        }
      ; migrate_prog_node = {
          srctype = [%typ: prog_node]
        ; dsttype = [%typ: Test2_ag.AT.prog_node]
        ; custom_branches_code = (function
              PROG x ->
              Test2_ag.AT.make_prog__PROG_0
                (__dt__.migrate_block1 __dt__ x)
          )
        }
      ; migrate_prog = {
          srctype = [%typ: prog]
        ; dsttype = [%typ: Test2_ag.AT.prog]
        ; code = (fun __dt__ x ->
            Test2_ag.AT.make_prog (__dt__.migrate_prog_node __dt__ x)
          )
        }
      ; migrate_block1_node = {
          srctype = [%typ: block1_node]
        ; dsttype = [%typ: Test2_ag.AT.block1_node]
        }
      ; migrate_block1 = {
          srctype = [%typ: block1]
        ; dsttype = [%typ: Test2_ag.AT.block1]
        ; code = (fun __dt__ x ->
            Test2_ag.AT.make_block1 (__dt__.migrate_block1_node __dt__ x)
          )
        }
      ; migrate_block2_node = {
          srctype = [%typ: block2_node]
        ; dsttype = [%typ: Test2_ag.AT.block2_node]
        }
      ; migrate_block2 = {
          srctype = [%typ: block2]
        ; dsttype = [%typ: Test2_ag.AT.block2]
        ; code = (fun __dt__ x ->
            Test2_ag.AT.make_block2 (__dt__.migrate_block2_node __dt__ x)
          )
        }
      ; migrate_binop_node = {
          srctype = [%typ: binop_node]
        ; dsttype = [%typ: Test2_ag.AT.binop_node]
        }
      ; migrate_binop = {
          srctype = [%typ: binop]
        ; dsttype = [%typ: Test2_ag.AT.binop]
        ; code = (fun __dt__ x ->
            Test2_ag.AT.make_binop (__dt__.migrate_binop_node __dt__ x)
          )
        }
      ; migrate_unop_node = {
          srctype = [%typ: unop_node]
        ; dsttype = [%typ: Test2_ag.AT.unop_node]
        }
      ; migrate_unop = {
          srctype = [%typ: unop]
        ; dsttype = [%typ: Test2_ag.AT.unop]
        ; code = (fun __dt__ x ->
            Test2_ag.AT.make_unop (__dt__.migrate_unop_node __dt__ x)
          )
        }
      ; migrate_loc = {
          srctype = [%typ: loc]
        ; dsttype = [%typ: loc]
        ; code = fun __dt__ x -> x
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
              BINOP (loc, bop, x, y, _) ->
              Test2_ag.BINOP
                (loc,
                 __dt__.migrate_binop __dt__ bop,
                 __dt__.migrate_expr __dt__ x,
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
      ; migrate_let_expr_node = {
          srctype = [%typ: let_expr_node]
        ; dsttype = [%typ: Test2_ag.let_expr]
        }
      ; migrate_let_expr = {
          srctype = [%typ: let_expr]
        ; dsttype = [%typ: Test2_ag.let_expr]
        ; code = (fun __dt__ x ->
            __dt__.migrate_let_expr_node __dt__ x.Pa_ppx_ag_runtime.Attributes.node
          )
        }
      ; migrate_let_body_node = {
          srctype = [%typ: let_body_node]
        ; dsttype = [%typ: Test2_ag.let_body]
        }
      ; migrate_let_body = {
          srctype = [%typ: let_body]
        ; dsttype = [%typ: Test2_ag.let_body]
        ; code = (fun __dt__ x ->
            __dt__.migrate_let_body_node __dt__ x.Pa_ppx_ag_runtime.Attributes.node
          )
        }
      ; migrate_ref_expr_node = {
          srctype = [%typ: ref_expr_node]
        ; dsttype = [%typ: Test2_ag.ref_expr]
        }
      ; migrate_ref_expr = {
          srctype = [%typ: ref_expr]
        ; dsttype = [%typ: Test2_ag.ref_expr]
        ; code = (fun __dt__ x ->
            __dt__.migrate_ref_expr_node __dt__ x.Pa_ppx_ag_runtime.Attributes.node
          )
        }
      ; migrate_prog_node = {
          srctype = [%typ: prog_node]
        ; dsttype = [%typ: Test2_ag.prog]
        ; custom_branches_code = (function
              PROG (x, _) ->
              Test2_ag.PROG
                (__dt__.migrate_block1 __dt__ x)
          )
        }
      ; migrate_prog = {
          srctype = [%typ: prog]
        ; dsttype = [%typ: Test2_ag.prog]
        ; code = (fun __dt__ x ->
            __dt__.migrate_prog_node __dt__ x.Pa_ppx_ag_runtime.Attributes.node
          )
        }
      ; migrate_block1_node = {
          srctype = [%typ: block1_node]
        ; dsttype = [%typ: Test2_ag.block1]
        }
      ; migrate_block1 = {
          srctype = [%typ: block1]
        ; dsttype = [%typ: Test2_ag.block1]
        ; code = (fun __dt__ x ->
            __dt__.migrate_block1_node __dt__ x.Pa_ppx_ag_runtime.Attributes.node
          )
        }
      ; migrate_block2_node = {
          srctype = [%typ: block2_node]
        ; dsttype = [%typ: Test2_ag.block2]
        }
      ; migrate_block2 = {
          srctype = [%typ: block2]
        ; dsttype = [%typ: Test2_ag.block2]
        ; code = (fun __dt__ x ->
            __dt__.migrate_block2_node __dt__ x.Pa_ppx_ag_runtime.Attributes.node
          )
        }

      ; migrate_binop_node = {
          srctype = [%typ: binop_node]
        ; dsttype = [%typ: Test2_ag.binop]
        }
      ; migrate_binop = {
          srctype = [%typ: binop]
        ; dsttype = [%typ: Test2_ag.binop]
        ; code = (fun __dt__ x ->
            __dt__.migrate_binop_node __dt__ x.Pa_ppx_ag_runtime.Attributes.node
          )
        }
      ; migrate_unop_node = {
          srctype = [%typ: unop_node]
        ; dsttype = [%typ: Test2_ag.unop]
        }
      ; migrate_unop = {
          srctype = [%typ: unop]
        ; dsttype = [%typ: Test2_ag.unop]
        ; code = (fun __dt__ x ->
            __dt__.migrate_unop_node __dt__ x.Pa_ppx_ag_runtime.Attributes.node
          )
        }
      ; migrate_loc = {
          srctype = [%typ: loc]
        ; dsttype = [%typ: loc]
        ; code = fun __dt__ x -> x
        }
      }
    }
]

let dt = make_dt ()
let expr x = dt.migrate_expr dt x
let prog x = dt.migrate_prog dt x

end

