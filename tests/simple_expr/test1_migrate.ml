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
  module _ = Test1_variants
  [%%import: Test1_variants.Unique.OK.expr]
  [@@deriving migrate
    { dispatch_type = dispatch_table_t
    ; dispatch_table_constructor = make_dt
    ; default_open_recursion = false
    ; open_recursion_dispatchers = [ expr ]
    ; default_dispatchers = [
        {
          srcmod = Test1_variants.Unique.OK
        ; dstmod = Test1_variants.Unique.OK
        ; types = [
            prog
          ; block1
          ; block2
          ; expr
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
      }
    }
  ]
end

module HC = struct
  module _ = Test1_variants
  [%%import: Test1_variants.Hashcons.HC.expr]
  [@@deriving migrate
    { dispatch_type = dispatch_table_t
    ; dispatch_table_constructor = make_dt
    ; default_open_recursion = false
    ; open_recursion_dispatchers = [ expr ]
    ; default_dispatchers = [
        {
          srcmod = Test1_variants.Hashcons.HC
        ; dstmod = Test1_variants.Hashcons.HC
        ; types = [
            prog_node
          ; block1_node
          ; block2_node
          ; expr_node
          ; binop_node
          ; unop_node
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
      ; migrate_expr = {
          srctype = [%typ: expr]
        ; dsttype = [%typ: expr]
        ; code = fun __dt__ -> fun { Hashcons.node = node } ->
            Test1_variants.Hashcons.HC.make_expr (migrate_expr_node __dt__ node)
        }
      ; migrate_prog = {
          srctype = [%typ: prog]
        ; dsttype = [%typ: prog]
        ; code = fun __dt__ -> fun { Hashcons.node = node } ->
            Test1_variants.Hashcons.HC.make_prog (migrate_prog_node __dt__ node)
        }
      ; migrate_block1 = {
          srctype = [%typ: block1]
        ; dsttype = [%typ: block1]
        ; code = fun __dt__ -> fun { Hashcons.node = node } ->
            Test1_variants.Hashcons.HC.make_block1 (migrate_block1_node __dt__ node)
        }
      ; migrate_block2 = {
          srctype = [%typ: block2]
        ; dsttype = [%typ: block2]
        ; code = fun __dt__ -> fun { Hashcons.node = node } ->
            Test1_variants.Hashcons.HC.make_block2 (migrate_block2_node __dt__ node)
        }
      ; migrate_binop = {
          srctype = [%typ: binop]
        ; dsttype = [%typ: binop]
        ; code = fun __dt__ -> fun { Hashcons.node = node } ->
            Test1_variants.Hashcons.HC.make_binop (migrate_binop_node __dt__ node)
        }
      ; migrate_unop = {
          srctype = [%typ: unop]
        ; dsttype = [%typ: unop]
        ; code = fun __dt__ -> fun { Hashcons.node = node } ->
            Test1_variants.Hashcons.HC.make_unop (migrate_unop_node __dt__ node)
        }
      }
    }
  ]
end

module Unique = struct
  module _ = Test1_ag
  [%%import: Test1_ag.UN.UN.expr]
  [@@deriving migrate
    { dispatch_type = dispatch_table_t
    ; dispatch_table_constructor = make_dt
    ; default_open_recursion = false
    ; open_recursion_dispatchers = [ expr ]
    ; default_dispatchers = [
        {
          srcmod = Test1_ag.UN.UN
        ; dstmod = Test1_ag.UN.UN
        ; types = [
            prog_node
          ; block1_node
          ; block2_node
          ; expr_node
          ; binop_node
          ; unop_node
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
      ; migrate_expr = {
          srctype = [%typ: expr]
        ; dsttype = [%typ: expr]
        ; code = fun __dt__ -> fun { Pa_ppx_unique_runtime.Unique.node = node } ->
            Test1_ag.UN.UN.make_expr (migrate_expr_node __dt__ node)
        }
      ; migrate_prog = {
          srctype = [%typ: prog]
        ; dsttype = [%typ: prog]
        ; code = fun __dt__ -> fun { Pa_ppx_unique_runtime.Unique.node = node } ->
            Test1_ag.UN.UN.make_prog (migrate_prog_node __dt__ node)
        }
      ; migrate_block1 = {
          srctype = [%typ: block1]
        ; dsttype = [%typ: block1]
        ; code = fun __dt__ -> fun { Pa_ppx_unique_runtime.Unique.node = node } ->
            Test1_ag.UN.UN.make_block1 (migrate_block1_node __dt__ node)
        }
      ; migrate_block2 = {
          srctype = [%typ: block2]
        ; dsttype = [%typ: block2]
        ; code = fun __dt__ -> fun { Pa_ppx_unique_runtime.Unique.node = node } ->
            Test1_ag.UN.UN.make_block2 (migrate_block2_node __dt__ node)
        }

      ; migrate_binop = {
          srctype = [%typ: binop]
        ; dsttype = [%typ: binop]
        ; code = fun __dt__ -> fun { Pa_ppx_unique_runtime.Unique.node = node } ->
            Test1_ag.UN.UN.make_binop (migrate_binop_node __dt__ node)
        }
      ; migrate_unop = {
          srctype = [%typ: unop]
        ; dsttype = [%typ: unop]
        ; code = fun __dt__ -> fun { Pa_ppx_unique_runtime.Unique.node = node } ->
            Test1_ag.UN.UN.make_unop (migrate_unop_node __dt__ node)
        }
      }
    }
  ]
end

module ToUnique = struct
module _ = Test1_ag
[%%import: Test1_ag.UN.OK.expr]
[@@deriving migrate
    { dispatch_type = dispatch_table_t
    ; dispatch_table_constructor = make_dt
    ; dispatchers = {
        migrate_expr_node = {
          srctype = [%typ: expr_node]
        ; dsttype = [%typ: Test1_ag.UN.UN.expr_node]
        }
      ; migrate_expr = {
          srctype = [%typ: expr]
        ; dsttype = [%typ: Test1_ag.UN.UN.expr]
        ; code = (fun __dt__ x ->
            Test1_ag.UN.UN.make_expr (__dt__.migrate_expr_node __dt__ x)
          )
        }
      ; migrate_prog_node = {
          srctype = [%typ: prog_node]
        ; dsttype = [%typ: Test1_ag.UN.UN.prog_node]
        }
      ; migrate_prog = {
          srctype = [%typ: prog]
        ; dsttype = [%typ: Test1_ag.UN.UN.prog]
        ; code = (fun __dt__ x ->
            Test1_ag.UN.UN.make_prog (__dt__.migrate_prog_node __dt__ x)
          )
        }
      ; migrate_block1_node = {
          srctype = [%typ: block1_node]
        ; dsttype = [%typ: Test1_ag.UN.UN.block1_node]
        }
      ; migrate_block1 = {
          srctype = [%typ: block1]
        ; dsttype = [%typ: Test1_ag.UN.UN.block1]
        ; code = (fun __dt__ x ->
            Test1_ag.UN.UN.make_block1 (__dt__.migrate_block1_node __dt__ x)
          )
        }

      ; migrate_block2_node = {
          srctype = [%typ: block2_node]
        ; dsttype = [%typ: Test1_ag.UN.UN.block2_node]
        }
      ; migrate_block2 = {
          srctype = [%typ: block2]
        ; dsttype = [%typ: Test1_ag.UN.UN.block2]
        ; code = (fun __dt__ x ->
            Test1_ag.UN.UN.make_block2 (__dt__.migrate_block2_node __dt__ x)
          )
        }

      ; migrate_binop_node = {
          srctype = [%typ: binop_node]
        ; dsttype = [%typ: Test1_ag.UN.UN.binop_node]
        }
      ; migrate_binop = {
          srctype = [%typ: binop]
        ; dsttype = [%typ: Test1_ag.UN.UN.binop]
        ; code = (fun __dt__ x ->
            Test1_ag.UN.UN.make_binop (__dt__.migrate_binop_node __dt__ x)
          )
        }
      ; migrate_unop_node = {
          srctype = [%typ: unop_node]
        ; dsttype = [%typ: Test1_ag.UN.UN.unop_node]
        }
      ; migrate_unop = {
          srctype = [%typ: unop]
        ; dsttype = [%typ: Test1_ag.UN.UN.unop]
        ; code = (fun __dt__ x ->
            Test1_ag.UN.UN.make_unop (__dt__.migrate_unop_node __dt__ x)
          )
        }
      }
    }
]

let dt = make_dt ()
let expr x = dt.migrate_expr dt x
let prog x = dt.migrate_prog dt x

end

module FromUnique = struct
module _ = Test1_variants
[%%import: Test1_ag.UN.UN.expr]
[@@deriving migrate
    { dispatch_type = dispatch_table_t
    ; dispatch_table_constructor = make_dt
    ; dispatchers = {
        migrate_expr_node = {
          srctype = [%typ: expr_node]
        ; dsttype = [%typ: Test1_ag.UN.OK.expr_node]
        }
      ; migrate_expr = {
          srctype = [%typ: expr]
        ; dsttype = [%typ: Test1_ag.UN.OK.expr]
        ; code = (fun __dt__ x ->
            __dt__.migrate_expr_node __dt__ x.Pa_ppx_unique_runtime.Unique.node
          )
        }
      ; migrate_prog_node = {
          srctype = [%typ: prog_node]
        ; dsttype = [%typ: Test1_ag.UN.OK.prog_node]
        }
      ; migrate_prog = {
          srctype = [%typ: prog]
        ; dsttype = [%typ: Test1_ag.UN.OK.prog]
        ; code = (fun __dt__ x ->
            __dt__.migrate_prog_node __dt__ x.Pa_ppx_unique_runtime.Unique.node
          )
        }
      ; migrate_block1_node = {
          srctype = [%typ: block1_node]
        ; dsttype = [%typ: Test1_ag.UN.OK.block1_node]
        }
      ; migrate_block1 = {
          srctype = [%typ: block1]
        ; dsttype = [%typ: Test1_ag.UN.OK.block1]
        ; code = (fun __dt__ x ->
            __dt__.migrate_block1_node __dt__ x.Pa_ppx_unique_runtime.Unique.node
          )
        }
      ; migrate_block2_node = {
          srctype = [%typ: block2_node]
        ; dsttype = [%typ: Test1_ag.UN.OK.block2_node]
        }
      ; migrate_block2 = {
          srctype = [%typ: block2]
        ; dsttype = [%typ: Test1_ag.UN.OK.block2]
        ; code = (fun __dt__ x ->
            __dt__.migrate_block2_node __dt__ x.Pa_ppx_unique_runtime.Unique.node
          )
        }
      ; migrate_binop_node = {
          srctype = [%typ: binop_node]
        ; dsttype = [%typ: Test1_ag.UN.OK.binop_node]
        }
      ; migrate_binop = {
          srctype = [%typ: binop]
        ; dsttype = [%typ: Test1_ag.UN.OK.binop]
        ; code = (fun __dt__ x ->
            __dt__.migrate_binop_node __dt__ x.Pa_ppx_unique_runtime.Unique.node
          )
        }
      ; migrate_unop_node = {
          srctype = [%typ: unop_node]
        ; dsttype = [%typ: Test1_ag.UN.OK.unop_node]
        }
      ; migrate_unop = {
          srctype = [%typ: unop]
        ; dsttype = [%typ: Test1_ag.UN.OK.unop]
        ; code = (fun __dt__ x ->
            __dt__.migrate_unop_node __dt__ x.Pa_ppx_unique_runtime.Unique.node
          )
        }
      }
    }
]

let dt = make_dt ()
let expr x = dt.migrate_expr dt x
let prog x = dt.migrate_prog dt x

end

module Attributed = struct
  module _ = Test1_variants
  [%%import: Test1_ag.REC.AT.expr]
  [@@deriving migrate
    { dispatch_type = dispatch_table_t
    ; dispatch_table_constructor = make_dt
    ; default_open_recursion = false
    ; open_recursion_dispatchers = [ expr ]
    ; default_dispatchers = [
        {
          srcmod = Test1_ag.REC.AT
        ; dstmod = Test1_ag.REC.AT
        ; types = [
            prog_node
          ; block1_node
          ; block2_node
          ; expr_node
          ; binop_node
          ; unop_node
          ; expr__BINOP_attributes
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
            Test1_ag.REC.AT.make_expr (migrate_expr_node __dt__ node)
        }
      ; migrate_prog = {
          srctype = [%typ: prog]
        ; dsttype = [%typ: prog]
        ; code = fun __dt__ -> fun { Pa_ppx_ag_runtime.Attributes.node = node } ->
            Test1_ag.REC.AT.make_prog (migrate_prog_node __dt__ node)
        }
      ; migrate_block1 = {
          srctype = [%typ: block1]
        ; dsttype = [%typ: block1]
        ; code = fun __dt__ -> fun { Pa_ppx_ag_runtime.Attributes.node = node } ->
            Test1_ag.REC.AT.make_block1 (migrate_block1_node __dt__ node)
        }
      ; migrate_block2 = {
          srctype = [%typ: block2]
        ; dsttype = [%typ: block2]
        ; code = fun __dt__ -> fun { Pa_ppx_ag_runtime.Attributes.node = node } ->
            Test1_ag.REC.AT.make_block2 (migrate_block2_node __dt__ node)
        }

      ; migrate_binop = {
          srctype = [%typ: binop]
        ; dsttype = [%typ: binop]
        ; code = fun __dt__ -> fun { Pa_ppx_ag_runtime.Attributes.node = node } ->
            Test1_ag.REC.AT.make_binop (migrate_binop_node __dt__ node)
        }
      ; migrate_unop = {
          srctype = [%typ: unop]
        ; dsttype = [%typ: unop]
        ; code = fun __dt__ -> fun { Pa_ppx_ag_runtime.Attributes.node = node } ->
            Test1_ag.REC.AT.make_unop (migrate_unop_node __dt__ node)
        }
      }
    }
  ]
end

module ToAttributed = struct
module _ = Test1_variants
[%%import: Test1_ag.REC.OK.expr]
[@@deriving migrate
    { dispatch_type = dispatch_table_t
    ; dispatch_table_constructor = make_dt
    ; dispatchers = {
        migrate_expr_node = {
          srctype = [%typ: expr_node]
        ; dsttype = [%typ: Test1_ag.REC.AT.expr_node]
        ; custom_branches_code = (function
              BINOP (bop, x, y) ->
              Test1_ag.REC.AT.make_expr__BINOP
                (__dt__.migrate_binop __dt__ bop)
                (__dt__.migrate_expr __dt__ x)
                (__dt__.migrate_expr __dt__ y)
          )
        }
      ; migrate_expr = {
          srctype = [%typ: expr]
        ; dsttype = [%typ: Test1_ag.REC.AT.expr]
        ; code = (fun __dt__ x ->
            Test1_ag.REC.AT.make_expr (__dt__.migrate_expr_node __dt__ x)
          )
        }
      ; migrate_prog_node = {
          srctype = [%typ: prog_node]
        ; dsttype = [%typ: Test1_ag.REC.AT.prog_node]
        }
      ; migrate_prog = {
          srctype = [%typ: prog]
        ; dsttype = [%typ: Test1_ag.REC.AT.prog]
        ; code = (fun __dt__ x ->
            Test1_ag.REC.AT.make_prog (__dt__.migrate_prog_node __dt__ x)
          )
        }
      ; migrate_block1_node = {
          srctype = [%typ: block1_node]
        ; dsttype = [%typ: Test1_ag.REC.AT.block1_node]
        }
      ; migrate_block1 = {
          srctype = [%typ: block1]
        ; dsttype = [%typ: Test1_ag.REC.AT.block1]
        ; code = (fun __dt__ x ->
            Test1_ag.REC.AT.make_block1 (__dt__.migrate_block1_node __dt__ x)
          )
        }
      ; migrate_block2_node = {
          srctype = [%typ: block2_node]
        ; dsttype = [%typ: Test1_ag.REC.AT.block2_node]
        }
      ; migrate_block2 = {
          srctype = [%typ: block2]
        ; dsttype = [%typ: Test1_ag.REC.AT.block2]
        ; code = (fun __dt__ x ->
            Test1_ag.REC.AT.make_block2 (__dt__.migrate_block2_node __dt__ x)
          )
        }

      ; migrate_binop_node = {
          srctype = [%typ: binop_node]
        ; dsttype = [%typ: Test1_ag.REC.AT.binop_node]
        }
      ; migrate_binop = {
          srctype = [%typ: binop]
        ; dsttype = [%typ: Test1_ag.REC.AT.binop]
        ; code = (fun __dt__ x ->
            Test1_ag.REC.AT.make_binop (__dt__.migrate_binop_node __dt__ x)
          )
        }
      ; migrate_unop_node = {
          srctype = [%typ: unop_node]
        ; dsttype = [%typ: Test1_ag.REC.AT.unop_node]
        }
      ; migrate_unop = {
          srctype = [%typ: unop]
        ; dsttype = [%typ: Test1_ag.REC.AT.unop]
        ; code = (fun __dt__ x ->
            Test1_ag.REC.AT.make_unop (__dt__.migrate_unop_node __dt__ x)
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
module _ = Test1_ag
[%%import: Test1_ag.REC.AT.expr]
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
        ; dsttype = [%typ: Test1_ag.REC.OK.expr_node]
        ; custom_branches_code = (function
              BINOP (bop, x, y, _) ->
              Test1_ag.REC.OK.BINOP
                (__dt__.migrate_binop __dt__ bop,
                 __dt__.migrate_expr __dt__ x,
                 __dt__.migrate_expr __dt__ y)
          )
        }
      ; migrate_expr = {
          srctype = [%typ: expr]
        ; dsttype = [%typ: Test1_ag.REC.OK.expr]
        ; code = (fun __dt__ x ->
            __dt__.migrate_expr_node __dt__ x.Pa_ppx_ag_runtime.Attributes.node
          )
        }
      ; migrate_prog_node = {
          srctype = [%typ: prog_node]
        ; dsttype = [%typ: Test1_ag.REC.OK.prog_node]
        }
      ; migrate_prog = {
          srctype = [%typ: prog]
        ; dsttype = [%typ: Test1_ag.REC.OK.prog]
        ; code = (fun __dt__ x ->
            __dt__.migrate_prog_node __dt__ x.Pa_ppx_ag_runtime.Attributes.node
          )
        }
      ; migrate_block1_node = {
          srctype = [%typ: block1_node]
        ; dsttype = [%typ: Test1_ag.REC.OK.block1_node]
        }
      ; migrate_block1 = {
          srctype = [%typ: block1]
        ; dsttype = [%typ: Test1_ag.REC.OK.block1]
        ; code = (fun __dt__ x ->
            __dt__.migrate_block1_node __dt__ x.Pa_ppx_ag_runtime.Attributes.node
          )
        }
      ; migrate_block2_node = {
          srctype = [%typ: block2_node]
        ; dsttype = [%typ: Test1_ag.REC.OK.block2_node]
        }
      ; migrate_block2 = {
          srctype = [%typ: block2]
        ; dsttype = [%typ: Test1_ag.REC.OK.block2]
        ; code = (fun __dt__ x ->
            __dt__.migrate_block2_node __dt__ x.Pa_ppx_ag_runtime.Attributes.node
          )
        }

      ; migrate_binop_node = {
          srctype = [%typ: binop_node]
        ; dsttype = [%typ: Test1_ag.REC.OK.binop_node]
        }
      ; migrate_binop = {
          srctype = [%typ: binop]
        ; dsttype = [%typ: Test1_ag.REC.OK.binop]
        ; code = (fun __dt__ x ->
            __dt__.migrate_binop_node __dt__ x.Pa_ppx_ag_runtime.Attributes.node
          )
        }
      ; migrate_unop_node = {
          srctype = [%typ: unop_node]
        ; dsttype = [%typ: Test1_ag.REC.OK.unop_node]
        }
      ; migrate_unop = {
          srctype = [%typ: unop]
        ; dsttype = [%typ: Test1_ag.REC.OK.unop]
        ; code = (fun __dt__ x ->
            __dt__.migrate_unop_node __dt__ x.Pa_ppx_ag_runtime.Attributes.node
          )
        }
      }
    }
]

let dt = make_dt ()
let expr x = dt.migrate_expr dt x
let prog x = dt.migrate_prog dt x

end
