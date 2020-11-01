(* camlp5o *)
(* test1_migrate.ml *)

exception Migration_error of string

let migration_error feature =
  raise (Migration_error feature)

let _migrate_list subrw0 __dt__ l =
  List.map (subrw0 __dt__) l

module OK = struct
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
  [%%import: Test1_variants.Unique.UN.expr]
  [@@deriving migrate
    { dispatch_type = dispatch_table_t
    ; dispatch_table_constructor = make_dt
    ; default_open_recursion = false
    ; open_recursion_dispatchers = [ expr ]
    ; default_dispatchers = [
        {
          srcmod = Test1_variants.Unique.UN
        ; dstmod = Test1_variants.Unique.UN
        ; types = [
            prog_node
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
            Test1_variants.Unique.UN.make_expr (migrate_expr_node __dt__ node)
        }
      ; migrate_prog = {
          srctype = [%typ: prog]
        ; dsttype = [%typ: prog]
        ; code = fun __dt__ -> fun { Pa_ppx_unique_runtime.Unique.node = node } ->
            Test1_variants.Unique.UN.make_prog (migrate_prog_node __dt__ node)
        }
      ; migrate_binop = {
          srctype = [%typ: binop]
        ; dsttype = [%typ: binop]
        ; code = fun __dt__ -> fun { Pa_ppx_unique_runtime.Unique.node = node } ->
            Test1_variants.Unique.UN.make_binop (migrate_binop_node __dt__ node)
        }
      ; migrate_unop = {
          srctype = [%typ: unop]
        ; dsttype = [%typ: unop]
        ; code = fun __dt__ -> fun { Pa_ppx_unique_runtime.Unique.node = node } ->
            Test1_variants.Unique.UN.make_unop (migrate_unop_node __dt__ node)
        }
      }
    }
  ]
end

module ToUnique = struct

[%%import: Test1_variants.Unique.OK.expr]
[@@deriving migrate
    { dispatch_type = dispatch_table_t
    ; dispatch_table_constructor = make_dt
    ; dispatchers = {
        migrate_expr_node = {
          srctype = [%typ: expr_node]
        ; dsttype = [%typ: Test1_variants.Unique.UN.expr_node]
        }
      ; migrate_expr = {
          srctype = [%typ: expr]
        ; dsttype = [%typ: Test1_variants.Unique.UN.expr]
        ; code = (fun __dt__ x ->
            Test1_variants.Unique.UN.make_expr (__dt__.migrate_expr_node __dt__ x)
          )
        }
      ; migrate_prog_node = {
          srctype = [%typ: prog_node]
        ; dsttype = [%typ: Test1_variants.Unique.UN.prog_node]
        }
      ; migrate_prog = {
          srctype = [%typ: prog]
        ; dsttype = [%typ: Test1_variants.Unique.UN.prog]
        ; code = (fun __dt__ x ->
            Test1_variants.Unique.UN.make_prog (__dt__.migrate_prog_node __dt__ x)
          )
        }
      ; migrate_binop_node = {
          srctype = [%typ: binop_node]
        ; dsttype = [%typ: Test1_variants.Unique.UN.binop_node]
        }
      ; migrate_binop = {
          srctype = [%typ: binop]
        ; dsttype = [%typ: Test1_variants.Unique.UN.binop]
        ; code = (fun __dt__ x ->
            Test1_variants.Unique.UN.make_binop (__dt__.migrate_binop_node __dt__ x)
          )
        }
      ; migrate_unop_node = {
          srctype = [%typ: unop_node]
        ; dsttype = [%typ: Test1_variants.Unique.UN.unop_node]
        }
      ; migrate_unop = {
          srctype = [%typ: unop]
        ; dsttype = [%typ: Test1_variants.Unique.UN.unop]
        ; code = (fun __dt__ x ->
            Test1_variants.Unique.UN.make_unop (__dt__.migrate_unop_node __dt__ x)
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

[%%import: Test1_variants.Unique.UN.expr]
[@@deriving migrate
    { dispatch_type = dispatch_table_t
    ; dispatch_table_constructor = make_dt
    ; dispatchers = {
        migrate_expr_node = {
          srctype = [%typ: expr_node]
        ; dsttype = [%typ: Test1_variants.Unique.OK.expr_node]
        }
      ; migrate_expr = {
          srctype = [%typ: expr]
        ; dsttype = [%typ: Test1_variants.Unique.OK.expr]
        ; code = (fun __dt__ x ->
            __dt__.migrate_expr_node __dt__ x.Pa_ppx_unique_runtime.Unique.node
          )
        }
      ; migrate_prog_node = {
          srctype = [%typ: prog_node]
        ; dsttype = [%typ: Test1_variants.Unique.OK.prog_node]
        }
      ; migrate_prog = {
          srctype = [%typ: prog]
        ; dsttype = [%typ: Test1_variants.Unique.OK.prog]
        ; code = (fun __dt__ x ->
            __dt__.migrate_prog_node __dt__ x.Pa_ppx_unique_runtime.Unique.node
          )
        }
      ; migrate_binop_node = {
          srctype = [%typ: binop_node]
        ; dsttype = [%typ: Test1_variants.Unique.OK.binop_node]
        }
      ; migrate_binop = {
          srctype = [%typ: binop]
        ; dsttype = [%typ: Test1_variants.Unique.OK.binop]
        ; code = (fun __dt__ x ->
            __dt__.migrate_binop_node __dt__ x.Pa_ppx_unique_runtime.Unique.node
          )
        }
      ; migrate_unop_node = {
          srctype = [%typ: unop_node]
        ; dsttype = [%typ: Test1_variants.Unique.OK.unop_node]
        }
      ; migrate_unop = {
          srctype = [%typ: unop]
        ; dsttype = [%typ: Test1_variants.Unique.OK.unop]
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
