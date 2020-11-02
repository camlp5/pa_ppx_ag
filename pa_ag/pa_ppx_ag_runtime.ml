(* camlp5r *)
(* pa_ppx_ag_runtime.ml,v *)

module Attributes = struct
  type attributed 'a 'b = { id : int ; node : 'a ; attributes : 'b } ;
  value ctr = ref 0 ;
  value attributed ~{attributes} node =
    let id = ctr.val in do {
      ctr.val := 1 + ctr.val ;
      { id = id ; node = node ; attributes = attributes }
    } ;
end ;
