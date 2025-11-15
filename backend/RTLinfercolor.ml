open Maps
open RTL
(* open RTLdmr *)
open RTLcolor

(* Parameter infer_coloring : function -> option (node -> PTree.t color). *)

let infer_coloring (f : coq_function) : (node -> color PTree.t) option =
  None
