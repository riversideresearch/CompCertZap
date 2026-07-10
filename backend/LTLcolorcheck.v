Require Import
  AST
  Builtins
  SharedFaultPolicy
  FaultPolicy
  CompCertZapUtils
  Errors
  Coqlib
  Events
  Integers
  LProofLiveness
  List
  Maps
  Registers
  LTL
  RTLcolor
  Values
  Locations
.

(*Definition check_col_function (f : function) : bool :=*)
(*  forallb (fun param => col f.(fn_entrypoint) param =?*)
Locate infer_coloring.
Check LProofLiveness.analyze.
Print LTL.function.
Check PTree.t.
Print PTree.

Parameter infer_coloring
  : function -> PMap.t (list Locset.t) -> option (node -> reg -> color).

Definition check_function (f :function) : bool :=
  match LProofLiveness.analyze f with
  | Some live => 
      let alive := block_live_after f live in
      match infer_coloring f (block_inst_llafter f alive) with
      | None => false
      | Some col => true
      end
  | None => false
  end.
  (*match ProofLiveness.analyze f with*)
  (*| Some live => match infer_coloring f live with*)
  (*               | None => false*)
  (*               | Some col => check_col_function live col f*)
  (*| None => false*)
  (*end.*)


Definition check_program (p :program) : bool :=
  forallb (fun def => match snd def with
                      | Gfun (Internal f) => check_function f
                      | _ => true
                      end) p.(prog_defs).

