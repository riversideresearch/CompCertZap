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
  ProofLiveness
  List
  Maps
  Registers
  LTL
  RTLcolor
  Values
.

(*Definition check_col_function (f : function) : bool :=*)
(*  forallb (fun param => col f.(fn_entrypoint) param =?*)

Definition check_function (f :function) : bool :=
  true.
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

