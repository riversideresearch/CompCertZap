Require Import
  AST
  Builtins2
  Coqlib
  Errors
  Linking
  Maps
  Op
  RTL
  RTLagreement
  Smallstep
.
Import ListNotations.

Section CHECKER.

Definition check_instr (instr : instruction) : bool :=
  match instr with
  | Ibuiltin ef bargs bres succ =>
      negb (is_vote_builtinb ef) && negb (is_vote_runtimeb ef)
  | _ => true
  end.

(* Definition check_function (f : function) : Errors.res function := *)
(*   if PTree_Properties.for_all f.(fn_code) (fun _ instr => check_instr instr) then *)
(*     OK f *)
(*   else *)
(*     Error (msg "source program contains a vote builtin"). *)

Definition check_function (f : function) : bool :=
  PTree_Properties.for_all f.(fn_code) (fun _ instr => check_instr instr).

Definition check_program (p : program) : bool :=
  forallb (fun def => match snd def with
                   | Gfun (Internal f) => check_function f
                   | Gfun (External ef) =>
                       negb (is_vote_builtinb ef) && negb (is_vote_runtimeb ef)
                   | _ => true
                   end) p.(prog_defs).


(* Definition check_fundef (fd : fundef) : Errors.res fundef := *)
(*   AST.transf_partial_fundef check_function fd. *)

(* Definition check_program (p : program) : Errors.res program := *)
(*   transform_partial_program check_fundef p. *)

Definition transf_program (p : program) : Errors.res program :=
  if check_program p then
    OK p
  else
    Error (msg "source program contains a vote builtin").

End CHECKER.
