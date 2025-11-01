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

Inductive is_vote_builtin : external_function -> Prop :=
| is_vote_int : forall sg,
    is_vote_builtin (EF_builtin "__builtin_vote_int" sg)
| is_vote_long : forall sg,
    is_vote_builtin (EF_builtin "__builtin_vote_long" sg)
| is_vote_single : forall sg,
    is_vote_builtin (EF_builtin "__builtin_vote_single" sg)
| is_vote_float : forall sg,
    is_vote_builtin (EF_builtin "__builtin_vote_float" sg).

Section CHECKER.

Definition check_function (f : function) : Errors.res function :=
  OK f. (* TODO *)

Definition check_fundef (fd : fundef) : Errors.res fundef :=
  AST.transf_partial_fundef check_function fd.

Definition check_program (p : program) : Errors.res program :=
  transform_partial_program check_fundef p.

End CHECKER.
