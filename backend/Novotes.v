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

Definition check_function (f : function) : Errors.res function :=
  OK f. (* TODO *)

Definition check_fundef (fd : fundef) : Errors.res fundef :=
  AST.transf_partial_fundef check_function fd.

Definition check_program (p : program) : Errors.res program :=
  transform_partial_program check_fundef p.

End CHECKER.
