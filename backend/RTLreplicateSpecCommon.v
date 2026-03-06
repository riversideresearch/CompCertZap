(** * Shared tactics and definitions for DMR/TMR replication specs. *)

Require Import
  AST
  Coqlib
  Errors
  Globalenvs
  Integers
  Linking
  Maps
  Memory
  Op
  Registers
  RTLgen
  RTLtyping
  Smallstep
  Values
.
Require Import RTL.
Require Import Errors.
Import ListNotations.

Local Open Scope positive_scope.

(** ** Shared Ltac tactics for RTLgen state monad reasoning. **)

Ltac gen_contra :=
  try match goal with
  | [H: RTLgen.Error _ = RTLgen.OK _ _ _ |- _ ] => inv H
  | [H: RTLgen.OK _ _ _ = RTLgen.Error _ |- _ ] => inv H
  end.

Ltac gen_inv :=
  match goal with
  | [H: RTLgen.OK _ _ _ = RTLgen.OK _ _ _ |- _ ] => inv H
  end.

Ltac gen_case H :=
  match goal with
  | [ _: match ?X with
         | RTLgen.Error _ => _
         | RTLgen.OK _ _ _ => _ end = _ |- _ ] =>
      destruct X eqn:H
  end; gen_contra; try gen_inv.

Ltac egen_case :=
  let H := fresh "H" in
  gen_case H.

Ltac lr_case :=
  match goal with
  | [ _: match ?X with
         | left _ => _
         | right _ => _ end = _ |- _ ] =>
      destruct X
  end; gen_contra; try gen_inv.

Ltac reserve_instr_inv :=
  match goal with
  | [ H: reserve_instr ?s = RTLgen.OK ?n ?s' ?pf |- _ ] => inv H
  end.

Ltac state_incr_inv :=
  match goal with
  | [ H: state_incr ?s1 ?s2 |- _ ] => inv H
  end.

(** ** Shared type definitions. **)

Definition comp_of_typ (ty : typ) : comparison -> condition :=
  match ty with
  | Tint => Ccompu
  | Tlong => Ccomplu
  | Tsingle => Ccompfs
  | Tfloat => Ccompf
  | _ => Ccomp
  end.

Definition is_actual_type (ty : typ) : Prop :=
  match ty with
  | Tany32 => False
  | Tany64 => False
  | _ => True
  end.

(** ** Shared builtin_res utilities. **)

Inductive is_BR {A: Type} : builtin_res A -> Prop :=
| is_br_BR : forall x, is_BR (BR x).

Definition is_BR_dec {A : Type} (br : builtin_res A)
  : { is_BR br } + { ~ is_BR br }.
Proof.
  destruct br.
  - left; constructor.
  - right; intro H; inv H.
  - right; intro H; inv H.
Qed.

(** ** Shared register-usage definitions. **)

Inductive reg_used_in_instr (r : reg) : instruction -> Prop :=
| reg_used_Iop_args : forall op args res succ,
    In r args ->
    reg_used_in_instr r (Iop op args res succ)
| reg_used_Iop_res : forall op args succ,
    reg_used_in_instr r (Iop op args r succ)
| reg_used_Iload_args : forall chunk addr args res succ,
    In r args ->
    reg_used_in_instr r (Iload chunk addr args res succ)
| reg_used_Iload_res : forall chunk addr args succ,
    reg_used_in_instr r (Iload chunk addr args r succ)
| reg_used_Istore_args : forall chunk addr args src succ,
    In r args ->
    reg_used_in_instr r (Istore chunk addr args src succ)
| reg_used_Istore_src : forall chunk addr args succ,
    reg_used_in_instr r (Istore chunk addr args r succ)
| reg_used_Icall_fn : forall sig args dst succ,
    reg_used_in_instr r (Icall sig (inl r) args dst succ)
| reg_used_Icall_args : forall sig fn args dst succ,
    In r args ->
    reg_used_in_instr r (Icall sig fn args dst succ)
| reg_used_Icall_dst : forall sig fn args succ,
    reg_used_in_instr r (Icall sig fn args r succ)
| reg_used_Itailcall_fn : forall sig args,
    reg_used_in_instr r (Itailcall sig (inl r) args)
| reg_used_Itailcall_args : forall sig fn args,
    In r args ->
    reg_used_in_instr r (Itailcall sig fn args)
| reg_used_Ibuiltin_args : forall ef bargs bres succ,
    In r (regs_of_builtin_args bargs) ->
    reg_used_in_instr r (Ibuiltin ef bargs bres succ)
| reg_used_Ibuiltin_res : forall ef bargs succ,
    reg_used_in_instr r (Ibuiltin ef bargs (BR r) succ)
| reg_used_Icond : forall cond args ifso ifnot,
    In r args ->
    reg_used_in_instr r (Icond cond args ifso ifnot)
| reg_used_Ijumptable : forall tbl,
    reg_used_in_instr r (Ijumptable r tbl)
| reg_used_Ireturn :
  reg_used_in_instr r (Ireturn (Some r)).

Definition reg_used_in_code (c : code) (r : reg) : Prop :=
  exists pc instr,
    c! pc = Some instr /\ reg_used_in_instr r instr.

(** A register is 'used' in a function whenever it either appears in
    the function's parameter list or is used somewhere in its code. *)
Definition reg_used (params : list reg) (c : code) (r : reg) : Prop :=
  In r params \/ reg_used_in_code c r.
