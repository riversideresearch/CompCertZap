(** Fault tolerance for RISC-V programs. *)

Require Import Coqlib.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Behaviors.
Require Asm.
Require Fault.

(**
A RISC-V program is fault tolerant if all of its behaviors under our
faulty semantics are also behaviors under the fault-free semantics.
*)
Definition fault_tolerant (p : Asm.program) : Prop :=
  forall beh,
  program_behaves (Fault.semantics p) beh ->
  program_behaves (Asm.semantics p) beh.
