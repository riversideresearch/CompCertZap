(** Faulty RISC-V semantics. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require Stacklayout.
Require Import Conventions.
Require Import Asm.

(**
We fault at most one register per (internal) function activation.

To limit faults, we maintain a stack of fault budgets, initializing a
callee's budget during [Pallocframe] and restoring its caller's budget
during [Pfreeframe]. Faults may arise when the budget at the top of
the stack is non-zero.

To relate our semantics to CompCert's RISC-V semantics, we maintain a
fault count that grows montonically with each injected fault. A run
under CompCert's semantics corresponds to a potentially faulty run
with no faults. (This is not strictly necessary.)
*)

Local Open Scope asm.

(**
RISC-V registers modeled by CompCert that lack replication. We never
fault these registers.

CONJECTURE: We could replicate and vote on some of these registers.
Imagine, for example, compiling with dedicated red, green, and blue
frame pointers to enable voting prior to reading or writing stack
slots.

Tolerating faults in PC seems more challenging. We could run our
concurrent threads in parallel on different cores. Voting would have
to involve communication (presumably via memory for error correction).
Moreover, the target program would have to detect and recover from
unexpected changes to PC.
*)

Definition unreplicated_regs : list preg :=
  PC ::
  (* X0 ::	(* always reads as zero, presumably cannot fault *) *)
  IR X1 ::	(* RA *)
  IR X2 ::	(* SP *)
  IR X3 ::	(* global pointer *)
  IR X4 ::	(* thread pointer *)
  IR X30 ::	(* FP? *)
  IR X31 ::	(* temporary used by [Asmgen], [exec_instr] *)
  nil.

Section SEM.

(**
Faulting values. Except for [Vundef], we preserve the value's
constructor (and thus typability). [Vundef] can fault to any value.
*)

Inductive fault_val: val -> val -> Prop :=
| fault_int i1 i2: fault_val (Vint i1) (Vint i2)
| fault_long i1 i2: fault_val (Vlong i1) (Vlong i2)
| fault_float f1 f2: fault_val (Vfloat f1) (Vfloat f2)
| fault_single f1 f2: fault_val (Vsingle f1) (Vsingle f2)
| fault_ptr b1 b2 o1 o2: fault_val (Vptr b1 o1) (Vptr b2 o2)
| fault_undef v: fault_val Vundef v.

(**
Optionally fault a register file. To fault, we pick a register and
change its contents. We do not fault [unreplicated_regs].
*)

Definition budgets: Type := list nat.
Definition count: Type := nat.

Inductive maybe_fault: budgets -> count -> regset -> budgets -> count -> regset -> Prop :=
| maybe_fault_refl bs c rs: maybe_fault bs c rs bs c rs
| maybe_fault_reg n bs c rs r v:
  ~ In r unreplicated_regs ->
  fault_val (rs r) v ->
  maybe_fault (Datatypes.S n :: bs) c rs (n :: bs) (Datatypes.S c) (rs # r <- v).

(**
Track internal function steps, pushing and popping fault budgets when
[exec_step_builtin] would execute [Pallocframe], [Pfreeframe].
*)

Variable ge: genv.

Definition set_activation_budgets (rs: regset) (m: mem) (bs: budgets) : option budgets :=
  let no_change := Some bs in
  match rs PC with
  | Vptr b ofs =>
    match Genv.find_funct_ptr ge b with
    | Some (Internal f) =>
      match find_instr (Ptrofs.unsigned ofs) f.(fn_code) with
      | Some i =>
        match i with
        | Pallocframe _ _ => Some (1%nat :: bs)
        | Pfreeframe _ _ =>
          match bs with
          | _ :: bs => Some bs
          | nil => None	(* Execution gets stuck *)
          end
        | _ => no_change
        end
      | None => no_change
      end
    | _ => no_change
    end
  | _ => no_change
  end.

(** Faulty execution of the instruction at [rs PC]. *)

Inductive state: Type :=
| State (bs: budgets) (c: nat) (rs: regset) (m: mem).

Inductive step: state -> trace -> state -> Prop :=
| exec_step bs c rs m bsf cf rsf t bs' rs' m':
  maybe_fault bs c rs bsf cf rsf ->
  set_activation_budgets rsf m bsf = Some bs' ->
  Asm.step ge (Asm.State rsf m) t (Asm.State rs' m') ->
  step (State bs c rs m) t (State bs' cf rs' m').

End SEM.

(** Faulty execution of whole programs. *)

Inductive initial_state (p: program): state -> Prop :=
| initial_state_intro bs0 c0 rs0 m0:
  bs0 = 1%nat :: nil ->
  c0 = 0%nat ->
  Asm.initial_state p (Asm.State rs0 m0) ->
  initial_state p (State bs0 c0 rs0 m0).

Inductive final_state: state -> int -> Prop :=
| final_state_intro bs c rs m r:
  Asm.final_state (Asm.State rs m) r ->
  final_state (State bs c rs m) r.

Definition semantics (p: program) : Smallstep.semantics :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).
