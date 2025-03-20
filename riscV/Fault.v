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
Require Import Builtins.
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

NOTE: CompCert's model of RISC-V _assembly_ limits our fault model.
Several pseudo-instructions and builtins, for example, expand "behind
the scenes" to multiple ISA instructions. At this level of
abstraction, we cannot model faults within those instruction
sequences.
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

(**
Identifying instructions that tolerate faults to a given register.

The following do not tolerate faults:

- Indirect branches.

- Most conditional branches.

- Anything that impacts the trace (as such things cannot be
replicated), including external function calls and builtins for
volatile loads and stores.

- Pseudo-instructions and builtins whose expansions to the RISC-V ISA
are not fault tolerant. Such expansion happens in [Asmexpand],
[TargetPrinter], and the assembler. (We may be able to improve some
intolerant expansions.)

TODO:

- All non-volatile stores probably tolerate faults. We presently
regard stores as intolerant. This seems fishy given (1) the special
treatment of volatile loads and stores and (2) the fact that
[Asm.exec_instr] handles most store instructions (with out emitting an
event in the trace). It would certainly be simpler to regard all
non-volatile stores as fault tolerant.

- Stores to stack slots that arise from spilling a temporary probably
tolerate faults. They don't show up in the trace. Modulo assumptions
about coalescing stack slots, they are unique per redundant
computation.

- For calls to internal functions, we could presumably define and use
a "triple-based" calling convention. Calls to such functions could
tolerate faults, and such functions would not need to set up and tear
down redundant computations.
*)

Inductive tolerance: Type := Tolerant | Intolerant.

(*
Builtins use [known_builtin_sem] and don't impact the trace.
*)

Definition standard_builtin_tolerance (f: standard_builtin) : tolerance :=
  (*
  This is conservative.

  - A few builtins (e.g., [BI_select], [BI_fabs], [BI_fabsf]) should
  not arise because they are eliminated by [sel_known_builtin] during
  instruction selection.

  - Others (e.g., [BI_fsqrt]) have a semantics but no evident
  implementation, suggesting they are external functions.
  *)
  Intolerant.

Definition platform_builtin_tolerance (f: platform_builtin) : tolerance :=
  match f with
  end.

Definition smove_tolerance (r: preg)
    (args: list (builtin_arg preg))
    (res: builtin_res preg) :  tolerance :=
  (*
  Moves like <<green <- red>>, <<blue <- red>> for setting up
  redundant computations cannot tolerate faults in red.
  *)
  match args , res with
  | (BA src :: nil) , BR _ => if preg_eq r src then Intolerant else Tolerant
  | _ , _ => Intolerant	(* should not happen *)
  end.

Definition replicate_builtin_tolerance (r: preg) (f: replicate_builtin)
    (args: list (builtin_arg preg))
    (res: builtin_res preg) :  tolerance :=
  match f with

  | BI_smove_int
  | BI_smove_long
  | BI_smove_single
  | BI_smove_float
    => smove_tolerance r args res

  (*
  Voting can tolerate faults (despite the conditional branch) since we
  fault at most one register per function activation.
  *)

  | BI_vote_int
  | BI_vote_long
  | BI_vote_single
  | BI_vote_float
    => Tolerant

  end.

Definition builtin_function_tolerance (r: preg) (f: builtin_function)
    (args: list (builtin_arg preg))
    (res: builtin_res preg) :  tolerance :=
  match f with
  | BI_standard f => standard_builtin_tolerance f
  | BI_platform f => platform_builtin_tolerance f
  | BI_replicate f => replicate_builtin_tolerance r f args res
  end.

Definition external_function_tolerance (r: preg) (f: external_function)
    (args: list (builtin_arg preg))
    (res: builtin_res preg) :  tolerance :=
  match f with
  | EF_external _ _ => Intolerant

  | EF_builtin name sg
  | EF_runtime name sg =>
    match lookup_builtin_function name sg with
    | Some f => builtin_function_tolerance r f args res
    | None => Intolerant
    end

  (*
  TODO: We may be able to consider some volatile loads and stores
  tolerant (assuming we replicate them) because they impact the trace
  only when the target block statisfies <<Senv.block_is_volatile>>.
  See [volatile_load], [volatile_store].
  *)
  | EF_vload _
  | EF_vstore _
    => Intolerant

  (*
  TODO: We may be able to define fault tolerant implementations of a
  few of these externals (e.g., a version of [EF_memcpy] with a
  "triples" calling convention).
  *)
  | EF_malloc
  | EF_free
  | EF_memcpy _ _
  | EF_annot _ _ _
  | EF_annot_val _ _ _
  | EF_inline_asm _ _ _
    => Intolerant

  (*
  TODO: We may be able to improve here.
  *)
  | EF_debug _ _ _  => Intolerant

  end.

Definition conditional_branch_tolerance (r1 r2 : ireg0) : tolerance :=
  (*
  We could go further by accounting for [unreplicated_regs]. A branch
  based on comparing two registers we never fault, for example, (or
  one such register and X0) tolerates faults.
  *)
  if ireg0_eq r1 r2 then Tolerant else Intolerant.

Definition instruction_tolerance (r: preg) (i: instruction) : tolerance :=
  match i with
  | Pmv _ _ => Tolerant

(* 32-bit integer register-immediate instructions *)
  | Paddiw _ _ _
  | Psltiw _ _ _
  | Psltiuw _ _ _
  | Pandiw _ _ _
  | Poriw _ _ _
  | Pxoriw _ _ _
  | Pslliw _ _ _
  | Psrliw _ _ _
  | Psraiw _ _ _
  | Pluiw _ _
    => Tolerant

(* 32-bit integer register-register instructions *)
  | Paddw _ _ _
  | Psubw _ _ _
  | Pmulw _ _ _
  | Pmulhw _ _ _
  | Pmulhuw _ _ _
  | Pdivw _ _ _
  | Pdivuw _ _ _
  | Premw _ _ _
  | Premuw _ _ _
  | Psltw _ _ _
  | Psltuw _ _ _
  | Pseqw _ _ _
  | Psnew _ _ _
  | Pandw _ _ _
  | Porw _ _ _
  | Pxorw _ _ _
  | Psllw _ _ _
  | Psrlw _ _ _
  | Psraw _ _ _
    => Tolerant

(* 64-bit integer register-immediate instructions *)
  | Paddil _ _ _
  | Psltil _ _ _
  | Psltiul _ _ _
  | Pandil _ _ _
  | Poril _ _ _
  | Pxoril _ _ _
  | Psllil _ _ _
  | Psrlil _ _ _
  | Psrail _ _ _
  | Pluil _ _
    => Tolerant

(* 64-bit integer register-register instructions *)
  | Paddl _ _ _
  | Psubl _ _ _
  | Pmull _ _ _
  | Pmulhl _ _ _
  | Pmulhul _ _ _
  | Pdivl _ _ _
  | Pdivul _ _ _
  | Preml _ _ _
  | Premul _ _ _
  | Psltl _ _ _
  | Psltul _ _ _
  | Pseql _ _ _
  | Psnel _ _ _
  | Pandl _ _ _
  | Porl _ _ _
  | Pxorl _ _ _
  | Pslll _ _ _
  | Psrll _ _ _
  | Psral _ _ _
  | Pcvtl2w _ _
  | Pcvtw2l _
    => Tolerant

(* Unconditional jumps.  Links are always to X1/RA. *)

  | Pj_l _
  | Pj_s _ _
  | Pjal_s _ _
    => Tolerant

  (**
  We cannot tolerate faults in indirect jumps.
  *)

  | Pj_r _ _
  | Pjal_r _ _
    => Intolerant

(* Conditional branches, 32-bit comparisons *)
  | Pbeqw r1 r2 _
  | Pbnew r1 r2 _
  | Pbltw r1 r2 _
  | Pbltuw r1 r2 _
  | Pbgew r1 r2 _
  | Pbgeuw r1 r2 _
    => conditional_branch_tolerance r1 r2

(* Conditional branches, 64-bit comparisons *)
  | Pbeql r1 r2 _
  | Pbnel r1 r2 _
  | Pbltl r1 r2 _
  | Pbltul r1 r2 _
  | Pbgel r1 r2 _
  | Pbgeul r1 r2 _
    => conditional_branch_tolerance r1 r2

(* Loads *)
  | Plb _ _ _
  | Plbu _ _ _
  | Plh _ _ _
  | Plhu _ _ _
  | Plw _ _ _
  | Plw_a _ _ _
  | Pld _ _ _
  | Pld_a _ _ _
    => Tolerant

(* Stores *)
  | Psb _ _ _
  | Psh _ _ _
  | Psw _ _ _
  | Psw_a _ _ _
  | Psd _ _ _
  | Psd_a _ _ _
    => Intolerant

(* Synchronization *)
  | Pfence
    => Tolerant

(* floating point register move *)
  | Pfmv _ _
  | Pfmvxs _ _
  | Pfmvsx _ _
  | Pfmvxd _ _
  | Pfmvdx _ _
    => Tolerant

(* 32-bit (single-precision) floating point *)
  | Pfls _ _ _ => Tolerant	(* load *)
  | Pfss _ _ _ => Intolerant	(* store *)
  | Pfnegs _ _
  | Pfabss _ _
  | Pfadds _ _ _
  | Pfsubs _ _ _
  | Pfmuls _ _ _
  | Pfdivs _ _ _
  | Pfmins _ _ _
  | Pfmaxs _ _ _
  | Pfeqs _ _ _
  | Pflts _ _ _
  | Pfles _ _ _
  | Pfsqrts _ _
  | Pfmadds _ _ _ _
  | Pfmsubs _ _ _ _
  | Pfnmadds _ _ _ _
  | Pfnmsubs _ _ _ _
  | Pfcvtws _ _
  | Pfcvtwus _ _
  | Pfcvtsw _ _
  | Pfcvtswu _ _
  | Pfcvtls _ _
  | Pfcvtlus _ _
  | Pfcvtsl _ _
  | Pfcvtslu _ _
    => Tolerant

(* 64-bit (double-precision) floating point *)
  | Pfld _ _ _ | Pfld_a _ _ _ => Tolerant	(* loads *)
  | Pfsd _ _ _ | Pfsd_a _ _ _ => Intolerant	(* stores *)
  | Pfnegd _ _
  | Pfabsd _ _
  | Pfaddd _ _ _
  | Pfsubd _ _ _
  | Pfmuld _ _ _
  | Pfdivd _ _ _
  | Pfmind _ _ _
  | Pfmaxd _ _ _
  | Pfeqd _ _ _
  | Pfltd _ _ _
  | Pfled _ _ _
  | Pfsqrtd _ _
  | Pfmaddd _ _ _ _
  | Pfmsubd _ _ _ _
  | Pfnmaddd _ _ _ _
  | Pfnmsubd _ _ _ _
  | Pfcvtwd _ _
  | Pfcvtwud _ _
  | Pfcvtdw _ _
  | Pfcvtdwu _ _
  | Pfcvtld _ _
  | Pfcvtlud _ _
  | Pfcvtdl _ _
  | Pfcvtdlu _ _
  | Pfcvtds _ _
  | Pfcvtsd _ _
    => Tolerant

(* Pseudo-instructions *)

  (*
  We never fault X30, X2.
  *)
  | Pallocframe _ _ | Pfreeframe _ _ => Tolerant

  (*
  A directive, not code.
  *)
  | Plabel _ => Tolerant

  (*
  These variations on "load immediate" all expand into sequences like
  load high bits, add low bits. Some may depend on the global pointer
  X3, which we never fault. Some depend on X31, which we never fault.
  *)
  | Ploadsymbol _ _ _
  | Ploadsymbol_high _ _ _
  | Ploadli _ _
  | Ploadfi _ _
  | Ploadsi _ _
    => Tolerant

  (*
  X5 (the branch target after expansion) is a single point of failure,
  and we can fault it.
  *)
  | Pbtbl _ _ => Intolerant

  | Pbuiltin f args dest => external_function_tolerance r f args dest

  | Pnop => Tolerant

  (*
  These are directives, not code.
  *)
  | Pcfi_rel_offset _ | Pcfi_adjust _ => Tolerant

end.

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

Variable ge: genv.

Definition internal_instruction (rs: regset) (m: mem) : option instruction :=
  match rs PC with
  | Vptr b ofs =>
    match Genv.find_funct_ptr ge b with
    | Some (Internal f) => find_instr (Ptrofs.unsigned ofs) f.(fn_code)
    | _ => None
    end
  | _ => None
  end.

Definition internal_instruction_tolance (rs: regset) (m: mem) (r: preg) : tolerance :=
  match internal_instruction rs m with
  | Some i => instruction_tolerance r i
  | None => Intolerant
  end.

Inductive maybe_fault: budgets -> count -> regset -> mem -> budgets -> count -> regset -> Prop :=
| maybe_fault_refl bs c rs m: maybe_fault bs c rs m bs c rs
| maybe_fault_reg n bs c rs m r v:
  ~ In r unreplicated_regs ->
  internal_instruction_tolance rs m r = Tolerant ->
  fault_val (rs r) v ->
  maybe_fault (Datatypes.S n :: bs) c rs m (n :: bs) (Datatypes.S c) (rs # r <- v).

(**
Track internal function steps, pushing and popping fault budgets when
[exec_step_builtin] would execute [Pallocframe], [Pfreeframe].
*)

Definition set_activation_budgets (rs: regset) (m: mem) (bs: budgets) : option budgets :=
  let no_change := Some bs in
  match internal_instruction rs m with
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
  end.

(** Faulty execution of the instruction at [rs PC]. *)

Inductive state: Type :=
| State (bs: budgets) (c: nat) (rs: regset) (m: mem).

Inductive step: state -> trace -> state -> Prop :=
| exec_step bs c rs m bsf cf rsf t bs' rs' m':
  maybe_fault bs c rs m bsf cf rsf ->
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
