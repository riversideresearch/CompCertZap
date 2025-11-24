(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** The RTL intermediate language: abstract syntax and semantics.

  RTL stands for "Register Transfer Language". This is the first
  intermediate language after Cminor and CminorSel.
*)

Require Import Coqlib Maps.
Require Import AST Linking Integers Values Builtins Events Memory Globalenvs Smallstep.
Require Import Op Registers.

(** * Abstract syntax *)

(** RTL is organized as instructions, functions and programs.
  Instructions correspond roughly to elementary instructions of the
  target processor, but take their arguments and leave their results
  in pseudo-registers (also called temporaries in textbooks).
  Infinitely many pseudo-registers are available, and each function
  has its own set of pseudo-registers, unaffected by function calls.

  Instructions are organized as a control-flow graph: a function is
  a finite map from ``nodes'' (abstract program points) to instructions,
  and each instruction lists explicitly the nodes of its successors.
*)

Definition node := positive.

Inductive instruction: Type :=
  | Inop: node -> instruction
      (** No operation -- just branch to the successor. *)
  | Iop: operation -> list reg -> reg -> node -> instruction
      (** [Iop op args dest succ] performs the arithmetic operation [op]
          over the values of registers [args], stores the result in [dest],
          and branches to [succ]. *)
  | Iload: memory_chunk -> addressing -> list reg -> reg -> node -> instruction
      (** [Iload chunk addr args dest succ] loads a [chunk] quantity from
          the address determined by the addressing mode [addr] and the
          values of the [args] registers, stores the quantity just read
          into [dest], and branches to [succ]. *)
  | Istore: memory_chunk -> addressing -> list reg -> reg -> node -> instruction
      (** [Istore chunk addr args src succ] stores the value of register
          [src] in the [chunk] quantity at the
          the address determined by the addressing mode [addr] and the
          values of the [args] registers, then branches to [succ]. *)
  | Icall: signature -> reg + ident -> list reg -> reg -> node -> instruction
      (** [Icall sig fn args dest succ] invokes the function determined by
          [fn] (either a function pointer found in a register or a
          function name), giving it the values of registers [args]
          as arguments.  It stores the return value in [dest] and branches
          to [succ]. *)
  | Itailcall: signature -> reg + ident -> list reg -> instruction
      (** [Itailcall sig fn args] performs a function invocation
          in tail-call position.  *)
  | Ibuiltin: external_function -> list (builtin_arg reg) -> builtin_res reg -> node -> instruction
      (** [Ibuiltin ef args dest succ] calls the built-in function
          identified by [ef], giving it the values of [args] as arguments.
          It stores the return value in [dest] and branches to [succ]. *)
  | Icond: condition -> list reg -> node -> node -> instruction
      (** [Icond cond args ifso ifnot] evaluates the boolean condition
          [cond] over the values of registers [args].  If the condition
          is true, it transitions to [ifso].  If the condition is false,
          it transitions to [ifnot]. *)
  | Ijumptable: reg -> list node -> instruction
      (** [Ijumptable arg tbl] transitions to the node that is the [n]-th
          element of the list [tbl], where [n] is the unsigned integer
          value of register [arg]. *)
  | Ireturn: option reg -> instruction.
      (** [Ireturn] terminates the execution of the current function
          (it has no successor).  It returns the value of the given
          register, or [Vundef] if none is given. *)

Definition code: Type := PTree.t instruction.

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_params: list reg;
  fn_stacksize: Z;
  fn_code: code;
  fn_entrypoint: node
}.

(** A function description comprises a control-flow graph (CFG) [fn_code]
    (a partial finite mapping from nodes to instructions).  As in Cminor,
    [fn_sig] is the function signature and [fn_stacksize] the number of bytes
    for its stack-allocated activation record.  [fn_params] is the list
    of registers that are bound to the values of arguments at call time.
    [fn_entrypoint] is the node of the first instruction of the function
    in the CFG. *)

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

(** * Operational semantics *)

Definition genv := Genv.t fundef unit.
Definition regset := Regmap.t val.

Fixpoint init_regs (vl: list val) (rl: list reg) {struct rl} : regset :=
  match rl, vl with
  | r1 :: rs, v1 :: vs => Regmap.set r1 v1 (init_regs vs rs)
  | _, _ => Regmap.init Vundef
  end.

(** The dynamic semantics of RTL is given in small-step style, as a
  set of transitions between states.  A state captures the current
  point in the execution.  Three kinds of states appear in the transitions:

- [State cs f sp pc rs m] describes an execution point within a function.
  [f] is the current function.
  [sp] is the pointer to the stack block for its current activation
     (as in Cminor).
  [pc] is the current program point (CFG node) within the code [c].
  [rs] gives the current values for the pseudo-registers.
  [m] is the current memory state.
- [Callstate cs f args m] is an intermediate state that appears during
  function calls.
  [f] is the function definition that we are calling.
  [args] (a list of values) are the arguments for this call.
  [m] is the current memory state.
- [Returnstate cs v m] is an intermediate state that appears when a
  function terminates and returns to its caller.
  [v] is the return value and [m] the current memory state.

In all three kinds of states, the [cs] parameter represents the call stack.
It is a list of frames [Stackframe res f sp pc rs].  Each frame represents
a function call in progress.
[res] is the pseudo-register that will receive the result of the call.
[f] is the calling function.
[sp] is its stack pointer.
[pc] is the program point for the instruction that follows the call.
[rs] is the state of registers in the calling function.
*)

Inductive stackframe : Type :=
  | Stackframe:
      forall (res: reg)            (**r where to store the result *)
             (f: function)         (**r calling function *)
             (sp: val)             (**r stack pointer in calling function *)
             (pc: node)            (**r program point in calling function *)
             (rs: regset),         (**r register state in calling function *)
      stackframe.

Inductive state : Type :=
  | State:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r current function *)
             (sp: val)                (**r stack pointer *)
             (pc: node)               (**r current program point in [c] *)
             (rs: regset)             (**r register state *)
             (m: mem),                (**r memory state *)
      state
  | Callstate:
      forall (stack: list stackframe) (**r call stack *)
             (f: fundef)              (**r function to call *)
             (args: list val)         (**r arguments to the call *)
             (m: mem),                (**r memory state *)
      state
  | Returnstate:
      forall (stack: list stackframe) (**r call stack *)
             (v: val)                 (**r return value for the call *)
             (m: mem),                (**r memory state *)
      state.

Section VOTE.
Context {VT: Builtins2.vote_type} {vsem: Builtins2.VoteSemantics VT}.

Section RELSEM.

Variable ge: genv.

Definition find_function
      (ros: reg + ident) (rs: regset) : option fundef :=
  match ros with
  | inl r => Genv.find_funct ge rs#r
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

(** The transitions are presented as an inductive predicate
  [step ge st1 t st2], where [ge] is the global environment,
  [st1] the initial state, [st2] the final state, and [t] the trace
  of system calls performed during this transition. *)

Inductive step: state -> trace -> state -> Prop :=
  | exec_Inop:
      forall s f sp pc rs m pc',
      (fn_code f)!pc = Some(Inop pc') ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' rs m)
  | exec_Iop:
      forall s f sp pc rs m op args res pc' v,
      (fn_code f)!pc = Some(Iop op args res pc') ->
      eval_operation ge sp op rs##args m = Some v ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' (rs#res <- v) m)
  | exec_Iload:
      forall s f sp pc rs m chunk addr args dst pc' a v,
      (fn_code f)!pc = Some(Iload chunk addr args dst pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' (rs#dst <- v) m)
  | exec_Istore:
      forall s f sp pc rs m chunk addr args src pc' a m',
      (fn_code f)!pc = Some(Istore chunk addr args src pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a rs#src = Some m' ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' rs m')
  | exec_Icall:
      forall s f sp pc rs m sig ros args res pc' fd,
      (fn_code f)!pc = Some(Icall sig ros args res pc') ->
      find_function ros rs = Some fd ->
      funsig fd = sig ->
      step (State s f sp pc rs m)
        E0 (Callstate (Stackframe res f sp pc' rs :: s) fd rs##args m)
  | exec_Itailcall:
      forall s f stk pc rs m sig ros args fd m',
      (fn_code f)!pc = Some(Itailcall sig ros args) ->
      find_function ros rs = Some fd ->
      funsig fd = sig ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (State s f (Vptr stk Ptrofs.zero) pc rs m)
        E0 (Callstate s fd rs##args m')
  | exec_Ibuiltin:
      forall s f sp pc rs m ef args res pc' vargs t vres m',
      (fn_code f)!pc = Some(Ibuiltin ef args res pc') ->
      eval_builtin_args ge (fun r => rs#r) sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      step (State s f sp pc rs m)
         t (State s f sp pc' (regmap_setres res vres rs) m')
  | exec_Icond:
      forall s f sp pc rs m cond args ifso ifnot b pc',
      (fn_code f)!pc = Some(Icond cond args ifso ifnot) ->
      eval_condition cond rs##args m = Some b ->
      pc' = (if b then ifso else ifnot) ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' rs m)
  | exec_Ijumptable:
      forall s f sp pc rs m arg tbl n pc',
      (fn_code f)!pc = Some(Ijumptable arg tbl) ->
      rs#arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some pc' ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' rs m)
  | exec_Ireturn:
      forall s f stk pc rs m or m',
      (fn_code f)!pc = Some(Ireturn or) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (State s f (Vptr stk Ptrofs.zero) pc rs m)
        E0 (Returnstate s (regmap_optget or Vundef rs) m')
  | exec_function_internal:
      forall s f args m m' stk,
      Val.has_argtype_list args f.(fn_sig).(sig_args) ->
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      step (Callstate s (Internal f) args m)
        E0 (State s
                  f
                  (Vptr stk Ptrofs.zero)
                  f.(fn_entrypoint)
                  (init_regs args f.(fn_params))
                  m')
  | exec_function_external:
      forall s ef args res t m m',
      external_call ef ge args m t res m' ->
      step (Callstate s (External ef) args m)
         t (Returnstate s res m')
  | exec_return:
      forall res f sp pc rs s vres m,
      step (Returnstate (Stackframe res f sp pc rs :: s) vres m)
        E0 (State s f sp pc (rs#res <- vres) m).

Lemma exec_Iop':
  forall s f sp pc rs m op args res pc' rs' v,
  (fn_code f)!pc = Some(Iop op args res pc') ->
  eval_operation ge sp op rs##args m = Some v ->
  rs' = (rs#res <- v) ->
  step (State s f sp pc rs m)
    E0 (State s f sp pc' rs' m).
Proof.
  intros. subst rs'. eapply exec_Iop; eauto.
Qed.

Lemma exec_Iload':
  forall s f sp pc rs m chunk addr args dst pc' rs' a v,
  (fn_code f)!pc = Some(Iload chunk addr args dst pc') ->
  eval_addressing ge sp addr rs##args = Some a ->
  Mem.loadv chunk m a = Some v ->
  rs' = (rs#dst <- v) ->
  step (State s f sp pc rs m)
    E0 (State s f sp pc' rs' m).
Proof.
  intros. subst rs'. eapply exec_Iload; eauto.
Qed.

End RELSEM.

(** Execution of whole programs are described as sequences of transitions
  from an initial state to a final state.  An initial state is a [Callstate]
  corresponding to the invocation of the ``main'' function of the program
  without arguments and with an empty call stack. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = signature_main ->
      initial_state p (Callstate nil f nil m0).

(** A final state is a [Returnstate] with an empty call stack. *)

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (Returnstate nil (Vint r) m) r.

(** The small-step semantics for a program. *)

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

(** This semantics is receptive to changes in events. *)

Lemma semantics_receptive:
  forall (p: program), receptive (semantics p).
Proof.
  intros. constructor; simpl; intros.
(* receptiveness *)
  assert (t1 = E0 -> exists s2, step (Genv.globalenv p) s t2 s2).
    intros. subst. inv H0. exists s1; auto.
  inversion H; subst; auto.
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
  exists (State s0 f sp pc' (regmap_setres res vres2 rs) m2). eapply exec_Ibuiltin; eauto.
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
  exists (Returnstate s0 vres2 m2). econstructor; eauto.
(* trace length *)
  red; intros; inv H; simpl; try lia.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
Qed.

(* Derived from x86 [Asm.semantics_determinate]. *)
Lemma semantics_determinate :
  forall p, determinate (semantics p).
Proof.
  Ltac Equalities :=
    match goal with
    | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
        rewrite H1 in H2; inv H2; Equalities
    | _ => idtac
    end.
  intros; constructor; simpl; intros.
  - (* determ *)
    inv H; inv H0; Equalities; try solve [split; try constructor; auto].
    + assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0.
      exploit external_call_determ. eexact H3. eexact H13. intros [A B].
      split. auto. intros. destruct B; auto. subst. auto.
    + exploit external_call_determ. eexact H1. eexact H7. intros [A B].
      split. auto. intros. destruct B; auto. subst. auto.
  - (* trace length *)
    red; intros; inv H; simpl; try lia.
    eapply external_call_trace_length; eauto.
    eapply external_call_trace_length; eauto.
  - (* initial states *)
    inv H; inv H0.
    unfold ge in *.
    unfold ge0 in *.
    f_equal; congruence.    
  - (* final no step *)
    assert (NOTNULL: forall b ofs, Vnullptr <> Vptr b ofs).
    { intros; unfold Vnullptr; destruct Archi.ptr64; congruence. }
    inv H. red; intros; red; intros. inv H; rewrite H0 in *; eelim NOTNULL; eauto.
  - (* final states *)
    inv H; inv H0. congruence.
Qed.

(** * Operations on RTL abstract syntax *)

(** Transformation of a RTL function instruction by instruction.
  This applies a given transformation function to all instructions
  of a function and constructs a transformed function from that. *)

Section TRANSF.

Variable transf: node -> instruction -> instruction.

Definition transf_function (f: function) : function :=
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    (PTree.map transf f.(fn_code))
    f.(fn_entrypoint).

End TRANSF.

(** Computation of the possible successors of an instruction.
  This is used in particular for dataflow analyses. *)

Definition successors_instr (i: instruction) : list node :=
  match i with
  | Inop s => s :: nil
  | Iop op args res s => s :: nil
  | Iload chunk addr args dst s => s :: nil
  | Istore chunk addr args src s => s :: nil
  | Icall sig ros args res s => s :: nil
  | Itailcall sig ros args => nil
  | Ibuiltin ef args res s => s :: nil
  | Icond cond args ifso ifnot => ifso :: ifnot :: nil
  | Ijumptable arg tbl => tbl
  | Ireturn optarg => nil
  end.

Definition successors_map (f: function) : PTree.t (list node) :=
  PTree.map1 successors_instr f.(fn_code).

(** The registers used by an instruction *)

Definition instr_uses (i: instruction) : list reg :=
  match i with
  | Inop s => nil
  | Iop op args res s => args
  | Iload chunk addr args dst s => args
  | Istore chunk addr args src s => src :: args
  | Icall sig (inl r) args res s => r :: args
  | Icall sig (inr id) args res s => args
  | Itailcall sig (inl r) args => r :: args
  | Itailcall sig (inr id) args => args
  | Ibuiltin ef args res s => params_of_builtin_args args
  | Icond cond args ifso ifnot => args
  | Ijumptable arg tbl => arg :: nil
  | Ireturn None => nil
  | Ireturn (Some arg) => arg :: nil
  end.

(** The register defined by an instruction, if any *)

Definition instr_defs (i: instruction) : option reg :=
  match i with
  | Inop s => None
  | Iop op args res s => Some res
  | Iload chunk addr args dst s => Some dst
  | Istore chunk addr args src s => None
  | Icall sig ros args res s => Some res
  | Itailcall sig ros args => None
  | Ibuiltin ef args res s =>
      match res with BR r => Some r | _ => None end
  | Icond cond args ifso ifnot => None
  | Ijumptable arg tbl => None
  | Ireturn optarg => None
  end.

(** Maximum PC (node number) in the CFG of a function.  All nodes of
  the CFG of [f] are between 1 and [max_pc_function f] (inclusive). *)

Definition max_pc_function (f: function) :=
  PTree.fold (fun m pc i => Pos.max m pc) f.(fn_code) 1%positive.

Lemma max_pc_function_sound:
  forall f pc i, f.(fn_code)!pc = Some i -> Ple pc (max_pc_function f).
Proof.
  intros until i. unfold max_pc_function.
  apply PTree_Properties.fold_rec with (P := fun c m => c!pc = Some i -> Ple pc m).
  (* extensionality *)
  intros. apply H0. rewrite H; auto.
  (* base case *)
  rewrite PTree.gempty. congruence.
  (* inductive case *)
  intros. rewrite PTree.gsspec in H2. destruct (peq pc k).
  inv H2. extlia.
  apply Ple_trans with a. auto. extlia.
Qed.

(** Maximum pseudo-register mentioned in a function.  All results or arguments
  of an instruction of [f], as well as all parameters of [f], are between
  1 and [max_reg_function] (inclusive). *)

Definition max_reg_instr (m: positive) (pc: node) (i: instruction) :=
  match i with
  | Inop s => m
  | Iop op args res s => fold_left Pos.max args (Pos.max res m)
  | Iload chunk addr args dst s => fold_left Pos.max args (Pos.max dst m)
  | Istore chunk addr args src s => fold_left Pos.max args (Pos.max src m)
  | Icall sig (inl r) args res s => fold_left Pos.max args (Pos.max r (Pos.max res m))
  | Icall sig (inr id) args res s => fold_left Pos.max args (Pos.max res m)
  | Itailcall sig (inl r) args => fold_left Pos.max args (Pos.max r m)
  | Itailcall sig (inr id) args => fold_left Pos.max args m
  | Ibuiltin ef args res s =>
      fold_left Pos.max (params_of_builtin_args args)
        (fold_left Pos.max (params_of_builtin_res res) m)
  | Icond cond args ifso ifnot => fold_left Pos.max args m
  | Ijumptable arg tbl => Pos.max arg m
  | Ireturn None => m
  | Ireturn (Some arg) => Pos.max arg m
  end.

Definition max_reg_function (f: function) :=
  Pos.max
    (PTree.fold max_reg_instr f.(fn_code) 1%positive)
    (fold_left Pos.max f.(fn_params) 1%positive).

Remark max_reg_instr_ge:
  forall m pc i, Ple m (max_reg_instr m pc i).
Proof.
  intros.
  assert (X: forall l n, Ple m n -> Ple m (fold_left Pos.max l n)).
  { induction l; simpl; intros.
    auto.
    apply IHl. extlia. }
  destruct i; simpl; try (destruct s0); repeat (apply X); try extlia.
  destruct o; extlia.
Qed.

Remark max_reg_instr_def:
  forall m pc i r, instr_defs i = Some r -> Ple r (max_reg_instr m pc i).
Proof.
  intros.
  assert (X: forall l n, Ple r n -> Ple r (fold_left Pos.max l n)).
  { induction l; simpl; intros. extlia. apply IHl. extlia. }
  destruct i; simpl in *; inv H.
- apply X. extlia.
- apply X. extlia.
- destruct s0; apply X; extlia.
- destruct b; inv H1. apply X. simpl. extlia.
Qed.

Remark max_reg_instr_uses:
  forall m pc i r, In r (instr_uses i) -> Ple r (max_reg_instr m pc i).
Proof.
  intros.
  assert (X: forall l n, In r l \/ Ple r n -> Ple r (fold_left Pos.max l n)).
  { induction l; simpl; intros.
    tauto.
    apply IHl. destruct H0 as [[A|A]|A]. right; subst; extlia. auto. right; extlia. }
  destruct i; simpl in *; try (destruct s0); try (apply X; auto).
- contradiction.
- destruct H. right; subst; extlia. auto.
- destruct H. right; subst; extlia. auto.
- destruct H. right; subst; extlia. auto.
- intuition. subst; extlia.
- destruct o; simpl in H; intuition. subst; extlia.
Qed.

Lemma max_reg_function_def:
  forall f pc i r,
  f.(fn_code)!pc = Some i -> instr_defs i = Some r -> Ple r (max_reg_function f).
Proof.
  intros.
  assert (Ple r (PTree.fold max_reg_instr f.(fn_code) 1%positive)).
  {  revert H.
     apply PTree_Properties.fold_rec with
       (P := fun c m => c!pc = Some i -> Ple r m).
   - intros. rewrite H in H1; auto.
   - rewrite PTree.gempty; congruence.
   - intros. rewrite PTree.gsspec in H3. destruct (peq pc k).
     + inv H3. eapply max_reg_instr_def; eauto.
     + apply Ple_trans with a. auto. apply max_reg_instr_ge.
  }
  unfold max_reg_function. extlia.
Qed.

Lemma max_reg_function_use:
  forall f pc i r,
  f.(fn_code)!pc = Some i -> In r (instr_uses i) -> Ple r (max_reg_function f).
Proof.
  intros.
  assert (Ple r (PTree.fold max_reg_instr f.(fn_code) 1%positive)).
  {  revert H.
     apply PTree_Properties.fold_rec with
       (P := fun c m => c!pc = Some i -> Ple r m).
   - intros. rewrite H in H1; auto.
   - rewrite PTree.gempty; congruence.
   - intros. rewrite PTree.gsspec in H3. destruct (peq pc k).
     + inv H3. eapply max_reg_instr_uses; eauto.
     + apply Ple_trans with a. auto. apply max_reg_instr_ge.
  }
  unfold max_reg_function. extlia.
Qed.

Lemma max_reg_function_params:
  forall f r, In r f.(fn_params) -> Ple r (max_reg_function f).
Proof.
  intros.
  assert (X: forall l n, In r l \/ Ple r n -> Ple r (fold_left Pos.max l n)).
  { induction l; simpl; intros.
    tauto.
    apply IHl. destruct H0 as [[A|A]|A]. right; subst; extlia. auto. right; extlia. }
  assert (Y: Ple r (fold_left Pos.max f.(fn_params) 1%positive)).
  { apply X; auto. }
  unfold max_reg_function. extlia.
Qed.

(** Recognition of function calls to runtime functions with known semantics. *)

Definition defmap := PTree.t (globdef fundef unit).

Definition is_known_runtime_function (dm: defmap) (ros: reg + ident) : option builtin_function :=
  match ros with
  | inl r => None
  | inr id =>
      match dm!id with
      | Some(Gfun(External(EF_runtime name sg))) => lookup_builtin_function name sg
      | _ => None
      end
  end.

Lemma is_known_runtime_function_sound:
  forall cu prog ros bf rs fd,
  is_known_runtime_function (prog_defmap cu) ros = Some bf ->
  linkorder cu prog ->
  find_function (Genv.globalenv prog) ros rs = Some fd ->
  exists name sg, fd = External(EF_runtime name sg)
               /\ lookup_builtin_function name sg = Some bf.
Proof.
  unfold is_known_runtime_function; intros.
  destruct ros as [r|id]; try discriminate.
  destruct (prog_defmap cu)!id as [gd|] eqn:D; try discriminate.
  destruct gd as [f|v]; try discriminate.
  destruct f as [f|ef]; try discriminate.
  destruct ef; try discriminate.
  exploit (prog_defmap_linkorder cu prog); eauto.
  intros (gd & D2 & LD). inv LD. inv H3.
  apply Genv.find_def_symbol in D2. fold ge in D2. destruct D2 as (b & F1 & F2).
  simpl in H1. rewrite F1 in H1. apply Genv.find_funct_ptr_iff in H1.
  exists name, sg; intuition congruence.
Qed. 

End VOTE.


(** Helpers for CompCertZap *)

Fixpoint regs_of_builtin_arg (arg : builtin_arg reg) : list reg :=
  match arg with
  | BA r => r :: nil
  | BA_splitlong hi lo => regs_of_builtin_arg hi ++ regs_of_builtin_arg lo
  | BA_addptr a1 a2 => regs_of_builtin_arg a1 ++ regs_of_builtin_arg a2
  | _ => nil
  end.

(** Pull out registers from builtin_args. *)
Fixpoint regs_of_builtin_args (args : list (builtin_arg reg)) : list reg :=
  match args with
  | nil => nil
  | ba :: rest => regs_of_builtin_arg ba ++ regs_of_builtin_args rest
  end.

Definition regs_of_fn (fn : reg + ident) : list reg :=
  match fn with
  | inl r => r :: nil
  | inr _ => nil
  end.

Definition args_of_instruction (instr : instruction) : list reg :=
  match instr with
  | Inop _ => nil
  | Iop _ args _ _ => args
  | Iload _  _ args _ _ => args
  | Istore _ _ args src _ => src :: args
  | Icall _ fn args _ _ => regs_of_fn fn ++ args
  | Itailcall _ fn args => regs_of_fn fn ++ args
  | Ibuiltin _ args _ _ => regs_of_builtin_args args
  | Icond _ args _ _ => args
  | Ijumptable arg _ => arg :: nil
  | Ireturn (Some r) => r :: nil
  | Ireturn None => nil
  end.

Definition inb (p : positive) (l : list positive) : bool :=
  existsb (fun x => Pos.eqb x p) l.

Lemma inb_spec (p : positive) (l : list positive) :
  reflect (In p l) (inb p l).
Proof.
  revert p; induction l; intros; simpl.
  { right; auto. }
  destruct (peq a p); subst.
  - rewrite Pos.eqb_refl; left; left; reflexivity.
  - destruct (IHl p).
    + rewrite orb_true_r; left; right; assumption.
    + apply Pos.eqb_neq in n; rewrite n; right; intros [H|H]; subst.
      * rewrite Pos.eqb_refl in n; discriminate.
      * contradiction.
Qed.

Lemma not_in_inb x l :
  ~ In x l ->
  inb x l = true ->
  False.
Proof. intros Hnotin Hinb; destruct (inb_spec x l); congruence. Qed.

Fixpoint dedup (l : list positive) : list positive :=
  match l with
  | nil => nil
  | x :: xs =>
      let l' := dedup xs in
      if inb x l' then l' else x :: l'
  end.

Lemma in_dedup (p : positive) (l : list positive) :
  In p (dedup l) -> In p l.
Proof.
  revert p; induction l; simpl; intros p Hin; auto.
  destruct (inb_spec a (dedup l)).
  - right; apply IHl; assumption.
  - inv Hin.
    + left; reflexivity.
    + right; apply IHl; assumption.
Qed.

Definition succ_of_instruction (instr : instruction) : option node :=
  match instr with
  | Inop succ => Some succ
  | Iop _ _ _ succ => Some succ
  | Iload _ _ _ _ succ => Some succ
  | Istore _ _ _ _ succ => Some succ
  | Icall _ _ _ _ succ => Some succ
  | Ibuiltin _ _ _ succ => Some succ
  | _ => None
  end.

(* Includes Icond and Ijumptable *)
Definition succs_of_instruction (instr : instruction) : list node :=
  match instr with
  | Inop succ => succ :: nil
  | Iop _ _ _ succ => succ :: nil
  | Iload _ _ _ _ succ => succ :: nil
  | Istore _ _ _ _ succ => succ :: nil
  | Icall _ _ _ _ succ => succ :: nil
  | Ibuiltin _ _ _ succ => succ :: nil
  | Icond _ _ ifso ifnot => ifso :: ifnot :: nil
  | Ijumptable _ succs => succs
  | _ => nil
  end.

(** Modify [instr] to jump to [new_succ]. *)
Definition change_succ (instr : instruction) (new_succ : node) : instruction :=
  match instr with
  | Inop _ => Inop new_succ
  | Iop op args dst _ => Iop op args dst new_succ
  | Iload chunk addr args dst _ => Iload chunk addr args dst new_succ
  | Istore chunk addr args src _ => Istore chunk addr args src new_succ
  | Icall sig fn args dst _ => Icall sig fn args dst new_succ
  | Ibuiltin ef args dst _ => Ibuiltin ef args dst new_succ
  | _ => instr
  end.

(** This ignores the recursive cases because according to
    [exec_Ibuiltin] (specifically [regmap_setres]) the result is used
    only in the [BR] case.  *)
Definition reg_of_builtin_res (res : builtin_res reg) : option reg :=
  match res with
  | BR r => Some r
  | _ => None
  end.

(** Result register of instruction. *)
Definition res_of_instruction (instr : instruction) : option reg :=
  match instr with
  | Iop _ _ res _ => Some res
  | Iload _ _ _ res _ => Some res
  | Icall _ _ _ res _ => Some res
  | Ibuiltin _ _ res _ => reg_of_builtin_res res
  | _ => None
  end.

Inductive in_builtin_arg {A : Type} (a : A) : builtin_arg A -> Prop :=
| in_builtin_arg_BA : in_builtin_arg a (BA a)
| in_builtin_arg_splitlong_hi : forall hi lo,
    in_builtin_arg a hi ->
    in_builtin_arg a (BA_splitlong hi lo)
| in_builtin_arg_splitlong_lo : forall hi lo,
    in_builtin_arg a lo ->
    in_builtin_arg a (BA_splitlong hi lo)
| in_builtin_arg_addptr_a1 : forall a1 a2,
    in_builtin_arg a a1 ->
    in_builtin_arg a (BA_addptr a1 a2)
| in_builtin_arg_addptr_a2 : forall a1 a2,
    in_builtin_arg a a2 ->
    in_builtin_arg a (BA_addptr a1 a2).

Fixpoint in_builtin_argb (r : reg) (barg : builtin_arg reg) : bool :=
  match barg with
  | BA r' => Pos.eqb r r'
  | BA_splitlong hi lo => in_builtin_argb r hi || in_builtin_argb r lo
  | BA_addptr a b => in_builtin_argb r a || in_builtin_argb r b
  | _ => false
  end.

Lemma in_builtin_argb_spec (r : reg) (barg : builtin_arg reg) :
  reflect (in_builtin_arg r barg) (in_builtin_argb r barg).
Proof.
  induction barg; simpl; try solve [right; intro HC; inv HC].
  - destruct (Pos.eqb_spec r x); subst.
    + left; constructor.
    + right; intro HC; inv HC; congruence.
  - destruct IHbarg1; simpl.
    + left; constructor; auto.
    + destruct IHbarg2; simpl.
      * left; solve [constructor; auto].
      * right; intro HC; inv HC; contradiction.
  - destruct IHbarg1; simpl.
    + left; constructor; auto.
    + destruct IHbarg2; simpl.
      * left; solve [constructor; auto].
      * right; intro HC; inv HC; contradiction.
Qed.

Lemma in_builtin_argb_sound (r : reg) (barg : builtin_arg reg) :
  in_builtin_argb r barg = true -> in_builtin_arg r barg.
Proof. destruct (in_builtin_argb_spec r barg); congruence. Qed.

Lemma in_regs_of_builtin_arg_in_builtin_arg r barg :
  In r (regs_of_builtin_arg barg) <-> in_builtin_arg r barg.
Proof.
  split.
  - induction barg; simpl; intro Hin; try contradiction;
      try (destruct Hin; subst; try contradiction; constructor);
      apply in_app_or in Hin; destruct Hin as [Hin | Hin];
      solve [constructor; auto].
  - induction barg; simpl; intro Hin; inv Hin; auto; apply in_or_app; auto.
Qed.

Lemma in_regs_of_builtin_args_exists_in_builtin_arg r bargs :
  In r (regs_of_builtin_args bargs) <-> Exists (in_builtin_arg r) bargs.
Proof.
  split.
  - induction bargs; simpl; intro Hin; try contradiction.
    apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + constructor; apply in_regs_of_builtin_arg_in_builtin_arg; auto.
    + right; auto.
  - induction bargs; simpl; intro Hin; inv Hin.
    + apply in_or_app; left.
      apply in_regs_of_builtin_arg_in_builtin_arg; auto.
    + apply in_or_app; right; auto.
Qed.

Inductive in_builtin_res {A : Type} (a : A) : builtin_res A -> Prop :=
| in_builtin_res_BR : in_builtin_res a (BR a)
| in_builtin_res_splitlong_hi : forall hi lo,
    in_builtin_res a hi ->
    in_builtin_res a (BR_splitlong hi lo)
| in_builtin_res_splitlong_lo : forall hi lo,
    in_builtin_res a lo ->
    in_builtin_res a (BR_splitlong hi lo).

Fixpoint in_builtin_resb (r : reg) (bres : builtin_res reg) : bool :=
  match bres with
  | BR r' => Pos.eqb r r'
  | BR_none => false
  | BR_splitlong hi lo => in_builtin_resb r hi || in_builtin_resb r lo
  end.

Lemma in_builtin_resb_spec (r : reg) (bres : builtin_res reg) :
  reflect (in_builtin_res r bres) (in_builtin_resb r bres).
Proof.
  induction bres; simpl; try solve [right; intro HC; inv HC].
  - destruct (Pos.eqb_spec r x); subst.
    + left; constructor.
    + right; intro HC; inv HC; congruence.
  - destruct IHbres1; simpl.
    + left; constructor; auto.
    + destruct IHbres2; simpl.
      * left; solve [constructor; auto].
      * right; intro HC; inv HC; contradiction.
Qed.

Lemma in_builtin_resb_sound (r : reg) (bres : builtin_res reg) :
  in_builtin_resb r bres = true -> in_builtin_res r bres.
Proof. destruct (in_builtin_resb_spec r bres); congruence. Qed.

(* TODO: maybe we can just assume faulted floats aren't NaN, and then
   the conversions from single/float to int/long will always succeed
   and we can consider them safe?

   It seems that considering NaN conversions to int/long to be
   immediate UB is a CompCert choice that isn't necessarily dictated
   by the C standard.

   Also TODO: this might need to go into backend specific Op.v
   file. And should it be called something else? 'is_protected'?
 *)
Inductive is_protected : operation -> Prop :=
(* Because division by zero causes immediate UB (see [Val.divs] in
   common/Values.v) *)
| is_protected_Odiv : is_protected Odiv
| is_protected_Odivu : is_protected Odivu
| is_protected_Omod : is_protected Omod
| is_protected_Omodu : is_protected Omodu
| is_protected_Odivl : is_protected Odivl
| is_protected_Odivlu : is_protected Odivlu
| is_protected_Omodl : is_protected Omodl
| is_protected_Omodlu : is_protected Omodlu

(* Trying to convert NaN (and maybe something else) causes immediate
   UB (see Val.intoffloat in common/Values.v) *)
| is_protected_Ointofsingle : is_protected Ointofsingle
| is_protected_Ointoffloat : is_protected Ointoffloat
| is_protected_Olongofsingle : is_protected Olongofsingle
| is_protected_Olongoffloat : is_protected Olongoffloat

(* Shifting more than the archi word size is immediate UB (see Val.shl
   in common/Values.v) *)
| is_protected_Oshl : is_protected Oshl
| is_protected_Oshr : is_protected Oshr
| is_protected_Oshru : is_protected Oshru
| is_protected_Oshll : is_protected Oshll
| is_protected_Oshrl : is_protected Oshrl
| is_protected_Oshrlu : is_protected Oshrlu

(* Subtracting pointers in different blocks causes immediate UB (see
   [Val.subl] in common/Values.v) *)
| is_protected_Osubl : Archi.ptr64 = true -> is_protected Osubl

(* A faulty selection can cause the faulty execution to take Vundef
   into a register that the normal execution has a defined value for,
   and subsequently encounter UB that the normal execution avoids. See
   [Val.select] in common/Values.v. *)
| is_protected_Osel : forall cond ty, is_protected (Osel cond ty)

(* Comparing pointers in different blocks or comparing a pointer with
   a nonzero integer causes immediate UB. *)
| is_protected_Ocmp_Ccompu : forall c, Archi.ptr64 = false ->
                               is_protected (Ocmp (Ccompu c))
| is_protected_Ocmp_Ccompuimm : forall c n, Archi.ptr64 = false ->
                                    is_protected (Ocmp (Ccompuimm c n))
| is_protected_Ocmp_Ccomplu : forall c, Archi.ptr64 = true ->
                                is_protected (Ocmp (Ccomplu c))
| is_protected_Ocmp_Ccompluimm : forall c n, Archi.ptr64 = true ->
                                     is_protected (Ocmp (Ccompluimm c n))
.

Definition is_protectedb (op : operation) : bool :=
  match op with
  | Odiv | Odivu | Omod | Omodu
  | Odivl | Odivlu | Omodl | Omodlu
  | Ointofsingle | Ointoffloat => true
  | Olongofsingle | Olongoffloat => true
  | Oshl | Oshr | Oshru | Oshll | Oshrl | Oshrlu => true
  | Osubl => Archi.ptr64
  | Osel _ _ => true
  | Ocmp (Ccompu _) | Ocmp (Ccompuimm _ _) => negb Archi.ptr64
  | Ocmp (Ccomplu _) | Ocmp (Ccompluimm _ _) => Archi.ptr64
  | _ => false
  end.

Lemma is_protectedb_spec (op : operation) : reflect (is_protected op) (is_protectedb op).
Proof.
  destruct op; try solve [right; intro HC; inv HC];
    try left; try constructor; auto.
  destruct cond; simpl; try solve [right; intro HC; inv HC].
  - destruct Archi.ptr64 eqn:Harchi; simpl.
    + right; intro HC; inv HC; congruence.
    + left; constructor; assumption.
  - destruct Archi.ptr64 eqn:Harchi; simpl.
    + right; intro HC; inv HC; congruence.
    + left; constructor; assumption.
  - destruct Archi.ptr64 eqn:Harchi; simpl.
    + left; constructor; assumption.
    + right; intro HC; inv HC; congruence.
  - destruct Archi.ptr64 eqn:Harchi; simpl.
    + left; constructor; assumption.
    + right; intro HC; inv HC; congruence.
Qed.

Lemma is_protected_subl_archi_ptr64_false :
  ~ is_protected Op.Osubl ->
  Archi.ptr64 = false.
Proof.
  intro H.
  destruct Archi.ptr64 eqn:Harchi; auto.
  exfalso; apply H; constructor; assumption.
Qed.

Inductive is_compu : condition -> Prop :=
| is_compu_CCompu : forall c, is_compu (Ccompu c)
| is_compu_CCompuimm : forall c n, is_compu (Ccompuimm c n).

Inductive is_complu : condition -> Prop :=
| is_compu_CComplu : forall c, is_complu (Ccomplu c)
| is_compu_CCompluimm : forall c n, is_complu (Ccompluimm c n).

Fixpoint builtin_res_forall {A : Type} (P : A -> Prop) (bres : builtin_res A) : Prop :=
  match bres with
  | BR x => P x
  | BR_none => True
  | BR_splitlong hi lo => builtin_res_forall P hi /\ builtin_res_forall P lo
  end.

Lemma builtin_res_forall_impl {A : Type} (P Q : A -> Prop ) bres :
  (forall a, P a -> Q a) ->
  builtin_res_forall P bres ->
  builtin_res_forall Q bres.
Proof.
  induction bres; simpl; intros Hpq Hforall; auto;
    destruct Hforall; auto.
Qed.

Fixpoint builtin_res_forallb {A : Type} (f : A -> bool) (bres : builtin_res A) : bool :=
  match bres with
  | BR x => f x
  | BR_none => true
  | BR_splitlong hi lo => builtin_res_forallb f hi && builtin_res_forallb f lo
  end.

Lemma builtin_res_forallb_spec {A : Type} (f : A -> bool) (bres : builtin_res A) :
  reflect (builtin_res_forall (fun a => f a = true) bres) (builtin_res_forallb f bres).
Proof.
  induction bres; simpl; try left; auto.
  - destruct (f x); solve [constructor; auto].
  - destruct IHbres1; simpl.
    + destruct IHbres2; simpl.
      * left; split; auto.
      * right; intros [H0 H1]; congruence.
    + right; intros [H0 H1]; congruence.
Qed.

Lemma builtin_res_forallb_sound {A : Type} (f : A -> bool) (bres : builtin_res A) :
  builtin_res_forallb f bres = true -> builtin_res_forall (fun a => f a = true) bres.
Proof. destruct (builtin_res_forallb_spec f bres); congruence. Qed.

Lemma in_builtin_arg_forall {A : Type} (P : A -> Prop) barg x :
  builtin_arg_forall P barg ->
  in_builtin_arg x barg ->
  P x.
Proof.
  revert x; induction barg; simpl; intros y Hforall Hin; inv Hin; auto;
    try solve [apply IHbarg1; intuition]; apply IHbarg2; intuition.
Qed.

Lemma in_builtin_res_forall {A : Type} (P : A -> Prop) bres x :
  builtin_res_forall P bres ->
  in_builtin_res x bres ->
  P x.
Proof.
  revert x; induction bres; simpl; intros y Hforall Hin; inv Hin; auto;
    destruct Hforall as [H1 H2]; auto.
Qed.

Inductive is_green_smove_builtin : external_function -> Prop :=
| is_green_smove_int :
  is_green_smove_builtin (EF_builtin "__builtin_smove_int_green"
                            [Xint ---> Xint]%asttyp)
| is_green_smove_long :
  is_green_smove_builtin (EF_builtin "__builtin_smove_long_green"
                            [Xlong ---> Xlong]%asttyp)
| is_green_smove_single :
  is_green_smove_builtin (EF_builtin "__builtin_smove_single_green"
                            [Xsingle ---> Xsingle]%asttyp)
| is_green_smove_float :
  is_green_smove_builtin (EF_builtin "__builtin_smove_float_green"
                            [Xfloat ---> Xfloat]%asttyp).

Definition is_green_smove_builtinb (ef : external_function) : bool :=
  match ef with
  | EF_builtin name sg =>
      (String.eqb name "__builtin_smove_int_green" &&
         proj_sumbool (signature_eq sg
                         [Xint ---> Xint]%asttyp)) ||
        (String.eqb name "__builtin_smove_long_green" &&
           proj_sumbool (signature_eq sg
                           [Xlong ---> Xlong]%asttyp)) ||
        (String.eqb name "__builtin_smove_single_green" &&
           proj_sumbool (signature_eq sg
                           [Xsingle ---> Xsingle]%asttyp)) ||
        (String.eqb name "__builtin_smove_float_green" &&
           proj_sumbool (signature_eq sg
                           [Xfloat ---> Xfloat]%asttyp))
  | _ => false
  end.

Lemma is_green_smove_builtinb_spec (ef : external_function) :
  reflect (is_green_smove_builtin ef) (is_green_smove_builtinb ef).
Proof.
  destruct ef; try solve [right; intro HC; inv HC].
  simpl.
  destruct (String.eqb name "__builtin_smove_single_green") eqn:H0.
  { rewrite String.eqb_eq in H0; subst.
    destruct (signature_eq sg
                [Xsingle ---> Xsingle]%asttyp); subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H0.
  destruct (String.eqb name "__builtin_smove_int_green") eqn:H1.
  { rewrite String.eqb_eq in H1; subst.
    destruct (signature_eq sg
                [Xint ---> Xint]%asttyp); subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H1.
  destruct (String.eqb name "__builtin_smove_float_green") eqn:H2.
  { rewrite String.eqb_eq in H2; subst.
    destruct (signature_eq sg
                [Xfloat ---> Xfloat]%asttyp)eqn:H2; subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H2.
  destruct (String.eqb name "__builtin_smove_long_green") eqn:H3.
  { rewrite String.eqb_eq in H3; subst.
    destruct (signature_eq sg
                [Xlong ---> Xlong]%asttyp); subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H3.
  right; intro HC; inv HC; congruence.
Qed.

Inductive is_blue_smove_builtin : external_function -> Prop :=
| is_blue_smove_int :
  is_blue_smove_builtin (EF_builtin "__builtin_smove_int_blue"
                            [Xint ---> Xint]%asttyp)
| is_blue_smove_long :
  is_blue_smove_builtin (EF_builtin "__builtin_smove_long_blue"
                            [Xlong ---> Xlong]%asttyp)
| is_blue_smove_single :
  is_blue_smove_builtin (EF_builtin "__builtin_smove_single_blue"
                            [Xsingle ---> Xsingle]%asttyp)
| is_blue_smove_float :
  is_blue_smove_builtin (EF_builtin "__builtin_smove_float_blue"
                            [Xfloat ---> Xfloat]%asttyp).

Definition is_blue_smove_builtinb (ef : external_function) : bool :=
  match ef with
  | EF_builtin name sg =>
      (String.eqb name "__builtin_smove_int_blue" &&
         proj_sumbool (signature_eq sg
                         [Xint ---> Xint]%asttyp)) ||
        (String.eqb name "__builtin_smove_long_blue" &&
           proj_sumbool (signature_eq sg
                           [Xlong ---> Xlong]%asttyp)) ||
        (String.eqb name "__builtin_smove_single_blue" &&
           proj_sumbool (signature_eq sg
                           [Xsingle ---> Xsingle]%asttyp)) ||
        (String.eqb name "__builtin_smove_float_blue" &&
           proj_sumbool (signature_eq sg
                           [Xfloat ---> Xfloat]%asttyp))
  | _ => false
  end.

Lemma is_blue_smove_builtinb_spec (ef : external_function) :
  reflect (is_blue_smove_builtin ef) (is_blue_smove_builtinb ef).
Proof.
  destruct ef; try solve [right; intro HC; inv HC].
  simpl.
  destruct (String.eqb name "__builtin_smove_single_blue") eqn:H0.
  { rewrite String.eqb_eq in H0; subst.
    destruct (signature_eq sg
                [Xsingle ---> Xsingle]%asttyp); subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H0.
  destruct (String.eqb name "__builtin_smove_int_blue") eqn:H1.
  { rewrite String.eqb_eq in H1; subst.
    destruct (signature_eq sg
                [Xint ---> Xint]%asttyp); subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H1.
  destruct (String.eqb name "__builtin_smove_float_blue") eqn:H2.
  { rewrite String.eqb_eq in H2; subst.
    destruct (signature_eq sg
                [Xfloat ---> Xfloat]%asttyp)eqn:H2; subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H2.
  destruct (String.eqb name "__builtin_smove_long_blue") eqn:H3.
  { rewrite String.eqb_eq in H3; subst.
    destruct (signature_eq sg
                [Xlong ---> Xlong]%asttyp); subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H3.
  right; intro HC; inv HC; congruence.
Qed.

Inductive is_vote_builtin : external_function -> Prop :=
| is_vote_int :
  is_vote_builtin (EF_builtin "__builtin_vote_int"
                     [Xint; Xint; Xint ---> Xint]%asttyp)
| is_vote_long :
  is_vote_builtin (EF_builtin "__builtin_vote_long"
                     [Xlong; Xlong; Xlong ---> Xlong]%asttyp)
| is_vote_single :
  is_vote_builtin (EF_builtin "__builtin_vote_single"
                     [Xsingle; Xsingle; Xsingle ---> Xsingle]%asttyp)
| is_vote_float :
  is_vote_builtin (EF_builtin "__builtin_vote_float"
                     [Xfloat; Xfloat; Xfloat ---> Xfloat]%asttyp).

Definition is_vote_builtinb (ef : external_function) : bool :=
  match ef with
  | EF_builtin name sg =>
      (String.eqb name "__builtin_vote_int" &&
         proj_sumbool (signature_eq sg
                         [Xint; Xint; Xint ---> Xint]%asttyp)) ||
        (String.eqb name "__builtin_vote_long" &&
           proj_sumbool (signature_eq sg
                           [Xlong; Xlong; Xlong ---> Xlong]%asttyp)) ||
        (String.eqb name "__builtin_vote_single" &&
           proj_sumbool (signature_eq sg
                           [Xsingle; Xsingle; Xsingle ---> Xsingle]%asttyp)) ||
        (String.eqb name "__builtin_vote_float" &&
           proj_sumbool (signature_eq sg
                           [Xfloat; Xfloat; Xfloat ---> Xfloat]%asttyp))
  | _ => false
  end.

Lemma is_vote_builtinb_spec (ef : external_function) :
  reflect (is_vote_builtin ef) (is_vote_builtinb ef).
Proof.
  destruct ef; try solve [right; intro HC; inv HC].
  simpl.
  destruct (String.eqb name "__builtin_vote_single") eqn:H0.
  { rewrite String.eqb_eq in H0; subst.
    destruct (signature_eq sg
                [Xsingle; Xsingle; Xsingle ---> Xsingle]%asttyp); subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H0.
  destruct (String.eqb name "__builtin_vote_int") eqn:H1.
  { rewrite String.eqb_eq in H1; subst.
    destruct (signature_eq sg
                [Xint; Xint; Xint ---> Xint]%asttyp); subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H1.
  destruct (String.eqb name "__builtin_vote_float") eqn:H2.
  { rewrite String.eqb_eq in H2; subst.
    destruct (signature_eq sg
                [Xfloat; Xfloat; Xfloat ---> Xfloat]%asttyp)eqn:H2; subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H2.
  destruct (String.eqb name "__builtin_vote_long") eqn:H3.
  { rewrite String.eqb_eq in H3; subst.
    destruct (signature_eq sg
                [Xlong; Xlong; Xlong ---> Xlong]%asttyp); subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H3.
  right; intro HC; inv HC; congruence.
Qed.
  
Lemma vote_not_green_smove (ef : external_function) :
  is_vote_builtin ef -> ~ is_green_smove_builtin ef.
Proof. intro H; inv H; intro HC; inv HC. Qed.

Lemma vote_not_blue_smove (ef : external_function) :
  is_vote_builtin ef -> ~ is_blue_smove_builtin ef.
Proof. intro H; inv H; intro HC; inv HC. Qed.

Inductive is_vote_runtime : external_function -> Prop :=
| is_vote_runtime_int :
  is_vote_runtime (EF_runtime "__builtin_vote_int"
                     [Xint; Xint; Xint ---> Xint]%asttyp)
| is_vote_runtime_long :
  is_vote_runtime (EF_runtime "__builtin_vote_long"
                     [Xlong; Xlong; Xlong ---> Xlong]%asttyp)
| is_vote_runtime_single :
  is_vote_runtime (EF_runtime "__builtin_vote_single"
                     [Xsingle; Xsingle; Xsingle ---> Xsingle]%asttyp)
| is_vote_runtime_float :
  is_vote_runtime (EF_runtime "__builtin_vote_float"
                     [Xfloat; Xfloat; Xfloat ---> Xfloat]%asttyp).

Definition is_vote_runtimeb (ef : external_function) : bool :=
  match ef with
  | EF_runtime name sg =>
      (String.eqb name "__builtin_vote_int" &&
         proj_sumbool (signature_eq sg
                         [Xint; Xint; Xint ---> Xint]%asttyp)) ||
        (String.eqb name "__builtin_vote_long" &&
           proj_sumbool (signature_eq sg
                           [Xlong; Xlong; Xlong ---> Xlong]%asttyp)) ||
        (String.eqb name "__builtin_vote_single" &&
           proj_sumbool (signature_eq sg
                           [Xsingle; Xsingle; Xsingle ---> Xsingle]%asttyp)) ||
        (String.eqb name "__builtin_vote_float" &&
           proj_sumbool (signature_eq sg
                           [Xfloat; Xfloat; Xfloat ---> Xfloat]%asttyp))
  | _ => false
  end.

Lemma is_vote_runtimeb_spec (ef : external_function) :
  reflect (is_vote_runtime ef) (is_vote_runtimeb ef).
Proof.
  destruct ef; try solve [right; intro HC; inv HC].
  simpl.
  destruct (String.eqb name "__builtin_vote_single") eqn:H0.
  { rewrite String.eqb_eq in H0; subst.
    destruct (signature_eq sg
                [Xsingle; Xsingle; Xsingle ---> Xsingle]%asttyp); subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H0.
  destruct (String.eqb name "__builtin_vote_int") eqn:H1.
  { rewrite String.eqb_eq in H1; subst.
    destruct (signature_eq sg
                [Xint; Xint; Xint ---> Xint]%asttyp); subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H1.
  destruct (String.eqb name "__builtin_vote_float") eqn:H2.
  { rewrite String.eqb_eq in H2; subst.
    destruct (signature_eq sg
                [Xfloat; Xfloat; Xfloat ---> Xfloat]%asttyp)eqn:H2; subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H2.
  destruct (String.eqb name "__builtin_vote_long") eqn:H3.
  { rewrite String.eqb_eq in H3; subst.
    destruct (signature_eq sg
                [Xlong; Xlong; Xlong ---> Xlong]%asttyp); subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H3.
  right; intro HC; inv HC; congruence.
Qed.

Definition Regset_of_list (l : list positive) : Regset.t  :=
  fold_right (fun acc p => Regset.add acc p) Regset.empty l.

Definition Regset_of_option (x : option positive) : Regset.t :=
  match x with
  | Some p => Regset.singleton p
  | None => Regset.empty
  end.

(** All registers that appear in an instruction (arguments or
    destination). *)
Definition instr_regs (i : instruction) : Regset.t :=
  match i with
  | Inop _ => Regset.empty
  | Iop _ args res _ =>
      Regset.union (Regset_of_list args) (Regset.singleton res)
  | Iload _ _ args dst _ =>
      Regset.union (Regset_of_list args) (Regset.singleton dst)
  | Istore _ _ args src _ =>
      Regset.union (Regset_of_list args) (Regset.singleton src)
  | Icall _ (inl r) args res _ =>
      Regset.union (Regset_of_list (r :: args)) (Regset.singleton res)
  | Icall _ _ args res _ =>
      Regset.union (Regset_of_list args) (Regset.singleton res)
  | Itailcall _ (inl r) args => Regset_of_list (r :: args)
  | Itailcall _ _ args => Regset_of_list args
  | Ibuiltin _ args res _ =>
      Regset.union (Regset_of_list (regs_of_builtin_args args))
        (Regset_of_option (reg_of_builtin_res res))
  | Icond _ args _ _ => Regset_of_list args
  | Ijumptable arg _ => Regset.singleton arg
  | Ireturn (Some arg) => Regset.singleton arg
  | Ireturn None => Regset.empty
  end.

(** All registers that appear in the given code (used in
    instructions). *)
Definition code_regs (c : code) : Regset.t :=
  PTree.fold (fun rs _ instr => Regset.union rs (instr_regs instr)) c Regset.empty.

Definition all_regs (params : list reg) (c : code) : Regset.t :=
  Regset.union (Regset_of_list params) (code_regs c).

Definition all_regs_list (params : list reg) (c : code) : list reg :=
  Regset.elements (all_regs params c).

(** All registers that appear in the given function (params + regs
    used in instructions). *)
Definition fun_regs (f : function) : Regset.t :=
  all_regs f.(fn_params) f.(fn_code).

Definition fun_regs_list (f : function) : list positive :=
  all_regs_list f.(fn_params) f.(fn_code).

Definition max_reg (regs : Regset.t) :=
  match Regset.max_elt regs with
  | Some p => p
  | None => 1%positive
  end.
