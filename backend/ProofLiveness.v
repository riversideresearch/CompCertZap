(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Conservative liveness analysis for the fault tolerance proof.       *)
(*  Derived from Liveness.v but always includes Iop/Iload argument     *)
(*  registers in the live set, regardless of whether the destination   *)
(*  register is live.  This is required by the faulty backward         *)
(*  simulation proof in RTLtolerant.v.                                 *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib.
Require Import Maps.
Require Import Lattice.
Require Import AST.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Kildall.

(** Helper definitions (identical to Liveness.v). *)

Notation reg_live := Regset.add.
Notation reg_dead := Regset.remove.

Definition reg_option_live (or: option reg) (lv: Regset.t) :=
  match or with None => lv | Some r => reg_live r lv end.

Definition reg_sum_live (ros: reg + ident) (lv: Regset.t) :=
  match ros with inl r => reg_live r lv | inr s => lv end.

Fixpoint reg_list_live
             (rl: list reg) (lv: Regset.t) {struct rl} : Regset.t :=
  match rl with
  | nil => lv
  | r1 :: rs => reg_list_live rs (reg_live r1 lv)
  end.

Fixpoint reg_list_dead
             (rl: list reg) (lv: Regset.t) {struct rl} : Regset.t :=
  match rl with
  | nil => lv
  | r1 :: rs => reg_list_dead rs (reg_dead r1 lv)
  end.

(** Conservative transfer function for the backward liveness analysis.
  Unlike [Liveness.transfer], this function always includes the argument
  registers of [Iop] and [Iload] instructions in the live set, even when
  the destination register is not live.  This ensures that [Val.lessdef]
  obligations on argument registers can always be discharged in the faulty
  backward simulation proof. *)

Definition transfer
            (f: function) (pc: node) (after: Regset.t) : Regset.t :=
  match f.(fn_code)!pc with
  | None =>
      Regset.empty
  | Some i =>
      match i with
      | Inop s =>
          after
      | Iop op args res s =>
          reg_list_live args (reg_dead res after)
      | Iload chunk addr args dst s =>
          reg_list_live args (reg_dead dst after)
      | Istore chunk addr args src s =>
          reg_list_live args (reg_live src after)
      | Icall sig ros args res s =>
          reg_list_live args
           (reg_sum_live ros (reg_dead res after))
      | Itailcall sig ros args =>
          reg_list_live args (reg_sum_live ros Regset.empty)
      | Ibuiltin ef args res s =>
          reg_list_live (params_of_builtin_args args)
            (reg_list_dead (params_of_builtin_res res) after)
      | Icond cond args ifso ifnot =>
          reg_list_live args after
      | Ijumptable arg tbl =>
          reg_live arg after
      | Ireturn optarg =>
          reg_option_live optarg Regset.empty
      end
  end.

(** Solver instantiation using the Kildall backward dataflow framework. *)

Module RegsetLat := LFSet(Regset).
Module DS := Backward_Dataflow_Solver(RegsetLat)(NodeSetBackward).

Definition analyze (f: function): option (PMap.t Regset.t) :=
  DS.fixpoint f.(fn_code) successors_instr (transfer f).

(** Fixpoint property: for every CFG edge from [n] to [s], the transfer
  function result at [s] is a subset of the fixpoint value at [n]. *)

Lemma analyze_solution:
  forall f live n i s,
  analyze f = Some live ->
  f.(fn_code)!n = Some i ->
  In s (successors_instr i) ->
  Regset.Subset (transfer f s live!!s) live!!n.
Proof.
  unfold analyze; intros. eapply DS.fixpoint_solution; eauto.
  intros. unfold transfer; rewrite H2. apply DS.L.eq_refl.
Qed.

(** Monotonicity helper: [reg_list_live] preserves existing membership. *)

Lemma reg_list_live_incl:
  forall args s r,
  Regset.In r s -> Regset.In r (reg_list_live args s).
Proof.
  induction args; simpl; intros.
  - assumption.
  - apply IHargs. apply Regset.add_2. assumption.
Qed.

(** Membership lemma: if [r] is in [args], then [r] is in
  [reg_list_live args s] for any [s]. *)

Lemma reg_list_live_in:
  forall r args s,
  In r args -> Regset.In r (reg_list_live args s).
Proof.
  induction args; simpl; intros.
  - contradiction.
  - destruct H as [H | H].
    + subst. apply reg_list_live_incl. apply Regset.add_1. reflexivity.
    + apply IHargs. assumption.
Qed.
