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
Require Import Events.
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
            (match res with BR x => reg_dead x after | _ => after end)
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

(** Bridge: [in_builtin_arg] implies membership in [params_of_builtin_arg]. *)

Lemma in_builtin_arg_in_params {A : Type} (a : A) barg :
  in_builtin_arg a barg -> In a (params_of_builtin_arg barg).
Proof.
  induction barg; simpl; intro H; inv H;
    try (left; reflexivity);
    try (apply in_or_app; left; auto; fail);
    try (apply in_or_app; right; auto; fail).
Qed.

Lemma in_builtin_arg_in_params_args {A : Type} (a : A) barg bargs :
  In barg bargs ->
  in_builtin_arg a barg ->
  In a (params_of_builtin_args bargs).
Proof.
  induction bargs; simpl; intros Hin Harg.
  - destruct Hin.
  - destruct Hin as [-> | Hin].
    + apply in_or_app; left. apply in_builtin_arg_in_params; auto.
    + apply in_or_app; right. eapply IHbargs; eauto.
Qed.

(** Variant of [builtin_arg_forall_impl] that also provides
    [in_builtin_arg a barg] evidence to the callback. *)

Lemma builtin_arg_forall_impl_in {A : Type} (P Q : A -> Prop) barg :
  (forall a, P a -> in_builtin_arg a barg -> Q a) ->
  builtin_arg_forall P barg ->
  builtin_arg_forall Q barg.
Proof.
  induction barg; simpl; intros Hpq Hforall; auto.
  - apply Hpq; auto. constructor.
  - destruct Hforall as [H1 H2]; split.
    + apply IHbarg1; auto.
      intros a Ha Hin. apply Hpq; auto. constructor; auto.
    + apply IHbarg2; auto.
      intros a Ha Hin. apply Hpq; auto.
      apply in_builtin_arg_splitlong_lo; auto.
  - destruct Hforall as [H1 H2]; split.
    + apply IHbarg1; auto.
      intros a Ha Hin. apply Hpq; auto. constructor; auto.
    + apply IHbarg2; auto.
      intros a Ha Hin. apply Hpq; auto.
      apply in_builtin_arg_addptr_a2; auto.
Qed.

(** Per-instruction liveness membership helpers.
    These prove that instruction arguments are in the transfer-function
    image [transfer f pc (live !! pc)], which is the
    "live-before" set at node [pc]. *)

Lemma args_in_transfer_iop f live pc op args res succ r :
  (fn_code f) ! pc = Some (Iop op args res succ) ->
  In r args ->
  Regset.In r (transfer f pc (live !! pc)).
Proof.
  intros Hpc Hin.
  unfold transfer. rewrite Hpc.
  apply reg_list_live_in; auto.
Qed.

Lemma args_in_transfer_iload f live pc chunk addr args dst succ r :
  (fn_code f) ! pc = Some (Iload chunk addr args dst succ) ->
  In r args ->
  Regset.In r (transfer f pc (live !! pc)).
Proof.
  intros Hpc Hin.
  unfold transfer. rewrite Hpc.
  apply reg_list_live_in; auto.
Qed.

Lemma args_in_transfer_istore f live pc chunk addr args src succ r :
  (fn_code f) ! pc = Some (Istore chunk addr args src succ) ->
  In r args ->
  Regset.In r (transfer f pc (live !! pc)).
Proof.
  intros Hpc Hin.
  unfold transfer. rewrite Hpc.
  apply reg_list_live_in; auto.
Qed.

Lemma src_in_transfer_istore f live pc chunk addr args src succ :
  (fn_code f) ! pc = Some (Istore chunk addr args src succ) ->
  Regset.In src (transfer f pc (live !! pc)).
Proof.
  intros Hpc.
  unfold transfer. rewrite Hpc.
  apply reg_list_live_incl.
  apply Regset.add_1. reflexivity.
Qed.

Lemma args_in_transfer_icall f live pc sig ros args res succ r :
  (fn_code f) ! pc = Some (Icall sig ros args res succ) ->
  In r args ->
  Regset.In r (transfer f pc (live !! pc)).
Proof.
  intros Hpc Hin.
  unfold transfer. rewrite Hpc.
  apply reg_list_live_in; auto.
Qed.

Lemma ros_in_transfer_icall f live pc sig r args res succ :
  (fn_code f) ! pc = Some (Icall sig (inl r) args res succ) ->
  Regset.In r (transfer f pc (live !! pc)).
Proof.
  intros Hpc.
  unfold transfer. rewrite Hpc.
  apply reg_list_live_incl.
  simpl. apply Regset.add_1. reflexivity.
Qed.

Lemma args_in_transfer_itailcall f live pc sig ros args r :
  (fn_code f) ! pc = Some (Itailcall sig ros args) ->
  In r args ->
  Regset.In r (transfer f pc (live !! pc)).
Proof.
  intros Hpc Hin.
  unfold transfer. rewrite Hpc.
  apply reg_list_live_in; auto.
Qed.

Lemma ros_in_transfer_itailcall f live pc sig r args :
  (fn_code f) ! pc = Some (Itailcall sig (inl r) args) ->
  Regset.In r (transfer f pc (live !! pc)).
Proof.
  intros Hpc.
  unfold transfer. rewrite Hpc.
  apply reg_list_live_incl.
  simpl. apply Regset.add_1. reflexivity.
Qed.

Lemma args_in_transfer_icond f live pc cond args ifso ifnot r :
  (fn_code f) ! pc = Some (Icond cond args ifso ifnot) ->
  In r args ->
  Regset.In r (transfer f pc (live !! pc)).
Proof.
  intros Hpc Hin.
  unfold transfer. rewrite Hpc.
  apply reg_list_live_in; auto.
Qed.

Lemma arg_in_transfer_ijumptable f live pc arg tbl :
  (fn_code f) ! pc = Some (Ijumptable arg tbl) ->
  Regset.In arg (transfer f pc (live !! pc)).
Proof.
  intros Hpc.
  unfold transfer. rewrite Hpc.
  apply Regset.add_1. reflexivity.
Qed.

Lemma args_in_transfer_ibuiltin f live pc ef args res succ r :
  (fn_code f) ! pc = Some (Ibuiltin ef args res succ) ->
  In r (params_of_builtin_args args) ->
  Regset.In r (transfer f pc (live !! pc)).
Proof.
  intros Hpc Hin.
  unfold transfer. rewrite Hpc.
  apply reg_list_live_in; auto.
Qed.

Lemma optarg_in_transfer_ireturn f live pc r :
  (fn_code f) ! pc = Some (Ireturn (Some r)) ->
  Regset.In r (transfer f pc (live !! pc)).
Proof.
  intros Hpc.
  unfold transfer. rewrite Hpc.
  simpl. apply Regset.add_1. reflexivity.
Qed.

(** For step_simulation: the transfer set at a successor is a subset
    of the solution at the current node, which in turn is a subset of
    the transfer set at the current node (since the transfer function
    adds arguments on top of a subset of the solution). *)

Lemma transfer_succ_subset f live pc i succ :
  analyze f = Some live ->
  (fn_code f) ! pc = Some i ->
  In succ (successors_instr i) ->
  Regset.Subset (transfer f succ (live !! succ)) (live !! pc).
Proof.
  intros LIVE Hpc Hsucc.
  eapply analyze_solution; eauto.
Qed.

(** Helper: if [r] is in [live !! pc] and [r <> res], then [r] is in
    the transfer-function image for Iop / Iload instructions. *)

Lemma live_in_transfer_iop f live pc op args res succ r :
  (fn_code f) ! pc = Some (Iop op args res succ) ->
  r <> res ->
  Regset.In r (live !! pc) ->
  Regset.In r (transfer f pc (live !! pc)).
Proof.
  intros Hpc Hneq Hin.
  unfold transfer. rewrite Hpc.
  apply reg_list_live_incl.
  apply Regset.remove_2; auto.
Qed.

Lemma live_in_transfer_iload f live pc chunk addr args dst succ r :
  (fn_code f) ! pc = Some (Iload chunk addr args dst succ) ->
  r <> dst ->
  Regset.In r (live !! pc) ->
  Regset.In r (transfer f pc (live !! pc)).
Proof.
  intros Hpc Hneq Hin.
  unfold transfer. rewrite Hpc.
  apply reg_list_live_incl.
  apply Regset.remove_2; auto.
Qed.

Lemma live_in_transfer_istore f live pc chunk addr args src succ r :
  (fn_code f) ! pc = Some (Istore chunk addr args src succ) ->
  Regset.In r (live !! pc) ->
  Regset.In r (transfer f pc (live !! pc)).
Proof.
  intros Hpc Hin.
  unfold transfer. rewrite Hpc.
  apply reg_list_live_incl.
  apply Regset.add_2; auto.
Qed.

Lemma live_in_transfer_icall f live pc sig ros args res succ r :
  (fn_code f) ! pc = Some (Icall sig ros args res succ) ->
  r <> res ->
  Regset.In r (live !! pc) ->
  Regset.In r (transfer f pc (live !! pc)).
Proof.
  intros Hpc Hneq Hin.
  unfold transfer. rewrite Hpc.
  apply reg_list_live_incl.
  destruct ros; simpl.
  - apply Regset.add_2. apply Regset.remove_2; auto.
  - apply Regset.remove_2; auto.
Qed.

Lemma live_in_transfer_icond f live pc cond args ifso ifnot r :
  (fn_code f) ! pc = Some (Icond cond args ifso ifnot) ->
  Regset.In r (live !! pc) ->
  Regset.In r (transfer f pc (live !! pc)).
Proof.
  intros Hpc Hin.
  unfold transfer. rewrite Hpc.
  apply reg_list_live_incl; auto.
Qed.

Lemma live_in_transfer_ijumptable f live pc arg tbl r :
  (fn_code f) ! pc = Some (Ijumptable arg tbl) ->
  Regset.In r (live !! pc) ->
  Regset.In r (transfer f pc (live !! pc)).
Proof.
  intros Hpc Hin.
  unfold transfer. rewrite Hpc.
  apply Regset.add_2; auto.
Qed.

Lemma reg_list_dead_incl rl s r :
  Regset.In r s ->
  ~ In r rl ->
  Regset.In r (reg_list_dead rl s).
Proof.
  revert s; induction rl; simpl; intros s Hin Hnotin.
  - assumption.
  - apply IHrl.
    + apply Regset.remove_2.
      * intro Heq; apply Hnotin; left; auto.
      * assumption.
    + intro Hin'; apply Hnotin; right; auto.
Qed.

Lemma live_in_transfer_ibuiltin f live pc ef args res succ r :
  (fn_code f) ! pc = Some (Ibuiltin ef args res succ) ->
  (forall x, res = BR x -> r <> x) ->
  Regset.In r (live !! pc) ->
  Regset.In r (transfer f pc (live !! pc)).
Proof.
  intros Hpc Hnotin Hin.
  unfold transfer. rewrite Hpc.
  apply reg_list_live_incl.
  destruct res; simpl; auto.
  apply Regset.remove_2; auto.
  intro Heq; eapply Hnotin; eauto.
Qed.

(** Composite helpers: successor transfer set membership implies
    current transfer set membership (for non-killed registers).
    These compose [transfer_succ_subset] with [live_in_transfer_*]. *)

Lemma succ_in_transfer_iop f live pc op args res succ r :
  analyze f = Some live ->
  (fn_code f) ! pc = Some (Iop op args res succ) ->
  r <> res ->
  Regset.In r (transfer f succ (live !! succ)) ->
  Regset.In r (transfer f pc (live !! pc)).
Proof.
  intros LIVE Hpc Hneq Hr.
  eapply live_in_transfer_iop; eauto.
  eapply transfer_succ_subset; eauto. simpl; auto.
Qed.

Lemma succ_in_transfer_iload f live pc chunk addr args dst succ r :
  analyze f = Some live ->
  (fn_code f) ! pc = Some (Iload chunk addr args dst succ) ->
  r <> dst ->
  Regset.In r (transfer f succ (live !! succ)) ->
  Regset.In r (transfer f pc (live !! pc)).
Proof.
  intros LIVE Hpc Hneq Hr.
  eapply live_in_transfer_iload; eauto.
  eapply transfer_succ_subset; eauto. simpl; auto.
Qed.

Lemma succ_in_transfer_istore f live pc chunk addr args src succ r :
  analyze f = Some live ->
  (fn_code f) ! pc = Some (Istore chunk addr args src succ) ->
  Regset.In r (transfer f succ (live !! succ)) ->
  Regset.In r (transfer f pc (live !! pc)).
Proof.
  intros LIVE Hpc Hr.
  eapply live_in_transfer_istore; eauto.
  eapply transfer_succ_subset; eauto. simpl; auto.
Qed.

Lemma succ_in_transfer_icall f live pc sig ros args res succ r :
  analyze f = Some live ->
  (fn_code f) ! pc = Some (Icall sig ros args res succ) ->
  r <> res ->
  Regset.In r (transfer f succ (live !! succ)) ->
  Regset.In r (transfer f pc (live !! pc)).
Proof.
  intros LIVE Hpc Hneq Hr.
  eapply live_in_transfer_icall; eauto.
  eapply transfer_succ_subset; eauto. simpl; auto.
Qed.

Lemma succ_in_transfer_icond f live pc cond args ifso ifnot succ r :
  analyze f = Some live ->
  (fn_code f) ! pc = Some (Icond cond args ifso ifnot) ->
  In succ (successors_instr (Icond cond args ifso ifnot)) ->
  Regset.In r (transfer f succ (live !! succ)) ->
  Regset.In r (transfer f pc (live !! pc)).
Proof.
  intros LIVE Hpc Hsucc Hr.
  eapply live_in_transfer_icond; eauto.
  eapply transfer_succ_subset; eauto.
Qed.

Lemma succ_in_transfer_ijumptable f live pc arg tbl succ r :
  analyze f = Some live ->
  (fn_code f) ! pc = Some (Ijumptable arg tbl) ->
  In succ (successors_instr (Ijumptable arg tbl)) ->
  Regset.In r (transfer f succ (live !! succ)) ->
  Regset.In r (transfer f pc (live !! pc)).
Proof.
  intros LIVE Hpc Hsucc Hr.
  eapply live_in_transfer_ijumptable; eauto.
  eapply transfer_succ_subset; eauto.
Qed.

Lemma succ_in_transfer_ibuiltin f live pc ef args res succ r :
  analyze f = Some live ->
  (fn_code f) ! pc = Some (Ibuiltin ef args res succ) ->
  (forall x, res = BR x -> r <> x) ->
  Regset.In r (transfer f succ (live !! succ)) ->
  Regset.In r (transfer f pc (live !! pc)).
Proof.
  intros LIVE Hpc Hnotin Hr.
  eapply live_in_transfer_ibuiltin; eauto.
  eapply transfer_succ_subset; eauto. simpl; auto.
Qed.
