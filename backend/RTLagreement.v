Require Import
  AST
  Behaviors
  Builtins
  Builtins2
  Coqlib
  Events
  Globalenvs
  Integers
  Maps
  Memory
  Op
  Registers
  RTL
  RTL3
  Smallstep
  Values
.

Import ListNotations.

Section RTL_WEAK_AGREEMENT.
  Variable p : RTL.program.

  Definition rtl_sem2 := RTL.semantics p.
  Definition rtl_sem3 := RTL3.semantics p.

  Definition rtl_weak_agreement :=
    forall beh,
      program_behaves rtl_sem2 beh ->
      program_behaves rtl_sem3 beh.

  (** [rtl_weak_agreement'] says: for every RTL3 behavior [beh3],
      there exists an RTL behavior [beh2] such that RTL3's behavior
      is refined by RTL's behavior ([behavior_improves beh3 beh2]).

      [behavior_improves beh3 beh2] means: beh3 = beh2, or beh3 goes
      wrong at some trace that is a prefix of beh2. In other words,
      the RTL behavior is at least as good as the RTL3 behavior.

      This captures the fact that RTL (2-voting) is more lenient than
      RTL3 (3-voting): RTL3 may go wrong where RTL continues, because
      [vote3] produces Vundef while [vote] produces a value. *)

  Definition rtl_weak_agreement' :=
    forall beh3, program_behaves rtl_sem3 beh3 ->
            exists beh2, program_behaves rtl_sem2 beh2 /\ behavior_improves beh3 beh2.

End RTL_WEAK_AGREEMENT.

Section BRIDGE.

Variable p : RTL.program.
Let ge := Genv.globalenv p.

(** * External call bridge: external_call3 result is Val.lessdef the external_call result *)

Lemma replicate_builtin_sem3_lessdef_sem:
  forall b vargs vres3,
    replicate_builtin_sem3 b vargs = Some vres3 ->
    exists vres, replicate_builtin_sem b vargs = Some vres /\ Val.lessdef vres3 vres.
Proof.
  intros b vargs vres3 H.
  destruct b; simpl in *;
    try (exists vres3; split; [exact H | apply Val.lessdef_refl]).
  - destruct vargs as [| a [| b0 [| c [| ? ?]]]]; try discriminate.
    inv H. eexists; split. reflexivity. apply vote3_lessdef_vote.
  - destruct vargs as [| a [| b0 [| c [| ? ?]]]]; try discriminate.
    inv H. eexists; split. reflexivity. apply vote3_lessdef_vote.
  - destruct vargs as [| a [| b0 [| c [| ? ?]]]]; try discriminate.
    inv H. eexists; split. reflexivity. apply vote3_lessdef_vote.
  - destruct vargs as [| a [| b0 [| c [| ? ?]]]]; try discriminate.
    inv H. eexists; split. reflexivity. apply vote3_lessdef_vote.
Qed.

Lemma builtin_function_sem3_lessdef_sem:
  forall b vargs vres3,
    builtin_function_sem3 b vargs = Some vres3 ->
    exists vres, builtin_function_sem b vargs = Some vres /\ Val.lessdef vres3 vres.
Proof.
  intros b vargs vres3 H.
  destruct b as [sb | pb | rb]; simpl in *.
  - exists vres3; split; [exact H | apply Val.lessdef_refl].
  - exists vres3; split; [exact H | apply Val.lessdef_refl].
  - apply replicate_builtin_sem3_lessdef_sem; auto.
Qed.

Lemma known_builtin_sem3_lessdef_known_builtin_sem:
  forall bf vargs m t vres3 m',
    known_builtin_sem3 bf ge vargs m t vres3 m' ->
    exists vres, known_builtin_sem bf ge vargs m t vres m' /\ Val.lessdef vres3 vres.
Proof.
  intros bf vargs m t vres3 m' H. inv H.
  exploit builtin_function_sem3_lessdef_sem; eauto.
  intros (vres & HSEM & HLD).
  exists vres; split; auto. constructor; auto.
Qed.

Lemma external_call3_lessdef_external_call:
  forall ef vargs m t vres3 m',
    external_call3 ef ge vargs m t vres3 m' ->
    exists vres, external_call ef ge vargs m t vres m' /\ Val.lessdef vres3 vres.
Proof.
  intros ef vargs m t vres3 m' H.
  destruct ef; simpl in *.
  - exists vres3; split; [exact H | apply Val.lessdef_refl].
  - unfold builtin_or_external_sem3 in H. unfold builtin_or_external_sem.
    destruct (lookup_builtin_function name sg) as [bf |].
    + apply known_builtin_sem3_lessdef_known_builtin_sem; auto.
    + exists vres3; split; [exact H | apply Val.lessdef_refl].
  - unfold builtin_or_external_sem3 in H. unfold builtin_or_external_sem.
    destruct (lookup_builtin_function name sg) as [bf |].
    + apply known_builtin_sem3_lessdef_known_builtin_sem; auto.
    + exists vres3; split; [exact H | apply Val.lessdef_refl].
  - exists vres3; split; [exact H | apply Val.lessdef_refl].
  - exists vres3; split; [exact H | apply Val.lessdef_refl].
  - exists vres3; split; [exact H | apply Val.lessdef_refl].
  - exists vres3; split; [exact H | apply Val.lessdef_refl].
  - exists vres3; split; [exact H | apply Val.lessdef_refl].
  - exists vres3; split; [exact H | apply Val.lessdef_refl].
  - exists vres3; split; [exact H | apply Val.lessdef_refl].
  - exists vres3; split; [exact H | apply Val.lessdef_refl].
  - exists vres3; split; [exact H | apply Val.lessdef_refl].
Qed.

(** * Match relation for forward simulation RTL3 -> RTL *)

Inductive match_stackframes : RTL.stackframe -> RTL.stackframe -> Prop :=
  | match_stackframes_intro: forall res f sp pc rs3 rs,
      regs_lessdef rs3 rs ->
      match_stackframes (Stackframe res f sp pc rs3) (Stackframe res f sp pc rs).

Inductive match_states : RTL.state -> RTL.state -> Prop :=
  | match_regular: forall s3 s f sp pc rs3 rs m3 m,
      list_forall2 match_stackframes s3 s ->
      regs_lessdef rs3 rs ->
      Mem.extends m3 m ->
      match_states (State s3 f sp pc rs3 m3) (State s f sp pc rs m)
  | match_call: forall s3 s fd args3 args m3 m,
      list_forall2 match_stackframes s3 s ->
      Val.lessdef_list args3 args ->
      Mem.extends m3 m ->
      match_states (Callstate s3 fd args3 m3) (Callstate s fd args m)
  | match_return: forall s3 s v3 v m3 m,
      list_forall2 match_stackframes s3 s ->
      Val.lessdef v3 v ->
      Mem.extends m3 m ->
      match_states (Returnstate s3 v3 m3) (Returnstate s v m).

(** * Helper lemmas *)

Lemma find_function_lessdef:
  forall ros rs3 rs fd,
    regs_lessdef rs3 rs ->
    RTL.find_function ge ros rs3 = Some fd ->
    RTL.find_function ge ros rs = Some fd.
Proof.
  intros ros rs3 rs fd RLESSDEF FIND.
  destruct ros as [r | id]; simpl in *.
  - assert (HLD: Val.lessdef (rs3#r) (rs#r)) by apply RLESSDEF.
    destruct (rs3#r) eqn:E; simpl in FIND; try discriminate.
    inv HLD. auto.
  - auto.
Qed.

Lemma init_regs_lessdef:
  forall vl3 vl rl,
    Val.lessdef_list vl3 vl ->
    regs_lessdef (init_regs vl3 rl) (init_regs vl rl).
Proof.
  intros vl3 vl rl. revert vl3 vl.
  induction rl; simpl; intros.
  - red; intros. rewrite Regmap.gi. apply Val.lessdef_refl.
  - inv H.
    + red; intros. rewrite Regmap.gi. apply Val.lessdef_refl.
    + apply set_reg_lessdef; auto.
Qed.

Lemma regmap_optget_lessdef:
  forall or rs3 rs,
    regs_lessdef rs3 rs ->
    Val.lessdef (regmap_optget or Vundef rs3) (regmap_optget or Vundef rs).
Proof.
  intros or rs3 rs HLD. destruct or; simpl; auto.
Qed.

(** * Step simulation: every RTL3 step is matched by an RTL step *)

Lemma step_simulation:
  forall s3 t s3' s
    (STEP: RTL3.step ge s3 t s3')
    (MATCH: match_states s3 s),
    exists s', RTL.step ge s t s' /\ match_states s3' s'.
Proof.
  intros.
  destruct STEP as
    [ stk3 f sp pc rs3 m3 pc' HCODE
    | stk3 f sp pc rs3 m3 op args res pc' v HCODE HEVAL
    | stk3 f sp pc rs3 m3 chunk addr args dst pc' a v HCODE HADDR HLOAD
    | stk3 f sp pc rs3 m3 chunk addr args src pc' a m3' HCODE HADDR HSTORE
    | stk3 f sp pc rs3 m3 sig ros args res pc' fd HCODE HFIND HSIG
    | stk3 f blk pc rs3 m3 sig ros args fd m3' HCODE HFIND HSIG HFREE
    | stk3 f sp pc rs3 m3 ef bargs bres pc' vargs t vres m3' HCODE HEVAL HEC3
    | stk3 f sp pc rs3 m3 cond args ifso ifnot b pc' HCODE HCOND HPC
    | stk3 f sp pc rs3 m3 arg tbl n pc' HCODE HARG HNTH
    | stk3 f blk pc rs3 m3 or m3' HCODE HFREE
    | stk3 fn args3 m3 m3' blk HTYPES HALLOC
    | stk3 ef args3 res t m3 m3' HEC3
    | res f sp pc rs3 stk3 vres m3
    ];
  inv MATCH.

  - (* exec_Inop *)
    eexists; split.
    + eapply RTL.exec_Inop; eauto.
    + econstructor; eauto.

  - (* exec_Iop *)
    exploit eval_operation_lessdef. eapply regs_lessdef_regs; eauto. eauto. eauto.
    intros (v2 & EVAL2 & VLD).
    eexists; split.
    + eapply RTL.exec_Iop; eauto.
    + econstructor; eauto. apply set_reg_lessdef; auto.

  - (* exec_Iload *)
    exploit eval_addressing_lessdef. eapply regs_lessdef_regs; eauto. eauto.
    intros (a2 & ADDR2 & ALD).
    exploit Mem.loadv_extends; eauto.
    intros (v2 & LOAD2 & VLD).
    eexists; split.
    + eapply RTL.exec_Iload; eauto.
    + econstructor; eauto. apply set_reg_lessdef; auto.

  - (* exec_Istore *)
    exploit eval_addressing_lessdef. eapply regs_lessdef_regs; eauto. eauto.
    intros (a2 & ADDR2 & ALD).
    exploit Mem.storev_extends; eauto.
    intros (m2' & STORE2 & MEXT').
    eexists; split.
    + eapply RTL.exec_Istore; eauto.
    + econstructor; eauto.

  - (* exec_Icall *)
    exploit find_function_lessdef; eauto.
    intros FIND2.
    eexists; split.
    + eapply RTL.exec_Icall; eauto.
    + econstructor.
      * constructor; auto. constructor; auto.
      * eapply regs_lessdef_regs; eauto.
      * eauto.

  - (* exec_Itailcall *)
    exploit find_function_lessdef; eauto.
    intros FIND2.
    exploit Mem.free_parallel_extends; eauto.
    intros (m2' & FREE2 & MEXT').
    eexists; split.
    + eapply RTL.exec_Itailcall; eauto.
    + econstructor; eauto.
      eapply regs_lessdef_regs; eauto.

  - (* exec_Ibuiltin -- KEY CASE *)
    match goal with
    | [ RLD: regs_lessdef ?rs_3 ?rs_2, MEXT: Mem.extends ?m_3 ?m_2 |- _ ] =>
      edestruct (@eval_builtin_args_lessdef _ ge (fun r => rs_3#r) (fun r => rs_2#r) sp m_3 m_2)
        as (vargs2 & EVALBA & VALD3);
      [ intros x; apply RLD | exact MEXT | exact HEVAL |]
    end.
    exploit external_call3_lessdef_external_call; eauto.
    intros (vres_mid & EC_MID & VLD_MID).
    match goal with
    | [ MEXT: Mem.extends _ ?m_2 |- _ ] =>
      edestruct (external_call_mem_extends ef ge)
        as (vres' & m2' & EC2 & VLD' & MEXT' & _);
      [ exact EC_MID | exact MEXT | exact VALD3 |]
    end.
    eexists; split.
    + eapply RTL.exec_Ibuiltin; eauto.
    + econstructor; eauto.
      apply set_res_lessdef; auto.
      eapply Val.lessdef_trans; eauto.

  - (* exec_Icond *)
    exploit eval_condition_lessdef. eapply regs_lessdef_regs; eauto. eauto. eauto.
    intros COND2.
    eexists; split.
    + eapply RTL.exec_Icond; eauto.
    + econstructor; eauto.

  - (* exec_Ijumptable *)
    assert (HARG2: rs#arg = Vint n).
    { match goal with
      | [ RLD: regs_lessdef _ ?rs2 |- ?rs2 # _ = _ ] =>
        generalize (RLD arg); rewrite HARG; intro HLD; inv HLD; auto
      end. }
    eexists; split.
    + eapply RTL.exec_Ijumptable; eauto.
    + econstructor; eauto.

  - (* exec_Ireturn *)
    exploit Mem.free_parallel_extends; eauto.
    intros (m2' & FREE2 & MEXT').
    eexists; split.
    + eapply RTL.exec_Ireturn; eauto.
    + econstructor; eauto.
      apply regmap_optget_lessdef; auto.

  - (* exec_function_internal *)
    exploit Mem.alloc_extends; eauto.
    { apply Z.le_refl. }
    { apply Z.le_refl. }
    intros (m2' & ALLOC2 & MEXT').
    eexists; split.
    + eapply RTL.exec_function_internal; eauto.
      eapply Val.has_argtype_list_lessdef; eauto.
    + econstructor; eauto.
      apply init_regs_lessdef; auto.

  - (* exec_function_external -- KEY CASE *)
    exploit external_call3_lessdef_external_call; eauto.
    intros (vres_mid & EC_MID & VLD_MID).
    match goal with
    | [ MEXT: Mem.extends _ ?m_2, LD: Val.lessdef_list _ ?args_2 |- _ ] =>
      edestruct (external_call_mem_extends ef ge)
        as (vres' & m2' & EC2 & VLD' & MEXT' & _);
      [ exact EC_MID | exact MEXT | exact LD |]
    end.
    eexists; split.
    + eapply RTL.exec_function_external; eauto.
    + econstructor; eauto.
      eapply Val.lessdef_trans; eauto.

  - (* exec_return *)
    match goal with
    | [ LF: list_forall2 match_stackframes (_ :: _) _ |- _ ] =>
      inv LF;
      match goal with
      | [ MSF: match_stackframes _ _ |- _ ] => inv MSF
      end
    end.
    eexists; split.
    + eapply RTL.exec_return.
    + econstructor; eauto.
      apply set_reg_lessdef; auto.
Qed.

(** * Forward simulation RTL3 -> RTL *)

Theorem rtl3_rtl_forward_simulation :
  forward_simulation (RTL3.semantics p) (RTL.semantics p).
Proof.
  apply forward_simulation_step with match_states.
  - intros. reflexivity.
  - intros s1 INIT. inv INIT.
    eexists; split.
    + econstructor; eauto.
    + econstructor.
      * constructor.
      * constructor.
      * apply Mem.extends_refl.
  - intros s1 s2 r MATCH FINAL. inv FINAL. inv MATCH.
    match goal with
    | [ LF: list_forall2 _ nil _, VLD: Val.lessdef (Vint _) _ |- _ ] =>
      inv LF; inv VLD; econstructor
    end.
  - intros. eapply step_simulation; eauto.
Qed.

(** * Backward simulation and behavior-level results *)

Corollary rtl3_rtl_backward_simulation :
  backward_simulation (RTL3.semantics p) (RTL.semantics p).
Proof.
  apply forward_to_backward_simulation.
  - exact rtl3_rtl_forward_simulation.
  - apply RTL3.semantics_receptive.
  - apply RTL.semantics_determinate.
Qed.

(** [rtl_weak_agreement'] proved directly from [forward_simulation_behavior_improves].

    The forward simulation RTL3 -> RTL gives: for every RTL3 behavior,
    RTL has a behavior that is at least as good. Specifically,
    [behavior_improves beh3 beh2] holds, meaning if RTL3 goes wrong at
    some trace, RTL has at least that trace as a prefix. *)

Theorem rtl_weak_agreement_no_novotes :
  rtl_weak_agreement' p.
Proof.
  unfold rtl_weak_agreement'.
  intros beh3 HBEH.
  eapply forward_simulation_behavior_improves; eauto.
  exact rtl3_rtl_forward_simulation.
Qed.

End BRIDGE.
