Require Import
  AST
  Behaviors
  Builtins2
  Coqlib
  Events
  Globalenvs
  Linking
  Maps
  Registers
  Replicate
  Replicatespec
  RTL
  RTLcolor
  RTLfault
  Smallstep
  Values
.

Import ListNotations.
Local Open Scope string_scope.

Definition match_rs (col : reg -> option color) (faulted : bool) (rs1 rs2 : regset) : Prop :=
  if faulted then
    exists c, is_basic c /\
           forall r, (col r <> Some c -> Val.lessdef (rs1 # r) (rs2 # r)) /\
                  (* TODO: remove this second condition? Need to use
                     more permissive vote semantics. *)
                  (col r = Some c -> val_compat (rs1 # r) (rs2 # r))
  else
    forall r, Val.lessdef (rs1 # r) (rs2 # r).

Lemma trace_prefix_cons e t1 t2 :
  trace_prefix t1 t2 ->
  trace_prefix (e :: t1) (e :: t2).
Proof.
  intros [? ?]; subst.
  eexists; reflexivity.
Qed.

Lemma Eappinf_eq_trace_prefix t1 t2 T1 T2 :
  t1 *** T1 = t2 *** T2 ->
  trace_prefix t1 t2 \/ trace_prefix t2 t1.
Proof.
  revert t2 T1 T2.
  induction t1; simpl; intros t2 T1 T2 Heq; subst.
  { left; eexists; reflexivity. }
  destruct t2.
  { right; eexists; reflexivity. }
  inv Heq.
  apply IHt1 in H1.
  destruct H1 as [Hpre | Hpre].
  - left; apply trace_prefix_cons; auto.
  - right; apply trace_prefix_cons; auto.
Qed.

Lemma traceinf_prefix_trace_prefix t t' T :
  (length t' >= length t)%nat ->
  traceinf_prefix t' (t *** T) ->
  trace_prefix t t'.
Proof.
  revert t T.
  induction t'; simpl; intros t T Hlen Hpre.
  { destruct t; simpl in *; try lia.
    eexists; reflexivity. }
  destruct t.
  { eexists; reflexivity. }
  simpl in Hlen.
  simpl in Hpre.
  destruct Hpre as [T' H].
  inv H.
  apply trace_prefix_cons.
  apply Eappinf_eq_trace_prefix in H2.
  destruct H2 as [Hpre | Hpre].
  - auto.
  - destruct Hpre as [? ?]; subst.
    eapply IHt'; try lia.
    exists (x *** T).
    apply Eappinf_assoc.
Qed.

Lemma reactive_prefix_exists_star sem s t T :
  Forever_reactive sem s T ->
  traceinf_prefix t T ->
  exists s' t', Star sem s t' s' /\ trace_prefix t t'.
Proof.
  intros Hreact [T' Hpre]; subst.
  rename T' into T.
  apply forever_reactive_forever_reactive' in Hreact.
  unfold forever_reactive' in Hreact.
  specialize (Hreact (length t)).
  destruct Hreact as (s' & t' & Hstar & Hlen & Hpre).
  exists s', t'; split; auto.
  eapply traceinf_prefix_trace_prefix; eauto.
Qed.

Section match_states.

  (** When a fault has occurred elsewhere and regsets [rs1] and [rs2]
      are unchanged, they still match. *)
  Lemma match_rs_fault col (pc : node) (rs1 rs2 : regset) :
    match_rs (col pc) false rs1 rs2 ->
    match_rs (col pc) true rs1 rs2.
  Proof.
    intro H; exists Red; split; constructor; auto.
    intro Hcol; apply val_lessdef_compat; auto.
  Qed.

  Inductive match_stackframes (faulted : bool)
    : RTL.stackframe -> RTL.stackframe -> Prop :=
  | match_stackframes_Stackframe : forall col res f1 f2 sp pc rs1 rs2
      (* (MATCH: match_votes_function f1 f2) *)
      (WC: wc_function col f1)
      (RS: match_rs (col pc) faulted rs1 rs2),
      match_stackframes faulted
        (Stackframe res f1 sp pc rs1)
        (Stackframe res f2 sp pc rs2).

  (** When a fault has occurred elsewhere and stackframes [sf1] and
      [sf2] are unchanged, they still match. *)
  Lemma match_stackframes_fault (sf1 sf2 : RTL.stackframe) :
    match_stackframes false sf1 sf2 ->
    match_stackframes true sf1 sf2.
  Proof.
    intro H; inv H.
    econstructor; eauto.
    apply match_rs_fault; auto.
  Qed.

  (** When a fault hasn't occurred, Val.lessdef should hold between
      all registers. When a fault has occurred, it should hold between
      all registers except those of the affected color. *)
  Inductive match_states : RTL.state -> fstate -> Prop :=
  (* TODO: need lessdef on memories. *)
  | match_states_State :
    forall col stk1 stk2 f sp pc rs1 rs2 m (b : bool)
      (STK: Forall2 (match_stackframes b) stk1 stk2)
      (* (VOTE: match_votes_function f1 f2) *)
      (WC: wc_function col f)
      (RS: match_rs (col pc) b rs1 rs2),
      match_states (State stk1 f sp pc rs1 m)
                   {| fs_state := State stk2 f sp pc rs2 m; fault := b |}
  | match_states_Callstate :
    forall stk1 stk2 fd args1 args2 m b
      (STK: Forall2 (match_stackframes b) stk1 stk2)
      (* (VOTE: match_votes_fundef fd1 fd2) *)
      (LESSDEF: Forall2 Val.lessdef args1 args2),
      match_states (Callstate stk1 fd args1 m)
                   {| fs_state := Callstate stk2 fd args2 m; fault := b |}
  | match_state_Returnstate :
    forall stk1 stk2 v1 v2 m b
      (STK: Forall2 (match_stackframes b) stk1 stk2)
      (LESSDEF: Val.lessdef v1 v2),
      match_states (Returnstate stk1 v1 m)
                   {| fs_state := Returnstate stk2 v2 m; fault := b |}.

End match_states.

Section TOLERANCE.
  Variable prog : program.
  (* Variable prog2 : program. *)
  (* Hypothesis PROG : match_votes_program prog1 prog2. *)
  Let ge := Genv.globalenv prog.
  (* Let ge2 := Genv.globalenv prog2. *)

  Hypothesis WC : wc_program prog.

  (* Corollary wc_prog2 : wc_program col prog2. *)
  (* Proof. eapply match_votes_wc; eauto. Qed. *)

  (* Lemma match_votes_function_not_builtin f1 f2 pc i : *)
  (*   not_builtin i -> *)
  (*   (fn_code f1) ! pc = Some i -> *)
  (*   (* match_votes_function f1 f2 -> *) *)
  (*   (fn_code f2) ! pc = Some i. *)
  (* Proof. *)
  (*   intros Hi Hpc Hmatch. *)
  (*   inv Hmatch. *)
  (*   simpl in *. *)
  (*   specialize (CODE pc). *)
  (*   inv CODE; try congruence. *)
  (*   inv HR; try congruence. *)
  (*   rewrite <- H0 in Hpc; inv Hpc. *)
  (*   inv Hi. *)
  (* Qed. *)

  Theorem faulty_step_exists s t s' fs :
    match_states s fs ->
    Step (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s t s' ->
    exists t' fs', Step (faulty_semantics prog) fs t' fs'.
  Proof.
    intros Hmatch Hstep.
    inv Hstep.
    - destruct fs.
      inv Hmatch.
      eexists; eexists.
      econstructor.
      + apply exec_Inop; eauto.
      + constructor.
    - destruct fs.
      inv Hmatch.
      eexists; eexists.
      econstructor.
      + eapply exec_Iop; eauto.
        (* By RS, in rs2 all the args are at least as defined as (and
           compatible with) their values in rs.  *)
        admit.
      + constructor.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  Theorem faulty_step_simulation s t s' fs t' fs' :
    match_states s fs ->
    Step (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s t s' ->
    Step (faulty_semantics prog) fs t' fs' ->
    t = t' /\ match_states s' fs'.
  Proof.
    intros Hmatch Hstep Hfstep.
    inv Hstep.

    (* exec_Inop *)
    - inv Hmatch.
      (* inv VOTE. *)
      simpl in *.
      (* generalize (CODE pc); intro Hmatchvote. *)
      (* inv Hmatchvote; try congruence. *)
      (* inv HR; try congruence. *)
      inv Hfstep.
      inv ZAP.
      + inv STEP; simpl in *; try congruence.
        split; auto.
        rewrite H in H8; inv H8.
        econstructor; eauto.
        admit.
      + inv STEP; simpl in *; try congruence.
        split; auto.
        rewrite H in H8; inv H8.
        econstructor; eauto.
        { eapply Forall2_impl.
          2: { eauto. }
          intros; apply match_stackframes_fault; auto. }
        (* { constructor; auto. } *)
        (* unfold match_rs. *)
        (* exists (col pc0 r); split. *)
        (* * admit. *)
    (* * admit. *)
        admit.

    (* exec_Iop *)
    - admit.
    (* exec_Iload *)
    - admit.
    (* exec_Istore *)
    - admit.
    (* exec_Icall *)
    - admit.
    (* exec_Itailcall *)
    - admit.
    (* exec_Ibuiltin *)
    - admit.
    (* exec_Icond *)
    - admit.
    (* exec_Ijumptable *)
    - admit.
    (* exec_Ireturn *)
    - admit.
    (* exec_function_internal *)
    - admit.
    (* exec_function_external *)
    - admit.
    (* exec_return *)
    - admit.
  Admitted.

  Corollary faulty_star_step_exists s t s' fs :
    match_states s fs ->
    Star (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s t s' ->
    exists fs', Star (faulty_semantics prog) fs t fs' /\ match_states s' fs'.
  Proof.
    intros Hmatch Hstar.
    revert Hmatch.
    revert fs.
    induction Hstar; intros fs Hmatch.
    { exists fs; split; auto; apply star_refl. }
    subst.
    pose proof H as Hstep.
    eapply faulty_step_exists in Hstep; eauto.
    destruct Hstep as (t' & fs' & Hfstep).
    eapply faulty_step_simulation in H; eauto.
    destruct H as [? Hmatch']; subst.
    eapply IHHstar in Hmatch'.
    destruct Hmatch' as (fs'' & Hstar'' & Hmatch'').
    exists fs''; split; auto.
    eapply star_step; eauto.
  Qed.

  Lemma initial_states_match s fs :
    initial_state (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s ->
    initial_state (faulty_semantics prog) fs ->
    match_states s fs.
  Proof.
    simpl; intros Hs Hfs.
    inv Hs; inv Hfs; inv H3.
    unfold ge0 in *.
    unfold ge1 in *.
    unfold ge0 in *.
    unfold ge1 in *.
    rewrite H0 in H5; inv H5.
    rewrite H in H4; inv H4.
    rewrite H1 in H6; inv H6.
    constructor; auto.
  Qed.

  Lemma final_state_faulty_nostep s fs r :
    match_states s fs ->
    final_state (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s r ->
    Nostep (faulty_semantics prog) fs.
  Proof.
    intros Hmatch Hfin.
    inv Hfin; inv Hmatch.
    intros t fs' Hfstep.
    inv Hfstep; inv STK; inv STEP.
  Qed.

  Lemma final_state_nostep s fs r :
    match_states s fs ->
    final_state (faulty_semantics prog) fs r ->
    Nostep (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s.
  Proof.
    intros Hmatch Hfin t s' Hstep.
    inv Hfin; inv Hmatch; simpl in *; try congruence.
    inv H0; inv STK; inv LESSDEF; inv Hstep.
  Qed.

  Lemma star_final_prog1_not_forever_silent t s s' fs r :
    match_states s fs ->
    Star (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s t s' ->
    final_state (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s' r ->
    Forever_silent (faulty_semantics prog) fs ->
    False.
  Proof.
    intros H Hstar.
    revert H.
    revert fs r.
    induction Hstar; intros fs r Hmatch Hfin Hsil; inv Hsil.
    - eapply final_state_faulty_nostep in Hfin; eauto.
      eapply Hfin; eauto.
    - eapply faulty_step_simulation in H; eauto.
      destruct H as [? Hmatch']; subst.
      eapply IHHstar; eauto.
  Qed.

  Lemma terminates_diverges_False t t' s s' fs fs' r :
    match_states s fs ->
    Star (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s t s' ->
    final_state (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s' r ->
    Star (faulty_semantics prog) fs t' fs' ->
    Forever_silent (faulty_semantics prog) fs' ->
    False.
  Proof.
    intros Hmatch Hstar Hfin Hstar' Hsil.
    revert Hmatch Hstar Hfin Hsil.
    revert s t s' r.
    induction Hstar'; intros s0 t' s' r Hmatch Hstar Hfin Hsil.
    - eapply star_final_prog1_not_forever_silent; eauto.
    - inv Hstar.
      + eapply final_state_faulty_nostep in Hfin; eauto.
        eapply Hfin; eauto.
      + eapply faulty_step_simulation in H; eauto.
        destruct H as [? Hmatch']; subst.
        eapply IHHstar'; eauto.
  Qed.

  (* This isn't true because RTL.final_state requires that the result
     value be a Vint, but here it could be Vundef. *)
  (* Lemma faulty_final_state_final s fs r : *)
  (*   match_states col s fs -> *)
  (*   final_state (faulty_semantics prog2) fs r -> *)
  (*   final_state (RTL.semantics prog1) s r. *)
  (* Proof. *)
  (*   intros Hmatch Hfin. *)
  (*   inv Hfin; inv Hmatch; simpl in *; try congruence. *)
  (*   inv H0; inv STK. *)    

  Lemma star_final_prog2_not_silent t s fs fs' r :
    match_states s fs ->
    Forever_silent (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s ->
    Star (faulty_semantics prog) fs t fs' ->
    final_state (faulty_semantics prog) fs' r ->
    False.
  Proof.
    intros Hmatch Hsil Hstar.
    revert Hmatch Hsil.
    revert s r.
    induction Hstar; intros s0 r Hmatch Hsil Hfin; inv Hsil.
    - eapply final_state_nostep in Hfin; eauto.
      eapply Hfin; eauto.
    - eapply faulty_step_simulation in H1; eauto.
      destruct H1 as [? Hmatch']; subst.
      eapply IHHstar; eauto.
  Qed.

  Lemma diverges_terminates_False t t' s s' fs fs' r :
    match_states s fs ->
    Star (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s t s' ->
    Forever_silent (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s' ->
    Star (faulty_semantics prog) fs t' fs' ->
    final_state (faulty_semantics prog) fs' r ->
    False.
  Proof.
    intros Hmatch Hstar.
    revert Hmatch.
    revert fs t' fs' r.
    induction Hstar; intros fs t' fs' r Hmatch Hsil Hstar' Hfin.
    - eapply star_final_prog2_not_silent; eauto.
    - inv Hstar'.
      + eapply final_state_nostep in Hfin; eauto.
        eapply Hfin; eauto.
      + eapply faulty_step_simulation in H1; eauto.
        destruct H1 as [? Hmatch']; subst.
        eapply IHHstar; eauto.
  Qed.

  Lemma reacts_terminates_False t s fs fs' r T :
    match_states s fs ->
    Forever_reactive (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s T ->
    Star (faulty_semantics prog) fs t fs' ->
    final_state (faulty_semantics prog) fs' r ->
    False.
  Proof.
    intros Hmatch Hreact Hstar.
    revert Hmatch Hreact.
    revert s r T.
    induction Hstar; intros s0 r T Hmatch Hreact Hfin.
    { inv Hreact.
      inv H; try congruence.
      eapply final_state_nostep in Hfin; eauto.
      eapply Hfin; eauto. }
    subst.
    inv Hreact.
    inv H0; try congruence.
    eapply faulty_step_simulation in H; eauto.
    destruct H as [? Hmatch']; subst.
    eapply IHHstar; eauto.
    eapply star_forever_reactive; eauto.
  Qed.

  Lemma star_silent_trace s t s' fs :
    match_states s fs ->
    Star (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s t s' -> 
    Forever_silent (faulty_semantics prog) fs ->
    t = E0.
  Proof.
    intros Hmatch Hstar.
    revert Hmatch.
    revert fs.
    induction Hstar; intros fs Hmatch Hsil; auto.
    inv Hsil.
    eapply faulty_step_simulation in H; eauto.
    destruct H as [? Hmatch']; subst; simpl.
    eapply IHHstar; eauto.
  Qed.

  Lemma reactive_not_silent s fs T :
    match_states s fs ->
    Forever_reactive (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s T ->
    Forever_silent (faulty_semantics prog) fs ->
    False.
  Proof.
    intros Hmatch Hreact Hsil.
    inv Hreact.
    eapply star_silent_trace in H; eauto.
  Qed.

  Lemma reacts_diverges_False t s fs fs' T :
    match_states s fs ->
    Forever_reactive (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s T ->
    Star (faulty_semantics prog) fs t fs' ->
    Forever_silent (faulty_semantics prog) fs' ->
    False.
  Proof.
    intros Hmatch Hreact Hstar.
    revert Hmatch Hreact.
    revert s T.
    induction Hstar; intros s0 T Hmatch Hreact Hfin.
    { eapply reactive_not_silent; eauto. }
    subst.
    inv Hreact.
    inv H0; try congruence.
    eapply faulty_step_simulation in H; eauto.
    destruct H as [? Hmatch']; subst.
    eapply IHHstar; eauto.
    eapply star_forever_reactive; eauto.
  Qed.

  (* Can't do other direction because prog1 can get stuck. *)
  Lemma match_states_forever_silent s fs :
    match_states s fs ->
    Forever_silent (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s ->
      Forever_silent (faulty_semantics prog) fs.
  Proof.
    revert s fs.
    cofix CH.
    intros s fs Hmatch Hsil.
    inv Hsil.
    pose proof H as Hstep.
    eapply faulty_step_exists in Hstep; eauto.
    destruct Hstep as (t' & fs' & Hfstep).
    eapply faulty_step_simulation in H; eauto.
    destruct H as [? Hmatch']; subst.
    econstructor; eauto.
  Qed.

  (* Can't do other direction because prog1 can get stuck. *)
  Lemma match_states_forever_reactive s fs T :
    match_states s fs ->
    Forever_reactive (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s T ->
      Forever_reactive (faulty_semantics prog) fs T.
  Proof.
    revert s fs T.
    cofix CH.
    intros s fs T Hmatch Hreact.
    inv Hreact.
    pose proof H as Hstar.
    eapply faulty_star_step_exists in Hstar; eauto.
    destruct Hstar as (t' & fs' & Hstar').
    econstructor; eauto.
  Qed.

  Lemma star_faulty_silent_trace s fs t fs' :
    match_states s fs ->
    Forever_silent (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s ->
    Star (faulty_semantics prog) fs t fs' ->
    t = E0.
  Proof.
    intros Hmatch Hsil Hstar.
    revert Hmatch Hsil.
    revert s.
    induction Hstar; intros s0 Hmatch Hsil; auto.
    inv Hsil.
    eapply faulty_step_simulation in H; eauto.
    destruct H as [? Hmatch']; subst; simpl.
    eapply IHHstar; eauto.
  Qed.

  Lemma silent_not_reactive s fs T :
    match_states s fs ->
    Forever_silent (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s ->
    Forever_reactive (faulty_semantics prog) fs T ->
    False.
  Proof.
    intros Hmatch Hsil Hreact.
    inv Hreact.
    eapply star_faulty_silent_trace in H; eauto.
  Qed.

  Lemma star_silent_not_reactive t s s' fs T :
    match_states s fs ->
    Star (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s t s' ->
    Forever_silent (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s' ->
    Forever_reactive (faulty_semantics prog) fs T ->
    False.
  Proof.
    intros Hmatch Hstar.
    revert Hmatch.
    revert fs T.
    induction Hstar; intros fs T Hmatch Hsil Hreact.
    - eapply silent_not_reactive; eauto.
    - subst.
      inv Hreact.
      inv H0; try congruence.
      eapply faulty_step_simulation in H3; eauto.
      destruct H3 as [? Hmatch']; subst.
      eapply IHHstar; eauto.
      eapply star_forever_reactive; eauto.
  Qed.

  Lemma star_final_not_reactive t s s' fs r T :
    match_states s fs ->
    Star (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s t s' ->
    final_state (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s' r ->
    Forever_reactive (faulty_semantics prog) fs T ->
    False.
  Proof.
    intros H Hstar.
    revert H.
    revert fs r T.
    induction Hstar; intros fs r T Hmatch Hfin Hreact; inv Hreact.
    - inv H; try congruence.
      eapply final_state_faulty_nostep in Hfin; eauto.
      eapply Hfin; eauto.
    - inv H1; try congruence.
      eapply faulty_step_simulation in H; eauto.
      destruct H as [? Hmatch']; subst.
      eapply IHHstar; eauto.
      eapply star_forever_reactive; eauto.
  Qed.

  Lemma match_states_final s fs r :
    match_states s fs ->
    final_state (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s r ->
    final_state (faulty_semantics prog) fs r.
  Proof.
    intros Hmatch Hfin; inv Hfin.
    inv Hmatch; inv STK; inv LESSDEF.
    constructor.
  Qed.

  Lemma faulty_final_state_nostep fs r :
    final_state (faulty_semantics prog) fs r ->
    Nostep (faulty_semantics prog) fs.
  Proof.
    intro Hfin; inv Hfin.
    destruct fs; simpl in *; rewrite <- H0.
    intros t fs' Hstep; inv Hstep; inv STEP.
  Qed.

  Lemma star_final_nostep_final s t s' r fs :
    match_states s fs ->
    Star (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s t s' ->
    final_state (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s' r ->
    Nostep (faulty_semantics prog) fs ->
    final_state (faulty_semantics prog) fs r.
  Proof.
    intros Hmatch Hstar Hfin Hnostep.
    inv Hstar.
    { eapply match_states_final; eauto. }
    eapply faulty_step_exists in H; eauto.
    destruct H as (t' & fs' & Hfstep).
    exfalso; eapply Hnostep; eauto.
  Qed.

  Lemma star_final_star_nostep_final s t s' r fs t' fs' :
    match_states s fs ->
    Star (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s t s' ->
    final_state (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s' r ->
    Star (faulty_semantics prog) fs t' fs' ->
    Nostep (faulty_semantics prog) fs' ->
    final_state (faulty_semantics prog) fs' r.
  Proof.
    intros Hmatch Hstar Hfin Hstar'.
    revert Hmatch Hstar Hfin.
    revert s t s' r.
    induction Hstar'; intros s0 t0 s' r Hmatch Hstar Hfin Hnostep.
    { eapply star_final_nostep_final; eauto. }
    inv Hstar.
    - clear IHHstar'.
      exfalso.
      eapply match_states_final in Hfin; eauto.
      eapply faulty_final_state_nostep; eauto.
    - eapply IHHstar'; auto.
      3: { eauto. }
      2: { eauto. }
      eapply faulty_step_simulation; eauto.
  Qed.

  Lemma star_final_final s t s' r fs r' :
    match_states s fs ->
    Star (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s t s' ->
    final_state (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s' r ->
    final_state (faulty_semantics prog) fs r' ->
    t = E0 /\ r = r'.
  Proof.
    intros Hmatch Hstar Hfin Hfin'.
    inv Hstar.
    - split; auto.
      inv Hfin; inv Hfin'; inv Hmatch.
      inv H0; inv LESSDEF; reflexivity.
    - exfalso; eapply final_state_nostep; eauto.
  Qed.

  Lemma star_final_star_final s t s' r fs t' fs' r' :
    match_states s fs ->
    Star (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s t s' ->
    final_state (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s' r ->
    Star (faulty_semantics prog) fs t' fs' ->
    final_state (faulty_semantics prog) fs' r' ->
    t = t' /\ r = r'.
  Proof.
    intros Hmatch Hstar Hfin Hstar'.
    revert Hmatch Hstar Hfin.
    revert s t s' r r'.
    induction Hstar'; intros s0 t' s' r r' Hmatch Hstar Hfin Hfin'.
    { eapply star_final_final; eauto. }
    inv Hstar.
    - exfalso; eapply final_state_faulty_nostep; eauto.
    - cut (t3 = t2 /\ r = r').
      { intros [? ?]; subst; split; auto; f_equal.
        eapply faulty_step_simulation; eauto. }
      eapply IHHstar'; eauto.
      eapply faulty_step_simulation; eauto.
  Qed.

  Lemma star_silent_star_silent s t s' fs t' fs' :
    match_states s fs ->
    Star (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s t s' ->
    Forever_silent (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s' ->
    Star (faulty_semantics prog) fs t' fs' ->
    Forever_silent (faulty_semantics prog) fs' ->
    t = t'.
  Proof.
    intros Hmatch Hstar Hsil Hstar'.
    revert Hmatch Hstar Hsil.
    revert s t s'.
    induction Hstar'; intros s0 t' s' Hmatch Hstar Hsil Hsil'.
    { eapply star_silent_trace; eauto. }
    subst.
    inv Hstar.
    - inv Hsil.
      eapply faulty_step_simulation in H0; eauto.
      destruct H0 as [? Hmatch']; subst; simpl.
      eapply IHHstar'; eauto.
      apply star_refl.
    - eapply faulty_step_simulation in H0; eauto.
      destruct H0 as [? Hmatch']; subst; f_equal.
      eapply IHHstar'; eauto.
  Qed.

  Lemma silent_not_star_stuck s fs t fs' :
    match_states s fs ->
    Forever_silent (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s ->
    Star (faulty_semantics prog) fs t fs' ->
    Nostep (faulty_semantics prog) fs' ->
    False.
  Proof.
    intros Hmatch Hsil Hstar.
    revert Hmatch Hsil.
    revert s.
    induction Hstar; intros s0 Hmatch Hsil Hnostep.
    { inv Hsil.
      eapply faulty_step_exists in H; eauto.
      destruct H as (t' & fs' & Hfstep).
      eapply Hnostep; eauto. }
    subst.
    inv Hsil.
    eapply faulty_step_simulation in H; eauto.
    destruct H as [? Hmatch']; subst.
    eapply IHHstar; eauto.
  Qed.

  Lemma star_silent_star_not_stuck s t s' fs t' fs' :
    match_states s fs ->
    Star (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s t s' ->
    Forever_silent (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s' ->
    Star (faulty_semantics prog) fs t' fs' ->
    Nostep (faulty_semantics prog) fs' ->
    False.
  Proof.
    intros Hmatch Hstar.
    revert Hmatch.
    revert fs t' fs'.
    induction Hstar; intros fs t' fs' Hmatch Hsil Hstar' Hnostep.
    { eapply silent_not_star_stuck; eauto. }
    subst.
    inv Hstar'.
    { eapply faulty_step_exists in H; eauto.
      destruct H as (t' & fs'' & Hfstep).
      eapply Hnostep; eauto. }
    eapply faulty_step_simulation in H; eauto.
    destruct H as [? Hmatch']; subst.
    eapply IHHstar; eauto.
  Qed.

  Lemma reactive_star_not_stuck s fs t' fs' T :
    match_states s fs ->
    Forever_reactive (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s T ->
    Star (faulty_semantics prog) fs t' fs' ->
    Nostep (faulty_semantics prog) fs' ->
    False.
  Proof.
    intros Hmatch Hreact Hstar.
    revert Hmatch Hreact.
    revert s T.
    induction Hstar; intros s0 T Hmatch Hreact Hnostep.
    { inv Hreact.
      inv H; try congruence.
      eapply faulty_step_exists in H2; eauto.
      destruct H2 as (t' & fs' & Hfstep).
      eapply Hnostep; eauto. }
    subst.
    inv Hreact.
    inv H0; try congruence.
    eapply faulty_step_simulation in H; eauto.
    destruct H as [? Hmatch']; subst.
    eapply IHHstar; eauto.
    eapply star_forever_reactive; eauto.
  Qed.

  Lemma traceinf_prefix_cons e t T :
    traceinf_prefix t T ->
    traceinf_prefix (e :: t) (Econsinf e T).
  Proof.
    intro Ht.
    unfold traceinf_prefix; simpl.
    destruct Ht as [T' Ht].
    exists T'; f_equal; auto.
  Qed.    

  Lemma prefixes_comparable_traceinf_sim T1 T2 :
    (forall t1 t2, traceinf_prefix t1 T1 ->
              traceinf_prefix t2 T2 ->
              trace_prefix t1 t2 \/ trace_prefix t2 t1) ->
    traceinf_sim T1 T2.
  Proof.
    revert T1 T2.
    cofix CH.
    intros T1 T2 Ht.
    destruct T1, T2.
    replace e0 with e in *.
    2: { specialize (Ht [e] [e0]).
         assert (H0: traceinf_prefix [e] (Econsinf e T1)).
         { exists T1; reflexivity. }
         assert (H1: traceinf_prefix [e0] (Econsinf e0 T2)).
         { exists T2; reflexivity. }
         destruct (Ht H0 H1) as [Ht' | Ht'].
         - destruct Ht' as [t' Ht'].
           inv Ht'; auto.
         - destruct Ht' as [t' Ht'].
           inv Ht'; auto. }
    constructor.
    apply CH; auto.
    intros t1 t2 Ht1 Ht2.
    specialize (Ht (e :: t1) (e :: t2)).
    eapply traceinf_prefix_cons in Ht1.
    eapply traceinf_prefix_cons in Ht2.
    destruct (Ht Ht1 Ht2) as [Ht' | Ht'].
    - destruct Ht' as [T' Ht'].
      simpl in Ht'.
      inv Ht'.
      left; exists T'; reflexivity.
    - destruct Ht' as [T' Ht'].
      simpl in Ht'.
      inv Ht'.
      right; exists T'; reflexivity.
  Qed.

  Lemma star_prefix s s' fs fs' t1 t2 :
    match_states s fs ->
    Star (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s t1 s' ->
    Star (faulty_semantics prog) fs t2 fs' ->
    trace_prefix t1 t2 \/ trace_prefix t2 t1.
  Proof.
    intros Hmatch Hstar.
    revert Hmatch.
    revert fs fs' t2.
    induction Hstar; intros fs fs' t2' Hmatch Hstar'.
    { left; eexists; reflexivity. }
    subst.
    inv Hstar'.
    { right; eexists; reflexivity. }
    eapply faulty_step_simulation in H; eauto.
    destruct H as [? Hmatch']; subst.
    cut (trace_prefix t2 t3 \/ trace_prefix t3 t2).
    { intros [[t' H] | [t' H]]; subst.
      - left; eexists; rewrite Eapp_assoc; reflexivity.
      - right; eexists; rewrite Eapp_assoc; reflexivity. }
    eapply IHHstar; eauto.
  Qed.

  Lemma trace_cub_comparable t1 t1' t2 :
    trace_prefix t1 t2 ->
    trace_prefix t1' t2 ->
    trace_prefix t1 t1' \/ trace_prefix t1' t1.
  Proof.
    unfold trace_prefix.
    intros [t ?]; subst.
    intros [t' ?]; subst.
    revert H.
    revert t1' t t'.
    induction t1; simpl; intros t1' t t' Heq.
    { subst; left; exists t1'; reflexivity. }
    destruct t1'; simpl in *.
    { subst; right; exists (a :: t1); reflexivity. }
    inv Heq.
    apply IHt1 in H1.
    destruct H1 as [[t'' ?] | [t'' ?]]; subst.
    - left; eexists; reflexivity.
    - right; eexists; reflexivity.
  Qed.

  Lemma trace_prefix_trans t1 t2 t3 :
    trace_prefix t1 t2 ->
    trace_prefix t2 t3 ->
    trace_prefix t1 t3.
  Proof.
    intros [t ?] [t' ?]; subst.
    eexists; rewrite Eapp_assoc; reflexivity.
  Qed.

  Lemma reactive_reactive s fs T1 T2 :
    match_states s fs ->
    Forever_reactive (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s T1 ->
    Forever_reactive (faulty_semantics prog) fs T2 ->
    traceinf_sim T1 T2.
  Proof.
    intros Hmatch Hreact Hreact'.
    apply prefixes_comparable_traceinf_sim.
    intros t1 t2 Ht1 Ht2.
    eapply reactive_prefix_exists_star in Hreact; eauto.
    eapply reactive_prefix_exists_star in Hreact'; eauto.
    destruct Hreact as (s' & t1' & Hstar & Ht1').
    destruct Hreact' as (fs' & t2' & Hstar' & Ht2').
    pose proof Hstar as H.
    eapply star_prefix in H; eauto.
    destruct H as [H | H].
    - eapply trace_cub_comparable.
      2: { eauto. }
      eapply trace_prefix_trans; eauto.
    - eapply trace_cub_comparable; eauto.
      eapply trace_prefix_trans; eauto.
  Qed.

  Lemma star_final_state_trace_prefix s s' fs fs' t1 t2 r :
    match_states s fs ->
    Star (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s t1 s' ->
    Star (faulty_semantics prog) fs t2 fs' ->
    final_state (faulty_semantics prog) fs' r ->
    trace_prefix t1 t2.
  Proof.
    intros Hmatch Hstar.
    revert Hmatch.
    revert fs fs' t2 r.
    induction Hstar; intros fs fs' t2' r Hmatch Hstar' Hfin.
    { eexists; reflexivity. }
    subst.
    inv Hstar'.
    { eapply faulty_step_exists in H; eauto.
      destruct H as (t' & fs'' & Hfstep).
      exfalso; eapply faulty_final_state_nostep; eauto. }
    eapply faulty_step_simulation in H; eauto.
    destruct H as [? Hmatch']; subst.
    apply trace_prefix_app.
    eapply IHHstar; eauto.
  Qed.

  Lemma star_silent_trace_prefix s s' fs fs' t1 t2 :
    match_states s fs ->
    Star (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s t1 s' ->
    Star (faulty_semantics prog) fs t2 fs' ->
    Forever_silent (faulty_semantics prog) fs' ->
    trace_prefix t1 t2.
  Proof.
    intros Hmatch Hstar.
    revert Hmatch.
    revert fs fs' t2.
    induction Hstar; intros fs fs' t2' Hmatch Hstar' Hsil.
    { eexists; reflexivity. }
    subst.
    inv Hstar'.
    { inv Hsil.
      eapply faulty_step_simulation in H; eauto.
      destruct H as [? Hmatch']; subst; simpl.
      eapply IHHstar; eauto.
      apply star_refl. }
    eapply faulty_step_simulation in H; eauto.
    destruct H as [? Hmatch']; subst.
    apply trace_prefix_app.
    eapply IHHstar; eauto.
  Qed.

  Lemma star_nostep_trace_prefix s s' fs fs' t1 t2 :
    match_states s fs ->
    Star (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s t1 s' ->
    Star (faulty_semantics prog) fs t2 fs' ->
    Nostep (faulty_semantics prog) fs' ->
    trace_prefix t1 t2.
  Proof.
    intros Hmatch Hstar.
    revert Hmatch.
    revert fs fs' t2.
    induction Hstar; intros fs fs' t2' Hmatch Hstar' Hnostep.
    { eexists; reflexivity. }
    subst.
    inv Hstar'.
    { eapply faulty_step_exists in H; eauto.
      destruct H as (t' & fs'' & Hfstep).
      exfalso; eapply Hnostep; eauto. }
    eapply faulty_step_simulation in H; eauto.
    destruct H as [? Hmatch']; subst.
    apply trace_prefix_app.
    eapply IHHstar; eauto.
  Qed.

  Lemma star_reactive_trace_prefix s s' fs t T :
    match_states s fs ->
    Star (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s t s' ->
    Forever_reactive (faulty_semantics prog) fs T ->
    traceinf_prefix t T.
  Proof.
    intros Hmatch Hstar.
    revert Hmatch.
    revert fs T.
    induction Hstar; intros fs T Hmatch Hreact.
    { eexists; reflexivity. }
    subst.
    inv Hreact.
    inv H0; try congruence.
    eapply faulty_step_simulation in H; eauto.
    destruct H as [? Hmatch']; subst.
    rewrite Eappinf_assoc.
    apply traceinf_prefix_app.
    eapply IHHstar; eauto.
    eapply star_forever_reactive; eauto.
  Qed.

  Lemma rtl_state_behaves_faulty_improves (s : RTL.state) (fs : fstate) beh1 beh2 :
    RTL.initial_state prog s ->
    initial_state (faulty_semantics prog) fs ->
    state_behaves (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s beh1 ->
    state_behaves (faulty_semantics prog) fs beh2 ->
    behavior_improves beh1 beh2.
  Proof.
    intros Hinit1 Hinit2 Hbeh1 Hbeh2.
    generalize (initial_states_match _ _ Hinit1 Hinit2); intro Hmatch.
    inv Hbeh1.
    - left; inv Hbeh2.
      + f_equal; eapply star_final_star_final; eauto.
      + exfalso; eapply terminates_diverges_False; eauto.
      + exfalso; eapply star_final_not_reactive; eauto.
      + exfalso; eapply H3, star_final_star_nostep_final; eauto.
    - left; inv Hbeh2.
      + exfalso; eapply diverges_terminates_False; eauto.
      + f_equal; eapply star_silent_star_silent; eauto.
      + exfalso; eapply star_silent_not_reactive; eauto.
      + exfalso; eapply star_silent_star_not_stuck; eauto.
    - left; inv Hbeh2.
      + exfalso; eapply reacts_terminates_False; eauto.
      + exfalso; eapply reacts_diverges_False; eauto.
      + f_equal; eapply reactive_reactive in H; eauto.
        apply traceinf_sim_ext; assumption.
      + exfalso; eapply reactive_star_not_stuck; eauto.
    - right.
      exists t; split; auto.
      pose proof H as Hstar.
      eapply faulty_star_step_exists in Hstar; eauto.
      destruct Hstar as (fs' & Hstar' & Hmatch').
      destruct beh2.
      + assert (Hpre: trace_prefix t t0).
        { clear Hmatch'; inv Hbeh2.
          eapply star_final_state_trace_prefix; eauto. }
        destruct Hpre as [t' ?]; subst.
        exists (Terminates t' i); reflexivity.
      + assert (Hpre: trace_prefix t t0).
        { clear Hmatch'; inv Hbeh2.
          eapply star_silent_trace_prefix; eauto. }
        destruct Hpre as [t' ?]; subst.
        exists (Diverges t'); reflexivity.
      + assert (Hpre: traceinf_prefix t t0).
        { clear Hmatch'; inv Hbeh2.
          eapply star_reactive_trace_prefix; eauto. }
        destruct Hpre as [t' ?]; subst.
        exists (Reacts t'); reflexivity.
      + assert (Hpre: trace_prefix t t0).
        { clear Hmatch'; inv Hbeh2.
          eapply star_nostep_trace_prefix; eauto. }
        destruct Hpre as [t' ?]; subst.
        exists (Goes_wrong t'); reflexivity.
  Qed.

  Theorem faulty_behavior_improves beh1 beh2 :
    program_behaves (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) beh1 ->
    program_behaves (faulty_semantics prog) beh2 ->
    behavior_improves beh1 beh2.
  Proof.
    intros Hbeh1 Hbeh2.
    inv Hbeh1.
    - inv Hbeh2.
      2: { exfalso.
           inv H.
           simpl in *.
           (* pose proof PROG as Hmatch. *)
           (* eapply Genv.find_funct_ptr_match in Hmatch; eauto. *)
           (* destruct Hmatch as (cunt & tf & Htf & Hmatch & Hlink). *)
           apply (H1 {| fs_state := Callstate [] f [] m0; fault := false |}).
           constructor; econstructor; eauto. }
           (* - eapply Genv.init_mem_match in PROG; eauto. *)
           (* - replace (prog_main prog2) with (prog_main prog1) in * by *)
           (*       (eapply match_program_main in PROG; auto). *)
           (*   eapply Genv.find_symbol_match in PROG. *)
           (*   rewrite PROG; eauto. *)
           (* - inv Hmatch; auto. *)
           (*   inv FUN; simpl in *; auto. } *)
      eapply rtl_state_behaves_faulty_improves; eauto.
    - inv Hbeh2.
      { exfalso.
        inv H0.
        inv H2.
        simpl in *.
        (* pose proof PROG as Hmatch. *)
        (* rename f into tf. *)
        (* eapply Genv.find_funct_ptr_match' in Hmatch; eauto. *)
        (* destruct Hmatch as (cunt & f & Hf & Hmatch & Hlink). *)
        apply (H (Callstate [] f [] m0)).
        econstructor; eauto. }
        (* - eapply Genv.init_mem_match' in PROG; eauto. *)
        (* - replace (prog_main prog1) with (prog_main prog2) in * by *)
        (*       (eapply match_program_main in PROG; auto). *)
        (*   eapply Genv.find_symbol_match in PROG. *)
        (*   rewrite <- PROG; eauto. *)
        (* - inv Hmatch; auto. *)
        (*   inv FUN; simpl in *; auto. } *)
      constructor; reflexivity.
  Qed.

  (* Alternate formulation that might avoid the need for traceinf_sim
     extensionality. EDIT: actually no, it just pushes the need for
     extensionality to the higher-level theorem in
     driver/Complements.v. *)
  (* Theorem faulty_behavior_improves' beh2 : *)
  (*   program_behaves (faulty_semantics prog) beh2 -> *)
  (*   exists beh1, program_behaves (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) beh1 /\ behavior_improves beh1 beh2. *)
  (* Admitted. *)

End TOLERANCE.
