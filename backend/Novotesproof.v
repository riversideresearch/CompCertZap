Require Import
  AST
  Behaviors
  Builtins
  Builtins2
  Coqlib
  Errors
  Events
  Linking
  Maps
  Novotes
  Op
  RTL
  RTLagreement
  Smallstep
.
Import ListNotations.

Definition not_vote (instr : instruction) : Prop :=
  match instr with
  | Ibuiltin ef args res succ =>
      ~ is_vote_builtin ef /\ ~ is_vote_runtime ef
  | _ => True
  end.

Definition no_votes_code (c : code) : Prop :=
  forall pc instr, c ! pc = Some instr -> not_vote instr.

Inductive no_votes_fundef : fundef -> Prop :=
| no_votes_Internal : forall f,
    no_votes_code f.(fn_code) ->
    no_votes_fundef (Internal f)
| no_votes_external : forall ef,
    ~ is_vote_builtin ef ->
    ~ is_vote_runtime ef ->
    no_votes_fundef (External ef).

Inductive no_votes_globdef : globdef fundef unit -> Prop :=
| no_votes_Gfun : forall fd,
    no_votes_fundef fd ->
    no_votes_globdef (Gfun fd)
| no_votes_Gvar : forall v,
    no_votes_globdef (Gvar v).

Inductive no_votes : RTL.program -> Prop :=
| no_votes_program : forall defs public main,
    Forall (fun id_def => no_votes_globdef (snd id_def)) defs ->
    no_votes {| prog_defs := defs
              ; prog_public := public
              ; prog_main := main |}.

(* Note: The 8 cases below follow a near-identical pattern. Deduplication via
   Ltac was attempted in Phase 4 but abandoned due to infinite memory consumption
   during proof checking. The repetition is intentional for build reliability. *)
Lemma no_votes_external_call (p : RTL.program) ef vargs t vres m m' :
  ~ is_vote_builtin ef ->
  ~ is_vote_runtime ef ->
  external_call ef (Globalenvs.Genv.to_senv (Globalenvs.Genv.globalenv p))
    vargs m t vres m' ->
  @external_call _ VoteSemantics_Three
    ef (Globalenvs.Genv.to_senv (Globalenvs.Genv.globalenv p))
    vargs m t vres m'.
Proof.
  intros Hef Hef'.
  destruct ef; simpl; auto.
  - unfold builtin_or_external_sem; intro Hsem.
    destruct (Builtins.lookup_builtin_function name sg) eqn:Hlookup; auto.
    inv Hsem.
    constructor.
    destruct b; auto.
    destruct b; simpl in *;
      repeat (destruct vargs; try congruence).
    + unfold Builtins.lookup_builtin_function in Hlookup.
      destruct (Builtins0.lookup_builtin _ _ _ _).
      { inv Hlookup. }
      destruct (Builtins0.lookup_builtin _ _ _ _).
      { inv Hlookup. }
      simpl in *.
      do 8 (destruct (string_dec name _ && signature_eq sg _);
            simpl in *; try solve [inv Hlookup]).
      destruct (string_dec name _ && signature_eq sg _) eqn:Heq;
        simpl in *; try solve [inv Hlookup].
      { apply andb_prop in Heq; destruct Heq as [H0 H1].
        exfalso; apply Hef.
        destruct (string_dec _ _); simpl in *; subst; try discriminate.
        destruct (signature_eq _ _); simpl in *; subst; try discriminate.
        constructor. }
      clear Heq.
      repeat (destruct (string_dec name _ && signature_eq sg _);
              simpl in *; try solve [inv Hlookup]).
    + unfold Builtins.lookup_builtin_function in Hlookup.
      destruct (Builtins0.lookup_builtin _ _ _ _).
      { inv Hlookup. }
      destruct (Builtins0.lookup_builtin _ _ _ _).
      { inv Hlookup. }
      simpl in *.
      do 9 (destruct (string_dec name _ && signature_eq sg _);
            simpl in *; try solve [inv Hlookup]).
      destruct (string_dec name _ && signature_eq sg _) eqn:Heq;
        simpl in *; try solve [inv Hlookup].
      { apply andb_prop in Heq; destruct Heq as [H0 H1].
        exfalso; apply Hef.
        destruct (string_dec _ _); simpl in *; subst; try discriminate.
        destruct (signature_eq _ _); simpl in *; subst; try discriminate.
        constructor. }
      clear Heq.
      repeat (destruct (string_dec name _ && signature_eq sg _);
              simpl in *; try solve [inv Hlookup]).
    + unfold Builtins.lookup_builtin_function in Hlookup.
      destruct (Builtins0.lookup_builtin _ _ _ _).
      { inv Hlookup. }
      destruct (Builtins0.lookup_builtin _ _ _ _).
      { inv Hlookup. }
      simpl in *.
      do 10 (destruct (string_dec name _ && signature_eq sg _);
            simpl in *; try solve [inv Hlookup]).
      destruct (string_dec name _ && signature_eq sg _) eqn:Heq;
        simpl in *; try solve [inv Hlookup].
      { apply andb_prop in Heq; destruct Heq as [H0 H1].
        exfalso; apply Hef.
        destruct (string_dec _ _); simpl in *; subst; try discriminate.
        destruct (signature_eq _ _); simpl in *; subst; try discriminate.
        constructor. }
      clear Heq.
      repeat (destruct (string_dec name _ && signature_eq sg _);
              simpl in *; try solve [inv Hlookup]).
    + unfold Builtins.lookup_builtin_function in Hlookup.
      destruct (Builtins0.lookup_builtin _ _ _ _).
      { inv Hlookup. }
      destruct (Builtins0.lookup_builtin _ _ _ _).
      { inv Hlookup. }
      simpl in *.
      do 11 (destruct (string_dec name _ && signature_eq sg _);
            simpl in *; try solve [inv Hlookup]).
      destruct (string_dec name _ && signature_eq sg _) eqn:Heq;
        simpl in *; try solve [inv Hlookup].
      { apply andb_prop in Heq; destruct Heq as [H0 H1].
        exfalso; apply Hef.
        destruct (string_dec _ _); simpl in *; subst; try discriminate.
        destruct (signature_eq _ _); simpl in *; subst; try discriminate.
        constructor. }
      clear Heq.
      repeat (destruct (string_dec name _ && signature_eq sg _);
              simpl in *; try solve [inv Hlookup]).
  - unfold builtin_or_external_sem; intro Hsem.
    destruct (Builtins.lookup_builtin_function name sg) eqn:Hlookup; auto.
    inv Hsem.
    constructor.
    destruct b; auto.
    destruct b; simpl in *;
      repeat (destruct vargs; try congruence).
    + unfold Builtins.lookup_builtin_function in Hlookup.
      destruct (Builtins0.lookup_builtin _ _ _ _).
      { inv Hlookup. }
      destruct (Builtins0.lookup_builtin _ _ _ _).
      { inv Hlookup. }
      simpl in *.
      do 8 (destruct (string_dec name _ && signature_eq sg _);
            simpl in *; try solve [inv Hlookup]).
      destruct (string_dec name _ && signature_eq sg _) eqn:Heq;
        simpl in *; try solve [inv Hlookup].
      { apply andb_prop in Heq; destruct Heq as [H0 H1].
        exfalso; apply Hef'.
        destruct (string_dec _ _); simpl in *; subst; try discriminate.
        destruct (signature_eq _ _); simpl in *; subst; try discriminate.
        constructor. }
      clear Heq.
      repeat (destruct (string_dec name _ && signature_eq sg _);
              simpl in *; try solve [inv Hlookup]).
    + unfold Builtins.lookup_builtin_function in Hlookup.
      destruct (Builtins0.lookup_builtin _ _ _ _).
      { inv Hlookup. }
      destruct (Builtins0.lookup_builtin _ _ _ _).
      { inv Hlookup. }
      simpl in *.
      do 9 (destruct (string_dec name _ && signature_eq sg _);
            simpl in *; try solve [inv Hlookup]).
      destruct (string_dec name _ && signature_eq sg _) eqn:Heq;
        simpl in *; try solve [inv Hlookup].
      { apply andb_prop in Heq; destruct Heq as [H0 H1].
        exfalso; apply Hef'.
        destruct (string_dec _ _); simpl in *; subst; try discriminate.
        destruct (signature_eq _ _); simpl in *; subst; try discriminate.
        constructor. }
      clear Heq.
      repeat (destruct (string_dec name _ && signature_eq sg _);
              simpl in *; try solve [inv Hlookup]).
    + unfold Builtins.lookup_builtin_function in Hlookup.
      destruct (Builtins0.lookup_builtin _ _ _ _).
      { inv Hlookup. }
      destruct (Builtins0.lookup_builtin _ _ _ _).
      { inv Hlookup. }
      simpl in *.
      do 10 (destruct (string_dec name _ && signature_eq sg _);
            simpl in *; try solve [inv Hlookup]).
      destruct (string_dec name _ && signature_eq sg _) eqn:Heq;
        simpl in *; try solve [inv Hlookup].
      { apply andb_prop in Heq; destruct Heq as [H0 H1].
        exfalso; apply Hef'.
        destruct (string_dec _ _); simpl in *; subst; try discriminate.
        destruct (signature_eq _ _); simpl in *; subst; try discriminate.
        constructor. }
      clear Heq.
      repeat (destruct (string_dec name _ && signature_eq sg _);
              simpl in *; try solve [inv Hlookup]).
    + unfold Builtins.lookup_builtin_function in Hlookup.
      destruct (Builtins0.lookup_builtin _ _ _ _).
      { inv Hlookup. }
      destruct (Builtins0.lookup_builtin _ _ _ _).
      { inv Hlookup. }
      simpl in *.
      do 11 (destruct (string_dec name _ && signature_eq sg _);
            simpl in *; try solve [inv Hlookup]).
      destruct (string_dec name _ && signature_eq sg _) eqn:Heq;
        simpl in *; try solve [inv Hlookup].
      { apply andb_prop in Heq; destruct Heq as [H0 H1].
        exfalso; apply Hef'.
        destruct (string_dec _ _); simpl in *; subst; try discriminate.
        destruct (signature_eq _ _); simpl in *; subst; try discriminate.
        constructor. }
      clear Heq.
      repeat (destruct (string_dec name _ && signature_eq sg _);
              simpl in *; try solve [inv Hlookup]).
Qed.


Section IMPLIES_AGREEMENT.

Variable p : program.

Hypothesis (Hnovote : no_votes p).
  
(* Lemma no_votes_weak_agreement : *)
(*   no_votes p -> *)
(*   rtl_weak_agreement p. *)

Inductive stackframe_invariant : stackframe -> Prop :=
| stackframe_invariant_Stackframe : forall res f sp pc rs,
    (exists i, In (i, Gfun (Internal f)) (prog_defs p)) ->
    stackframe_invariant (Stackframe res f sp pc rs).

Inductive state_invariant : state (rtl_sem2 p) -> Prop :=
| state_invariant_State : forall stk f sp pc rs m,
    Forall stackframe_invariant stk ->
    (exists i, In (i, Gfun (Internal f)) (prog_defs p)) ->
    state_invariant (State stk f sp pc rs m)
| state_invariant_Callstate : forall stk fd args m,
    Forall stackframe_invariant stk ->
    (exists i, In (i, Gfun fd) (prog_defs p)) ->
    state_invariant (Callstate stk fd args m)
| state_invariant_Returnstate : forall stk v m,
    Forall stackframe_invariant stk ->
    state_invariant (Returnstate stk v m).

Definition match_states (s1 : state (rtl_sem2 p)) (s2 : state (rtl_sem3 p)) : Prop :=
  s1 = s2 /\ state_invariant s1.

Lemma no_votes_step_simulation :
  forall (s1 : RTL.state) (t : Events.trace) (s1' : RTL.state),
  RTL.step (Globalenvs.Genv.globalenv p) s1 t s1' ->
  forall s2 : RTL.state,
  match_states s1 s2 ->
  exists s2' : RTL.state, @RTL.step _ VoteSemantics_Three
                       (Globalenvs.Genv.globalenv p) s2 t s2' /\ match_states s1' s2'.
Proof.
  intros s1 t s1' Hstep s2 Hmatch.
  inv Hmatch.
  exists s1'; split; try reflexivity.
  inv Hstep; try solve [econstructor; eauto].
  - inv H0.
    destruct H10 as [i Hin].
    inv Hnovote.
    rewrite Forall_forall in H0.
    destruct p.
    inv H3.
    apply H0 in Hin.
    inv Hin.
    inv H4.
    specialize (H6 _ _ H).
    simpl in H6.
    eapply exec_Ibuiltin; eauto.
    destruct H6.
    eapply no_votes_external_call; auto.
  - eapply exec_function_external.
    assert (~ is_vote_builtin ef /\ ~ is_vote_runtime ef).
    { inv H0.
      destruct H6 as [i Hin].
      inv Hnovote.
      rewrite Forall_forall in H0.
      destruct p; inv H1.
      simpl in *.
      apply H0 in Hin; inv Hin.
      inv H2; split; assumption. }
    destruct H1.
    eapply no_votes_external_call; try assumption.
  - split; auto.
    inv Hstep; inv H0; try solve [constructor; auto].
    + constructor.
      * constructor; auto.
        constructor; assumption.
      * unfold find_function in H1.
        destruct ros.
        { eapply Globalenvs.Genv.find_funct_inversion; eassumption. }
        destruct (Globalenvs.Genv.find_symbol _ _); try congruence.
        eapply Globalenvs.Genv.find_funct_ptr_inversion; eassumption.
    + constructor; auto.
      unfold find_function in H1.
        destruct ros.
        { eapply Globalenvs.Genv.find_funct_inversion; eassumption. }
        destruct (Globalenvs.Genv.find_symbol _ _); try congruence.
        eapply Globalenvs.Genv.find_funct_ptr_inversion; eassumption.
    + inv H1; inv H2.
      constructor; assumption.
  Qed.

Lemma initial_state_invariant s :
  RTL.initial_state p s ->
  state_invariant s.
Proof.
  intro Hinit; inv Hinit.
  constructor; auto.
  eapply Globalenvs.Genv.find_funct_ptr_inversion; eassumption.
Qed.

Lemma no_votes_forward_simulation :
  forward_simulation (rtl_sem2 p) (rtl_sem3 p).
Proof.
  apply forward_simulation_step with (match_states := match_states);
    simpl in *; auto.
  - intros s1 Hinit.
    eexists; split; eauto.
    split; auto.
    apply initial_state_invariant; assumption.
  - intros s1 s2 r Hmatch Hfin.
    inv Hmatch; assumption.
  - eapply no_votes_step_simulation.
Qed.

Lemma no_votes_weak_agreement' :
  rtl_weak_agreement' p.
Proof.
  unfold rtl_weak_agreement'.
  intros beh Hbeh.
  eapply backward_simulation_behavior_improves; eauto.
  apply forward_to_backward_simulation.
  - apply no_votes_forward_simulation.
  - apply RTL.semantics_receptive.
  - apply RTL.semantics_determinate.
Qed.

End IMPLIES_AGREEMENT.

Lemma check_program_sound p :
  check_program p = true ->
  no_votes p.
Proof.
  unfold check_program.
  intro Hforall.
  rewrite forallb_forall in Hforall.
  destruct p.
  simpl in *.
  constructor.
  apply Forall_forall.
  intros id_gd Hin.
  apply Hforall in Hin; clear Hforall.
  destruct id_gd as [id []]; simpl in *; constructor.
  destruct f; constructor.
  - intros pc i Hpci.
    unfold check_function in Hin.
    eapply PTree_Properties.for_all_correct in Hin; eauto.
    unfold check_instr in Hin.
    destruct i; try constructor.
    + apply andb_prop in Hin; destruct Hin as [H0 H1].
      destruct (is_vote_builtinb_spec e); auto; simpl in *; discriminate.
    + apply andb_prop in Hin; destruct Hin as [H0 H1].
      destruct (is_vote_runtimeb_spec e); auto; simpl in *; discriminate.
  - apply andb_prop in Hin; destruct Hin as [H0 H1].
    destruct (is_vote_builtinb_spec e); auto; simpl in *; discriminate.
  - apply andb_prop in Hin; destruct Hin as [H0 H1].
    destruct (is_vote_runtimeb_spec e); auto; simpl in *; discriminate.
Qed.
