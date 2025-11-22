Require Import
  AST
  Behaviors
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
  | Ibuiltin ef args res succ => not (is_vote_builtin ef)
  | _ => True
  end.

Definition no_votes_code (c : code) : Prop :=
  forall pc instr, c ! pc = Some instr -> not_vote instr.

Inductive no_votes_fundef : fundef -> Prop :=
| no_votes_Internal : forall f,
    no_votes_code f.(fn_code) ->
    no_votes_fundef (Internal f)
| no_votes_external : forall ef,
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

Section IMPLIES_AGREEMENT.

Variable p : program.
Hypothesis (Hnovote : no_votes p).
  
(* Lemma no_votes_weak_agreement : *)
(*   no_votes p -> *)
(*   rtl_weak_agreement p. *)
(* Admitted. *)

(* TODO: in State case (maybe Callstate too?) include fact that [f]
   came from a globdef in [p]. *)
Definition match_states (s1 : state (rtl_sem2 p)) (s2 : state (rtl_sem3 p)) : Prop :=
  s1 = s2.

(* Lemma no_votes_external_call ef vargs t vres m m' : *)
(*   Events.external_call ef (Globalenvs.Genv.to_senv (Globalenvs.Genv.globalenv p)) *)
(*     vargs m t vres m' -> *)
(*   @Events.external_call _ VoteSemantics_Three *)
(*     ef (Globalenvs.Genv.to_senv (Globalenvs.Genv.globalenv p)) *)
(*     vargs m t vres m'. *)
(* Proof. *)
(*   intro Hcall. *)
(*   destruct ef; simpl; auto. *)
(*   -  *)
(* Admitted. *)

Lemma no_votes_step_simulation :
  forall (s1 : RTL.state) (t : Events.trace) (s1' : RTL.state),
  RTL.step (Globalenvs.Genv.globalenv p) s1 t s1' ->
  forall s2 : RTL.state,
  match_states s1 s2 ->
  exists s2' : RTL.state, @RTL.step _ VoteSemantics_Three
                       (Globalenvs.Genv.globalenv p) s2 t s2' /\ match_states s1' s2'.
Proof.
(*   intros s1 t s1' Hstep s2 Hmatch. *)
(*   inv Hmatch. *)
(*   exists s1'; split; try reflexivity. *)
(*   inv Hstep; try solve [econstructor; eauto]. *)
(*   - eapply exec_Ibuiltin; eauto. *)
(*     eapply no_votes_external_call; assumption. *)
(*   - eapply exec_function_external. *)
(*     eapply no_votes_external_call; assumption. *)
  (* Qed. *)
Admitted.

Lemma no_votes_forward_simulation :
  forward_simulation (rtl_sem2 p) (rtl_sem3 p).
Proof.
  apply forward_simulation_step with (match_states := match_states);
    simpl in *; auto.
  - intros s1 Hinit.
    eexists; split; eauto.
    reflexivity.
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
  intros pc i Hpci.
  unfold check_function in Hin.
  eapply PTree_Properties.for_all_correct in Hin; eauto.
  unfold check_instr in Hin.
  destruct i; try constructor.
  intro HC; inv HC; simpl in *;
    destruct (signature_eq _ _); simpl in *; congruence.
Qed.
