(** This file is currently not used for anything. *)

Require Import
  Asm
  AST
  Behaviors
  Builtins2
  Coqlib
  Cstrategy
  Maps
  Novotes
  Registers
  RTLagreement
  Smallstep
  Values
.

Import ListNotations.

(* Section WEAK_AGREEMENT. *)
(*   Context {F V : Type}. *)
(*   Variable sem : forall VT : vote_type, VoteSemantics VT -> AST.program F V -> semantics. *)
(*   Variable p : AST.program F V. *)

(*   Definition sem2 := sem Two (VoteSemantics_Two) p. *)
(*   Definition sem3 := sem Three (VoteSemantics_Three) p. *)

(*   Definition weak_agreement := *)
(*     forall beh, *)
(*       program_behaves sem2 beh -> *)
(*       program_behaves sem3 beh. *)
(* End WEAK_AGREEMENT. *)

Section ASM_WEAK_AGREEMENT.
  Variable p : Asm.program.

  Definition asm_sem2 := @Asm.semantics Two (VoteSemantics_Two) p.
  Definition asm_sem3 := @Asm.semantics Three (VoteSemantics_Three) p.

  Definition asm_weak_agreement :=
    forall beh,
      program_behaves asm_sem2 beh ->
      program_behaves asm_sem3 beh.

  (* Definition asm_weak_agreement' := *)
  (*   forall beh, *)
  (*     program_behaves asm_sem3 beh -> *)
  (*     program_behaves asm_sem2 beh. *)

  (* Definition asm_weak_agreement := weak_agreement (@Asm.semantics). *)

  (* Definition asm_weak_agreement' := backward_simulation asm_sem2 asm_sem3. *)

  Definition asm_weak_agreement' :=
    forall beh3, program_behaves asm_sem3 beh3 ->
            exists beh2, program_behaves asm_sem2 beh2 /\ behavior_improves beh2 beh3.

End ASM_WEAK_AGREEMENT.

Section AGREEMENT_PRESERVATION.
  Variable p : RTL.program.
  Variable tp : Asm.program.

  Lemma initial_state_sem3_sem2 s :
    initial_state (asm_sem3 tp) s ->
    initial_state (asm_sem2 tp) s.
  Proof. intro Hinit; inv Hinit; econstructor; eauto. Qed.

  Theorem forward_simulation_preserves_weak_agreement :
    (forall beh, program_behaves (rtl_sem2 p) beh -> not_wrong beh) ->
    forward_simulation (rtl_sem2 p) (asm_sem2 tp) ->
    forward_simulation (rtl_sem3 p) (asm_sem3 tp) ->
    rtl_weak_agreement p ->
    asm_weak_agreement tp.
  Proof.
    unfold rtl_weak_agreement, asm_weak_agreement.
    intros Hsafe Hforward2 Hforward3 Hagree beh Hbeh.

    assert (Hbackward: backward_simulation (rtl_sem3 p) (asm_sem3 tp)).
    { apply forward_to_backward_simulation; auto.
      - apply RTL.semantics_receptive.
      - apply Asm.semantics_determinate. }

    assert (Hbackward2: backward_simulation (rtl_sem2 p) (asm_sem2 tp)).
    { apply forward_to_backward_simulation; auto.
      - apply RTL.semantics_receptive.
      - apply Asm.semantics_determinate. }

    pose proof Hbeh as Hbeh'.
    inv Hbeh'.
    2: { constructor.
         intros s Hs.
         eapply H with s.
         eapply initial_state_sem3_sem2; auto. }

    eapply backward_simulation_same_safe_behavior in Hbeh.
    2: { eauto. }
    - eapply forward_simulation_same_safe_behavior; eauto.
    - intros beh' Hbeh'; eauto.
  Qed.
  
  Theorem forward_simulation_preserves_weak_agreement' :
    (forall beh, program_behaves (rtl_sem2 p) beh -> not_wrong beh) ->
    forward_simulation (rtl_sem2 p) (asm_sem2 tp) ->
    forward_simulation (rtl_sem3 p) (asm_sem3 tp) ->
    rtl_weak_agreement' p ->
    asm_weak_agreement' tp.
  Proof.
    unfold rtl_weak_agreement', asm_weak_agreement'.
    intros Hsafe Hforward2 Hforward3 Hagree beh3 Hbeh3.
    assert (Hbackward: backward_simulation (rtl_sem3 p) (asm_sem3 tp)).
    { apply forward_to_backward_simulation; auto.
      - apply RTL.semantics_receptive.
      - apply Asm.semantics_determinate. }
    eapply backward_simulation_behavior_improves in Hbackward; eauto.
    destruct Hbackward as (beh1 & Hbeh1 & Himp).
    eapply Hagree in Hbeh1.
    destruct Hbeh1 as (beh2 & Hbeh2 & Himp').
    exists beh2; split.
    2: { eapply behavior_improves_trans; eauto. }
    eapply forward_simulation_same_safe_behavior; eauto.
  Qed.
  
End AGREEMENT_PRESERVATION.
