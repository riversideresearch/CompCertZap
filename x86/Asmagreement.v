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

(* Section CSTRATEGY_WEAK_AGREEMENT. *)
(*   Variable p : Csyntax.program. *)

(*   Definition cstrategy_sem2 := atomic (@Cstrategy.semantics Two (VoteSemantics_Two) p). *)
(*   Definition cstrategy_sem3 := atomic (@Cstrategy.semantics Three (VoteSemantics_Three) p). *)

(*   Definition cstrategy_weak_agreement := *)
(*     forall beh, *)
(*       program_behaves cstrategy_sem2 beh -> *)
(*       program_behaves cstrategy_sem3 beh. *)
(* End CSTRATEGY_WEAK_AGREEMENT. *)

Section ASM_WEAK_AGREEMENT.
  Variable p : Asm.program.

  Definition asm_sem2 := @Asm.semantics Two (VoteSemantics_Two) p.
  Definition asm_sem3 := @Asm.semantics Three (VoteSemantics_Three) p.

  Definition asm_weak_agreement :=
    forall beh,
      program_behaves asm_sem2 beh ->
      program_behaves asm_sem3 beh.
End ASM_WEAK_AGREEMENT.

(* Section AGREEMENT_PRESERVATION. *)
(*   Variable p : Csyntax.program. *)
(*   Variable tp : Asm.program. *)

(*   Lemma initial_state_sem3_sem2 s : *)
(*     initial_state (asm_sem3 tp) s -> *)
(*     initial_state (asm_sem2 tp) s. *)
(*   Proof. intro Hinit; inv Hinit; econstructor; eauto. Qed. *)

(*   Theorem forward_simulation_preserves_weak_agreement : *)
(*     (forall beh, program_behaves (cstrategy_sem2 p) beh -> not_wrong beh) -> *)
(*     forward_simulation (cstrategy_sem2 p) (asm_sem2 tp) -> *)
(*     forward_simulation (cstrategy_sem3 p) (asm_sem3 tp) -> *)
(*     cstrategy_weak_agreement p -> *)
(*     asm_weak_agreement tp. *)
(*   Proof. *)
(*     unfold cstrategy_weak_agreement, asm_weak_agreement. *)
(*     intros Hsafe Hforward2 Hforward3 Hagree beh Hbeh. *)

(*     assert (Hbackward: backward_simulation (cstrategy_sem3 p) (asm_sem3 tp)). *)
(*     { apply forward_to_backward_simulation; auto. *)
(*       - apply atomic_receptive. *)
(*         apply Cstrategy.semantics_strongly_receptive. *)
(*       - apply Asm.semantics_determinate. } *)

(*     assert (Hbackward2: backward_simulation (cstrategy_sem2 p) (asm_sem2 tp)). *)
(*     { apply forward_to_backward_simulation; auto. *)
(*       - apply atomic_receptive. *)
(*         apply Cstrategy.semantics_strongly_receptive. *)
(*       - apply Asm.semantics_determinate. } *)

(*     pose proof Hbeh as Hbeh'. *)
(*     inv Hbeh'. *)
(*     2: { constructor. *)
(*          intros s Hs. *)
(*          eapply H with s. *)
(*          eapply initial_state_sem3_sem2; auto. } *)

(*     eapply backward_simulation_same_safe_behavior in Hbeh. *)
(*     2: { eauto. } *)
(*     - eapply forward_simulation_same_safe_behavior; eauto. *)
(*     - intros beh' Hbeh'; eauto. *)
(*   Qed. *)
  
(* End AGREEMENT_PRESERVATION. *)

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
  
End AGREEMENT_PRESERVATION.
