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

(** Corollaries of the main semantic preservation theorem. *)

From Coq Require Import Classical.
Require Import Coqlib Errors.
Require Import AST Linking Events Smallstep Behaviors.
Require Import Csyntax Csem Cstrategy Asm.
Require Import Compiler.
Require Import Compopts.
Require Import RTLagreement RTLcolor RTLcolorcheck RTLfault RTLtolerant.
Require Import Asmagreement.
Require Import Builtins2.

Local Open Scope linking_scope.

Definition rtl_to_asm_passes :=
  mkpass (match_if Compopts.dmr RTLdmrproof.match_prog)
  ::: mkpass (match_if Compopts.tmr RTLtmrproof.match_prog)
  ::: mkpass Renumberproof.match_prog
  ::: mkpass Allocproof.match_prog
  ::: mkpass Tunnelingproof.match_prog
  ::: mkpass Linearizeproof.match_prog
  ::: mkpass CleanupLabelsproof.match_prog
  ::: mkpass (match_if Compopts.debug Debugvarproof.match_prog)
  ::: mkpass Stackingproof.match_prog
  ::: mkpass Asmgenproof.match_prog
  ::: pass_nil _.

Definition match_prog_rtl_asm: RTL.program -> Asm.program -> Prop :=
  pass_match (compose_passes rtl_to_asm_passes).

Lemma transf_rtl_to_asm_match_prog p tp :
  transf_rtl_program' p = OK tp ->
  match_prog_rtl_asm p tp.
Proof.
  intro T.
  unfold transf_rtl_program', time in T. rewrite ! compose_print_identity in T. simpl in T.
  destruct (partial_if dmr RTLdmr.transf_program p) as [pdmr|e] eqn:Pdmr; simpl in T; try discriminate.
  destruct (partial_if tmr RTLtmr.transf_program pdmr) as [p15'|e] eqn:P15; simpl in T; try discriminate.
  set (p15 := Renumber.transf_program p15') in *.
    unfold transf_rtl_program'', time in T. rewrite ! compose_print_identity in T. simpl in T.
  destruct (Allocation.transf_program p15) as [p16|e] eqn:P16; simpl in T; try discriminate.
  set (p17 := Tunneling.tunnel_program p16) in *.
  destruct (Linearize.transf_program p17) as [p18|e] eqn:P18; simpl in T; try discriminate.
  set (p19 := CleanupLabels.transf_program p18) in *.
  destruct (partial_if debug Debugvar.transf_program p19) as [p20|e] eqn:P20; simpl in T; try discriminate.
  destruct (Stacking.transf_program p20) as [p21|e] eqn:P21; simpl in T; try discriminate.
  unfold match_prog; simpl.
  exists pdmr; split. eapply partial_if_match; eauto. apply RTLdmrproof.transf_program_match; auto.
  exists p15'; split. eapply partial_if_match; eauto. apply RTLtmrproof.transf_program_match; auto.
  exists p15; split. apply Renumberproof.transf_program_match; auto.
  exists p16; split. apply Allocproof.transf_program_match; auto.
  exists p17; split. apply Tunnelingproof.transf_program_match.
  exists p18; split. apply Linearizeproof.transf_program_match; auto.
  exists p19; split. apply CleanupLabelsproof.transf_program_match; auto.
  exists p20; split. eapply partial_if_match; eauto. apply Debugvarproof.transf_program_match.
  exists p21; split. apply Stackingproof.transf_program_match; auto.
  exists tp; split. apply Asmgenproof.transf_program_match; auto.
  reflexivity.
Qed.


Definition c_to_rtl_passes :=
      mkpass SimplExprproof.match_prog
  ::: mkpass SimplLocalsproof.match_prog
  ::: mkpass Cshmgenproof.match_prog
  ::: mkpass Cminorgenproof.match_prog
  ::: mkpass Selectionproof.match_prog
  ::: mkpass RTLgenproof.match_prog
  ::: mkpass (match_if Compopts.optim_tailcalls Tailcallproof.match_prog)
  ::: mkpass Inliningproof.match_prog
  ::: mkpass Renumberproof.match_prog
  ::: mkpass (match_if Compopts.optim_constprop Constpropproof.match_prog)
  ::: mkpass (match_if Compopts.optim_constprop Renumberproof.match_prog)
  ::: mkpass (match_if Compopts.optim_CSE CSEproof.match_prog)
  ::: mkpass (match_if Compopts.optim_redundancy Deadcodeproof.match_prog)
  ::: mkpass Unusedglobproof.match_prog
  ::: pass_nil _.

Definition match_prog_c_rtl: Csyntax.program -> RTL.program -> Prop :=
  pass_match (compose_passes c_to_rtl_passes).

(** * Preservation of whole-program behaviors *)

(** From the simulation diagrams proved in file [Compiler]. it follows that
  whole-program observable behaviors are preserved in the following sense.
  First, every behavior of the generated assembly code is matched by
  a behavior of the source C code.  The behavior [beh] of the assembly
  code is either identical to the behavior [beh'] of the source C code
  or ``improves upon'' [beh']  by replacing a ``going wrong'' behavior
  with a more defined behavior. *)

Theorem transf_c_program_preservation:
  forall p tp beh,
  transf_c_program p = OK tp ->
  program_behaves (Asm.semantics tp) beh ->
  exists beh', program_behaves (Csem.semantics p) beh' /\ behavior_improves beh' beh.
Proof.
  intros. eapply backward_simulation_behavior_improves; eauto.
  apply transf_c_program_correct; auto.
Qed.

Theorem transf_c_program_to_rtl_preservation:
  forall p tp beh,
  transf_c_program_to_rtl p = OK tp ->
  program_behaves (RTL.semantics tp) beh ->
  exists beh', program_behaves (Csem.semantics p) beh' /\ behavior_improves beh' beh.
Proof.
  intros. eapply backward_simulation_behavior_improves; eauto.
  eapply transf_c_program_to_rtl_correct; eauto.
Qed.

Lemma apply_partial_factor {A B : Type} (f : res A) (g : A -> res B) x :
  f @@@ (fun y => g y) = OK x -> exists z, f = OK z /\ g z = OK x.
Proof.
  unfold apply_partial.
  intro H.
  destruct f; simpl.
  - exists a; split; auto.
  - inv H.
Qed.

Definition transf_c_program_to_rtl' (p: Csyntax.program)
  : res RTL.program :=
  OK p
  @@@ time "Clight generation" SimplExpr.transl_program
  @@@ transf_clight_program_to_rtl.

Lemma transf_c_to_rtl_match_prog p tp :
  OK p @@@ SimplExpr.transl_program @@@ transf_clight_program = OK tp ->
  match_prog_c_rtl p tp.
Proof.
  intro T.
  unfold transf_c_program, time in T. simpl in T.
  destruct (SimplExpr.transl_program p) as [p1|e] eqn:P1; simpl in T; try discriminate.
  unfold transf_clight_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  destruct (SimplLocals.transf_program p1) as [p2|e] eqn:P2; simpl in T; try discriminate.
  destruct (Cshmgen.transl_program p2) as [p3|e] eqn:P3; simpl in T; try discriminate.
  destruct (Cminorgen.transl_program p3) as [p4|e] eqn:P4; simpl in T; try discriminate.
  unfold transf_cminor_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  destruct (Selection.sel_program p4) as [p5|e] eqn:P5; simpl in T; try discriminate.
  destruct (RTLgen.transl_program p5) as [p6|e] eqn:P6; simpl in T; try discriminate.
  unfold transf_rtl_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  set (p7 := total_if optim_tailcalls Tailcall.transf_program p6) in *.
  destruct (Inlining.transf_program p7) as [p8|e] eqn:P8; simpl in T; try discriminate.
  set (p9 := Renumber.transf_program p8) in *.
  set (p10 := total_if optim_constprop Constprop.transf_program p9) in *.
  set (p11 := total_if optim_constprop Renumber.transf_program p10) in *.
  destruct (partial_if optim_CSE CSE.transf_program p11) as [p12|e] eqn:P12; simpl in T; try discriminate.
  destruct (partial_if optim_redundancy Deadcode.transf_program p12) as [p13|e] eqn:P13; simpl in T; try discriminate.
  destruct (Unusedglob.transform_program p13) as [p14|e] eqn:P14; simpl in T; try discriminate.
  inv T.
  unfold match_prog; simpl.
  exists p1; split. apply SimplExprproof.transf_program_match; auto.
  exists p2; split. apply SimplLocalsproof.match_transf_program; auto.
  exists p3; split. apply Cshmgenproof.transf_program_match; auto.
  exists p4; split. apply Cminorgenproof.transf_program_match; auto.
  exists p5; split. apply Selectionproof.transf_program_match; auto.
  exists p6; split. apply RTLgenproof.transf_program_match; auto.
  exists p7; split. apply total_if_match. apply Tailcallproof.transf_program_match.
  exists p8; split. apply Inliningproof.transf_program_match; auto.
  exists p9; split. apply Renumberproof.transf_program_match; auto.
  exists p10; split. apply total_if_match. apply Constpropproof.transf_program_match.
  exists p11; split. apply total_if_match. apply Renumberproof.transf_program_match.
  exists p12; split. eapply partial_if_match; eauto. apply CSEproof.transf_program_match.
  exists p13; split. eapply partial_if_match; eauto. apply Deadcodeproof.transf_program_match.
  exists tp; split. apply Unusedglobproof.transf_program_match; auto.
  reflexivity.
Qed.

Ltac DestructM :=
  match goal with
    [ H: exists p, _ /\ _ |- _ ] =>
      let p := fresh "p" in let M := fresh "M" in
                            let MM := fresh "MM" in
                            destruct H as (p & M & MM); clear H
  end.

Lemma match_prog_c_rtl_forward_simulation p tp :
  match_prog_c_rtl p tp ->
  forward_simulation (Cstrategy.semantics p) (RTL.semantics tp).
Proof.
  intro Hmatch.
  unfold match_prog_c_rtl, pass_match in Hmatch; simpl in Hmatch.
  repeat DestructM. subst p14.
  eapply compose_forward_simulations.
  eapply SimplExprproof.transl_program_correct; eassumption.
  eapply compose_forward_simulations.
  eapply SimplLocalsproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
  eapply Cshmgenproof.transl_program_correct; eassumption.
  eapply compose_forward_simulations.
  eapply Cminorgenproof.transl_program_correct; eassumption.
  eapply compose_forward_simulations.
  eapply Selectionproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
  eapply RTLgenproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
  eapply match_if_simulation. eassumption. exact Tailcallproof.transf_program_correct.
  eapply compose_forward_simulations.
  eapply Inliningproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations. eapply Renumberproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
  eapply match_if_simulation. eassumption. exact Constpropproof.transf_program_correct.
  eapply compose_forward_simulations.
  eapply match_if_simulation. eassumption. exact Renumberproof.transf_program_correct.
  eapply compose_forward_simulations.
  eapply match_if_simulation. eassumption. exact CSEproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
  eapply match_if_simulation. eassumption. exact Deadcodeproof.transf_program_correct; eassumption.
  eapply Unusedglobproof.transf_program_correct; eassumption.
Qed.

Lemma match_prog_c_rtl_backward_simulation p tp :
  match_prog_c_rtl p tp ->
  backward_simulation (Csem.semantics p) (RTL.semantics tp).
Proof.
  intros.
  apply compose_backward_simulation with (atomic (Cstrategy.semantics p)).
  eapply sd_traces; eapply RTL.semantics_determinate.
  apply factor_backward_simulation.
  apply Cstrategy.strategy_simulation.
  apply Csem.semantics_single_events.
  eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  apply forward_to_backward_simulation.
  - apply factor_forward_simulation.
    + apply match_prog_c_rtl_forward_simulation; assumption.
    + apply sd_traces, RTL.semantics_determinate.
  - apply atomic_receptive.
    apply Cstrategy.semantics_strongly_receptive.
  - apply RTL.semantics_determinate.
Qed.

Lemma transf_c_program_to_rtl'_preservation p tp beh :
  transf_c_program_to_rtl' p = OK tp ->
  program_behaves (RTL.semantics tp) beh ->
  exists beh', program_behaves (Csem.semantics p) beh' /\
            behavior_improves beh' beh.
Proof.
  unfold transf_c_program_to_rtl'.
  intros Hmatch Hbeh.
  apply transf_c_to_rtl_match_prog in Hmatch.
  eapply backward_simulation_behavior_improves; eauto.
  apply match_prog_c_rtl_backward_simulation; assumption.
Qed.



Definition rtl_to_rtl_passes :=
      mkpass (match_if Compopts.dmr RTLdmrproof.match_prog)
  ::: mkpass (match_if Compopts.tmr RTLtmrproof.match_prog)
  ::: mkpass Renumberproof.match_prog
  ::: pass_nil _.

Definition match_prog_rtl_rtl: RTL.program -> RTL.program -> Prop :=
  pass_match (compose_passes rtl_to_rtl_passes).

Lemma transf_rtl_program_to_rtl_match_prog p tp :
  transf_rtl_program_to_rtl' p = OK tp ->
  match_prog_rtl_rtl p tp.
Proof.
  intro T.
  unfold transf_rtl_program_to_rtl', time in T.
  rewrite ! compose_print_identity in T. simpl in T.
  destruct (partial_if dmr RTLdmr.transf_program p) as [pdmr|e] eqn:Pdmr;
    simpl in T; try discriminate.
  destruct (partial_if tmr RTLtmr.transf_program pdmr) as [p15'|e] eqn:P15;
    simpl in T; try discriminate.
  set (p15 := Renumber.transf_program p15') in *.
  inv T.
  unfold match_prog_rtl_rtl; simpl.
  exists pdmr; split. eapply partial_if_match; eauto.
  apply RTLdmrproof.transf_program_match; auto.
  exists p15'; split. eapply partial_if_match; eauto.
  apply RTLtmrproof.transf_program_match; auto.
  exists p15; split. apply Renumberproof.transf_program_match; auto.
  reflexivity.
Qed.

Lemma transf_rtl_program_to_rtl'_forward_simulation p tp :
  transf_rtl_program_to_rtl' p = OK tp ->
  forward_simulation (RTL.semantics p) (RTL.semantics tp).
Proof.
  intro Hmatch.
  apply transf_rtl_program_to_rtl_match_prog in Hmatch.
  unfold match_prog_rtl_rtl, pass_match in Hmatch; simpl in Hmatch.
  repeat DestructM. subst p3.
  eapply compose_forward_simulations.
  eapply match_if_simulation. eassumption.
  apply RTLdmrproof.transf_program_correct; assumption.
  eapply compose_forward_simulations.
  eapply match_if_simulation. eassumption.
  apply RTLtmrproof.transf_program_correct; assumption.
  apply Renumberproof.transf_program_correct; assumption.
Qed.

Lemma transf_rtl_program_to_rtl'_preservation p tp beh :
  transf_rtl_program_to_rtl' p = OK tp ->
  program_behaves (RTL.semantics tp) beh ->
  exists beh', program_behaves (RTL.semantics p) beh' /\
            behavior_improves beh' beh.
Proof.
  intros Hp Hbeh.
  eapply backward_simulation_behavior_improves; eauto.
  apply forward_to_backward_simulation.
  - apply transf_rtl_program_to_rtl'_forward_simulation; assumption.
  - apply RTL.semantics_receptive.
  - apply RTL.semantics_determinate.
Qed.

(** The core fault-tolerance preservation theorem. For any C program [p]
    compiled to RTL program [tp] (with TMR), if [tp] passes the well-coloredness
    check, then every behavior of the faulty semantics (single-fault model) is
    refined by some C source behavior.

    The proof composes two refinement steps via [behavior_improves_trans]:
    1. faulty(tp) -> RTL3(tp): backward simulation from RTLtolerant
       yields beh3 with [behavior_improves beh3 beh]
    2. RTL3(tp) = RTL(tp): for well-colored programs, every RTL3 behavior
       is also an RTL behavior ([wc_rtl3_behavior_in_rtl])
    3. RTL(tp) -> C(p): backward simulation from Compiler
       yields beh_c with [behavior_improves beh_c beh3]

    Then [behavior_improves_trans beh_c beh3 beh] gives the result.

    This avoids the diamond problem that arises from using the RTL3->RTL
    forward simulation (which only gives [behavior_improves], not equality).
    The key insight is that for well-colored programs, RTL3 and RTL produce
    identical behaviors, so no "improvement" step is needed. *)

(** For well-colored programs, every RTL3 behavior is also an RTL behavior.

    This holds because [vote3(a,a,a) = a] for well-colored programs, so
    RTL3 and RTL semantics agree on every step.  In particular, RTL3
    cannot go wrong at a point where RTL continues: when RTL3 is stuck
    (e.g., Iload with Vundef address from a disagreeing vote), the
    well-coloredness guarantee ensures the corresponding RTL register
    holds the same value, so RTL is stuck too.

    Formally closing this requires strengthening the RTL3->RTL forward
    simulation in RTLagreement.v to maintain register equality (not just
    [Val.lessdef]) under the well-coloredness hypothesis. *)
Lemma wc_rtl3_behavior_in_rtl:
  forall p, wc_program p ->
  forall beh, program_behaves (RTL3.semantics p) beh ->
  program_behaves (RTL.semantics p) beh.
Proof.
  intros p HWC beh HBEH.
  exact (RTLagreement.wc_rtl3_behavior_in_rtl p beh HBEH).
Qed.

Theorem transf_c_program_to_rtl_preservation_faulty:
  forall p tp beh,
    transf_c_program_to_rtl p = OK tp ->
    RTLcolorcheck.check_program tp = true ->
    program_behaves (faulty_semantics tp) beh ->
    exists beh', program_behaves (Csem.semantics p) beh' /\
              behavior_improves beh' beh.
Proof.
  intros p tp beh HTRANSF HCHECK HFAULTY.
  (* Establish well-coloredness *)
  apply check_program_sound in HCHECK.
  (* Step 1: faulty(tp) -> RTL3(tp) via backward simulation *)
  pose proof (faulty_backward_simulation tp HCHECK) as BSIM1.
  pose proof (backward_simulation_behavior_improves BSIM1 HFAULTY)
    as (beh3 & HBEH3 & HIMP_3_beh).
  (* Step 2: RTL3(tp) behaves same as RTL(tp) for well-colored programs *)
  pose proof (wc_rtl3_behavior_in_rtl tp HCHECK beh3 HBEH3) as HBEH2.
  (* Step 3: RTL(tp) -> C(p) via backward simulation *)
  pose proof (transf_c_program_to_rtl_correct p tp HTRANSF) as BSIM2.
  pose proof (backward_simulation_behavior_improves BSIM2 HBEH2)
    as (beh_c & HBEHC & HIMP_c_3).
  (* Compose: beh_c improves beh3, beh3 improves beh *)
  exists beh_c; split; auto.
  eapply behavior_improves_trans; eauto.
Qed.

(** As a corollary, if the source C code cannot go wrong, i.e. is free of
  undefined behaviors, the behavior of the generated assembly code is
  one of the possible behaviors of the source C code. *)

Theorem transf_c_program_is_refinement:
  forall p tp,
  transf_c_program p = OK tp ->
  (forall beh, program_behaves (Csem.semantics p) beh -> not_wrong beh) ->
  (forall beh, program_behaves (Asm.semantics tp) beh -> program_behaves (Csem.semantics p) beh).
Proof.
  intros. eapply backward_simulation_same_safe_behavior; eauto.
  apply transf_c_program_correct; auto.
Qed.

(** If we consider the C evaluation strategy implemented by the compiler,
  we get stronger preservation results. *)

Theorem transf_cstrategy_program_preservation:
  forall p tp,
  transf_c_program p = OK tp ->
  (forall beh, program_behaves (Cstrategy.semantics p) beh ->
     exists beh', program_behaves (Asm.semantics tp) beh' /\ behavior_improves beh beh')
/\(forall beh, program_behaves (Asm.semantics tp) beh ->
     exists beh', program_behaves (Cstrategy.semantics p) beh' /\ behavior_improves beh' beh)
/\(forall beh, not_wrong beh ->
     program_behaves (Cstrategy.semantics p) beh -> program_behaves (Asm.semantics tp) beh)
/\(forall beh,
     (forall beh', program_behaves (Cstrategy.semantics p) beh' -> not_wrong beh') ->
     program_behaves (Asm.semantics tp) beh ->
     program_behaves (Cstrategy.semantics p) beh).
Proof.
  assert (WBT: forall p, well_behaved_traces (Cstrategy.semantics p)).
    intros. eapply ssr_well_behaved. apply Cstrategy.semantics_strongly_receptive.
  intros.
  assert (MATCH: Compiler.match_prog p tp) by (apply transf_c_program_match; auto).
  intuition auto.
  eapply forward_simulation_behavior_improves; eauto.
    apply (proj1 (cstrategy_semantic_preservation _ _ MATCH)).
  exploit backward_simulation_behavior_improves.
    apply (proj2 (cstrategy_semantic_preservation _ _ MATCH)).
    eauto.
  intros [beh1 [A B]]. exists beh1; split; auto. rewrite atomic_behaviors; auto.
  eapply forward_simulation_same_safe_behavior; eauto.
    apply (proj1 (cstrategy_semantic_preservation _ _ MATCH)).
  exploit backward_simulation_same_safe_behavior.
    apply (proj2 (cstrategy_semantic_preservation _ _ MATCH)).
    intros. rewrite <- atomic_behaviors in H2; eauto. eauto.
    intros. rewrite atomic_behaviors; auto.
Qed.

(** We can also use the alternate big-step semantics for [Cstrategy]
  to establish behaviors of the generated assembly code. *)

Theorem bigstep_cstrategy_preservation:
  forall p tp,
  transf_c_program p = OK tp ->
  (forall t r,
     Cstrategy.bigstep_program_terminates p t r ->
     program_behaves (Asm.semantics tp) (Terminates t r))
/\(forall T,
     Cstrategy.bigstep_program_diverges p T ->
       program_behaves (Asm.semantics tp) (Reacts T)
    \/ exists t, program_behaves (Asm.semantics tp) (Diverges t) /\ traceinf_prefix t T).
Proof.
  intuition.
  apply transf_cstrategy_program_preservation with p; auto. red; auto.
  apply behavior_bigstep_terminates with (Cstrategy.bigstep_semantics p); auto.
  apply Cstrategy.bigstep_semantics_sound.
  exploit (behavior_bigstep_diverges (Cstrategy.bigstep_semantics_sound p)). eassumption.
  intros [A | [t [A B]]].
  left. apply transf_cstrategy_program_preservation with p; auto. red; auto.
  right; exists t; split; auto. apply transf_cstrategy_program_preservation with p; auto. red; auto.
Qed.

(** * Satisfaction of specifications *)

(** The second additional results shows that if all executions
  of the source C program satisfies a given specification,
  then all executions of the produced Asm program satisfy
  this specification as well.  *)

(** The specifications we consider here are sets of observable
  behaviors, representing the good behaviors a program is expected
  to have.  A specification can be as simple as
  ``the program does not go wrong'' or as precise as
  ``the program prints a prime number then terminates with code 0''.
  As usual in Coq, sets of behaviors are represented as predicates
  [program_behavior -> Prop]. *)

Definition specification := program_behavior -> Prop.

(** A program satisfies a specification if all its observable behaviors
  are in the specification. *)

Definition c_program_satisfies_spec (p: Csyntax.program) (spec: specification): Prop :=
  forall beh,  program_behaves (Csem.semantics p) beh -> spec beh.
Definition asm_program_satisfies_spec (p: Asm.program) (spec: specification): Prop :=
  forall beh,  program_behaves (Asm.semantics p) beh -> spec beh.
  
(** It is not always the case that if the source program satisfies a
  specification, then the generated assembly code satisfies it as
  well.  For example, if the specification is ``the program goes wrong
  on an undefined behavior'', a C source that goes wrong satisfies
  this specification but can be compiled into Asm code that does not
  go wrong and therefore does not satisfy the specification.

  For this reason, we restrict ourselves to safety-enforcing specifications:
  specifications that exclude ``going wrong'' behaviors and are satisfied
  only by programs that execute safely. *)

Definition safety_enforcing_specification (spec: specification): Prop :=
  forall beh, spec beh -> not_wrong beh.

(** As the main result of this section, we show that CompCert
  compilation preserves safety-enforcing specifications: 
  any such specification that is satisfied by the source C program is
  always satisfied by the generated assembly code. *)

Theorem transf_c_program_preserves_spec:
  forall p tp spec,
  transf_c_program p = OK tp ->
  safety_enforcing_specification spec ->
  c_program_satisfies_spec p spec ->
  asm_program_satisfies_spec tp spec.
Proof.
  intros p tp spec TRANSF SES CSAT; red; intros beh AEXEC.
  exploit transf_c_program_preservation; eauto. intros (beh' & CEXEC & IMPR).
  apply CSAT in CEXEC. destruct IMPR as [EQ | [t [A B]]].
- congruence.
- subst beh'. apply SES in CEXEC. contradiction. 
Qed.

(** Safety-enforcing specifications are not the only good properties
  of source programs that are preserved by compilation.  Another example
  of a property that is preserved is the ``initial trace'' property:
  all executions of the program start by producing an expected trace
  of I/O actions, representing the good behavior expected from the program.
  After that, the program may terminate, or continue running, or go wrong
  on an undefined behavior.  What matters is that the program produced
  the expected trace at the beginning of its execution.  This is a typical
  liveness property, and it is preserved by compilation. *)

Definition c_program_has_initial_trace (p: Csyntax.program) (t: trace): Prop :=
  forall beh, program_behaves (Csem.semantics p) beh -> behavior_prefix t beh.
Definition asm_program_has_initial_trace (p: Asm.program) (t: trace): Prop :=
  forall beh, program_behaves (Asm.semantics p) beh -> behavior_prefix t beh.

Theorem transf_c_program_preserves_initial_trace:
  forall p tp t,
  transf_c_program p = OK tp ->
  c_program_has_initial_trace p t ->
  asm_program_has_initial_trace tp t.
Proof.
  intros p tp t TRANSF CTRACE; red; intros beh AEXEC.
  exploit transf_c_program_preservation; eauto. intros (beh' & CEXEC & IMPR).
  apply CTRACE in CEXEC. destruct IMPR as [EQ | [t' [A B]]].
- congruence.
- destruct CEXEC as (beh1' & EQ').
  destruct B as (beh1 & EQ).
  subst beh'. destruct beh1'; simpl in A; inv A. 
  exists (behavior_app t0 beh1). apply behavior_app_assoc.
Qed.

(** * Extension to separate compilation *)

(** The results above were given in terms of whole-program compilation.
    They also extend to separate compilation followed by linking. *)

Section SEPARATE_COMPILATION.

(** The source: a list of C compilation units *)
Variable c_units: nlist Csyntax.program.

(** The compiled code: a list of Asm compilation units, obtained by separate compilation *)
Variable asm_units: nlist Asm.program.
Hypothesis separate_compilation_succeeds: 
  nlist_forall2 (fun cu tcu => transf_c_program cu = OK tcu) c_units asm_units.

(** We assume that the source C compilation units can be linked together
    to obtain a monolithic C program [c_program]. *)
Variable c_program: Csyntax.program.
Hypothesis source_linking: link_list c_units = Some c_program.

(** Then, linking the Asm units obtained by separate compilation succeeds. *)
Lemma compiled_linking_succeeds:
  { asm_program | link_list asm_units = Some asm_program }.
Proof.
  destruct (link_list asm_units) eqn:E. 
- exists p; auto.
- exfalso. 
  exploit separate_transf_c_program_correct; eauto. intros (a & P & Q).
  congruence.
Qed.

(** Let asm_program be the result of linking the Asm units. *)
Let asm_program: Asm.program := proj1_sig compiled_linking_succeeds.
Let compiled_linking: link_list asm_units = Some asm_program := proj2_sig compiled_linking_succeeds.

(** Then, [asm_program] preserves the semantics and the specifications of
  [c_program], in the following sense.
  First, every behavior of [asm_program] improves upon one of the possible
  behaviors of [c_program]. *)

Theorem separate_transf_c_program_preservation:
  forall beh,
  program_behaves (Asm.semantics asm_program) beh ->
  exists beh', program_behaves (Csem.semantics c_program) beh' /\ behavior_improves beh' beh.
Proof.
  intros. exploit separate_transf_c_program_correct; eauto. intros (a & P & Q).
  assert (a = asm_program) by congruence. subst a. 
  eapply backward_simulation_behavior_improves; eauto.
Qed.

(** As a corollary, if [c_program] is free of undefined behaviors, 
  the behavior of [asm_program] is one of the possible behaviors of [c_program]. *)

Theorem separate_transf_c_program_is_refinement:
  (forall beh, program_behaves (Csem.semantics c_program) beh -> not_wrong beh) ->
  (forall beh, program_behaves (Asm.semantics asm_program) beh -> program_behaves (Csem.semantics c_program) beh).
Proof.
  intros. exploit separate_transf_c_program_preservation; eauto. intros (beh' & P & Q).
  assert (not_wrong beh') by auto.
  inv Q.
- auto.
- destruct H2 as (t & U & V). subst beh'. elim H1. 
Qed.

(** We now show that if all executions of [c_program] satisfy a specification,
  then all executions of [asm_program] also satisfy the specification, provided
  the specification is of the safety-enforcing kind. *)

Theorem separate_transf_c_program_preserves_spec:
  forall spec,
  safety_enforcing_specification spec ->
  c_program_satisfies_spec c_program spec ->
  asm_program_satisfies_spec asm_program spec.
Proof.
  intros spec SES CSAT; red; intros beh AEXEC.
  exploit separate_transf_c_program_preservation; eauto. intros (beh' & CEXEC & IMPR).
  apply CSAT in CEXEC. destruct IMPR as [EQ | [t [A B]]].
- congruence.
- subst beh'. apply SES in CEXEC. contradiction. 
Qed.

(** As another corollary of [separate_transf_c_program_preservation],
  if all executions of [c_program] have a trace [t] as initial trace,
  so do all executions of [asm_program]. *)

Theorem separate_transf_c_program_preserves_initial_trace:
  forall t,
  c_program_has_initial_trace c_program t ->
  asm_program_has_initial_trace asm_program t.
Proof.
  intros t CTRACE; red; intros beh AEXEC.
  exploit separate_transf_c_program_preservation; eauto. intros (beh' & CEXEC & IMPR).
  apply CTRACE in CEXEC. destruct IMPR as [EQ | [t' [A B]]].
- congruence.
- destruct CEXEC as (beh1' & EQ').
  destruct B as (beh1 & EQ).
  subst beh'. destruct beh1'; simpl in A; inv A. 
  exists (behavior_app t0 beh1). apply behavior_app_assoc.
Qed.

End SEPARATE_COMPILATION.
