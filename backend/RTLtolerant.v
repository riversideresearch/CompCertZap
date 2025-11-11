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
  RTLtmr
  RTLtmrspec
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
           forall r, col r <> Some c -> rs1 # r = rs2 # r
  else
    forall r, rs1 # r = rs2 # r.

(* Definition rs_compat (rs1 rs2 : regset) : Prop := *)
(*   forall r, val_compat (rs1 # r) (rs2 # r). *)

Section match_states.

  (** When a fault has occurred elsewhere and regsets [rs1] and [rs2]
      are unchanged, they still match. *)
  Lemma match_rs_fault col (pc : node) (rs1 rs2 : regset) :
    match_rs (col pc) false rs1 rs2 ->
    match_rs (col pc) true rs1 rs2.
  Proof. intro H; exists Red; split; auto; constructor. Qed.

  Inductive match_stackframes (faulted : bool)
    : RTL.stackframe -> RTL.stackframe -> Prop :=
  | match_stackframes_Stackframe : forall col res f1 f2 sp pc rs1 rs2
                                          (* (MATCH: match_votes_function f1 f2) *)
                                          (WC_FUN: wc_function col f1)
                                          (* (RS_COMPAT: rs_compat rs1 rs2) *)
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

  (** When a fault hasn't occurred, equality should hold between all
      registers. When a fault has occurred, it should hold between all
      registers except those of the affected color. *)
  Inductive match_states : bool -> RTL.state -> fstate -> Prop :=
  | match_states_State :
    forall col stk1 stk2 f sp pc rs1 rs2 m (b : bool)
      (STK: Forall2 (match_stackframes b) stk1 stk2)
      (* (VOTE: match_votes_function f1 f2) *)
      (WC_FUN: wc_function col f)
      (* (RS_COMPAT: rs_compat rs1 rs2) *)
      (RS: match_rs (col pc) b rs1 rs2),
      (* (MEM: Memory.Mem.extends m1 m2), *)
      match_states b (State stk1 f sp pc rs1 m)
                   {| fs_state := State stk2 f sp pc rs2 m; fault := b |}
  | match_states_Callstate :
    forall stk1 stk2 fd args m b
      (STK: Forall2 (match_stackframes b) stk1 stk2),
      (* (VOTE: match_votes_fundef fd1 fd2) *)
      (* (LESSDEF: Forall2 Val.lessdef args1 args2) *)
      (* (MEM: Memory.Mem.extends m1 m2), *)
      match_states b (Callstate stk1 fd args m)
                   {| fs_state := Callstate stk2 fd args m; fault := b |}
  | match_state_Returnstate :
    forall stk1 stk2 v m b
      (STK: Forall2 (match_stackframes b) stk1 stk2),
      (* (LESSDEF: Val.lessdef v1 v2) *)
      (* (MEM: Memory.Mem.extends m1 m2), *)
      match_states b (Returnstate stk1 v m)
                   {| fs_state := Returnstate stk2 v m; fault := b |}.

End match_states.

Lemma init_match_states_refl p s :
  RTL.initial_state p s ->
  match_states false s {| fs_state := s; fault := false |}.
Proof.
  intro Hinit; inv Hinit.
  constructor; auto.
  (* apply Memory.Mem.extends_refl. *)
Qed.

Section TOLERANCE.
  Variable prog : program.
  (* Variable prog2 : program. *)
  (* Hypothesis PROG : match_votes_program prog1 prog2. *)
  Let ge := Genv.globalenv prog.
  (* Let ge2 := Genv.globalenv prog2. *)

  Hypothesis WC_prog : wc_program prog.

  Lemma forall2_match_stackframes_fault stk1 stk2 :
    Forall2 (match_stackframes false) stk1 stk2 ->
    Forall2 (match_stackframes true) stk1 stk2.
  Proof.
    induction 1; constructor; auto.
    apply match_stackframes_fault; auto.
  Qed.

  Lemma maybe_zap_preserves_match_states s s1 s2 b2 :
    match_states false s {| fs_state := s1; fault := false |} ->
    maybe_zap s1 s2 b2 ->
    match_states b2 s {| fs_state := s2; fault := b2 |}.
  Proof.
    intros Hmatch Hzap.
    inv Hzap; auto.
    inv Hmatch.
    econstructor; eauto.
    - apply forall2_match_stackframes_fault; auto.
    (* - unfold rs_compat. *)
    (*   intro x. *)
    (*   unfold rs_compat in RS_COMPAT. *)
    (*   specialize (RS_COMPAT x). *)
    (*   destruct (DecidableTypeEx.Positive_as_DT.eq_dec x r); subst. *)
    (*   + rewrite Regmap.gss; auto. *)
    (*     eapply val_compat_trans; eauto. *)
    (*   + rewrite Regmap.gso; auto. *)
    - unfold match_rs in *.
      (* exists color of faulted register r *)
      admit.
  Admitted.

  Lemma match_states_fault_inv b1 b2 s1 s2 :
    match_states b1 s1 {| fs_state := s2; fault := b2 |} ->
    b1 = b2.
  Proof. intro Hmatch; inv Hmatch; reflexivity. Qed.

  Definition fault_order (b1 b2 : bool) : Prop :=
    b1 = true /\ b2 = false.

  Lemma well_founded_fault_order :
    well_founded fault_order.
  Proof.
    intros [].
    - constructor; intros b []; congruence.
    - constructor; intros b []; subst.
      constructor; intros b []; congruence.
  Qed.

  Lemma final_state_dec s : { exists r, final_state (faulty_semantics prog) s r } +
                              { ~ (exists r, final_state (faulty_semantics prog) s r) }.
  Proof.
    simpl in *.
    destruct s.
    destruct fs_state.
    - right; intros [r HC]; inv HC.
    - right; intros [r HC]; inv HC.
    - destruct stack.
      2: { right; intros [r HC]; inv HC. }
      destruct v; try solve [right; intros [r HC]; inv HC].
      left; exists i; constructor.
  Qed.

  Lemma match_states_final b s fs r :
    match_states b s fs ->
    final_state (@RTL.semantics Builtins2.Three VoteSemantics_Three prog) s r ->
    final_state (faulty_semantics prog) fs r.
  Proof.
    intros Hmatch Hfin; inv Hfin.
    inv Hmatch; inv STK; constructor.
  Qed.

  (* Lemma kdsfgd v1 v1' v2 v2' v : *)
  (*   val_compat v1 v1' -> *)
  (*   val_compat v2 v2' -> *)
  (*   Val.divs v1 v2 = Some v -> *)
  (*   exists v', Val.divs v1' v2' = Some v'. *)
  (* Proof. *)
  (*   intros H0 H1 Hdivs. *)
  (*   inv H0; simpl in *; try congruence. *)
  (*   inv H1; simpl in *; try congruence. *)
  (*   eexists. *)
  (*   destruct (Integers.Int.eq _ _). *)

  (* TODO: vote on division and mod operations so we have guaranteed
     equality of register contents for them, so we don't need the
     rs_compat invariant. Probably admit soundness proof for them at
     first since we know it won't be a problem. *)

  (* Lemma rs_compat_eval_operation rs1 rs2 sp op args m v : *)
  (*   rs_compat rs1 rs2 -> *)
  (*   Op.eval_operation (Genv.globalenv prog) sp op rs1 ## args m = Some v -> *)
  (*   exists v', Op.eval_operation (Genv.globalenv prog) sp op rs2 ## args m = Some v'. *)
  (* Proof. *)
  (*   intros Hcompat Hop. *)
  (*   destruct op; simpl in *; *)
  (*     try (destruct args; simpl in *; try congruence); *)
  (*     try (destruct args; simpl in *; try congruence); *)
  (*     try (destruct args; simpl in *; try congruence); *)
  (*     inv Hop; eexists; eauto. *)
  (*   - unfold Val.divs in *. *)
  (*     simpl in *. *)
  (* Admitted. *)

  Ltac inv_Forall :=
    repeat match goal with
      | [H : Forall _ (_ :: _) |- _] => inv H
      end.

  (* Lemma rs_eq_eval_addressing sp addr rs1 rs2 args a : *)
  (*   (forall r, rs1 # r = rs2 # r) -> *)
  (*   Op.eval_addressing (Genv.globalenv prog) sp addr rs1 ## args = Some a -> *)
  (*   Op.eval_addressing (Genv.globalenv prog) sp addr rs2 ## args = Some a. *)
  (* Proof. *)
  (*   unfold Op.eval_addressing. *)
  (*   destruct Archi.ptr64 eqn: Harchi. *)
  (*   - intros Heq Heval. *)
  (*     destruct addr; simpl in *; *)
  (*       repeat (destruct args; simpl in *; try congruence). *)
  (*   - intros Heq Heval. *)
  (*     destruct addr; simpl in *; try rewrite Harchi in *; *)
  (*       repeat (destruct args; simpl in *; try congruence). *)
  (* Qed. *)

  Lemma rs_eq_eval_addressing sp addr rs1 rs2 args a :
    Forall (fun r => rs1 # r = rs2 # r) args ->
    Op.eval_addressing (Genv.globalenv prog) sp addr rs1 ## args = Some a ->
    Op.eval_addressing (Genv.globalenv prog) sp addr rs2 ## args = Some a.
  Proof.
    unfold Op.eval_addressing.
    destruct Archi.ptr64 eqn: Harchi.
    - intros Heq Heval.
      destruct addr; simpl in *;
        repeat (destruct args; inv_Forall; simpl in *; try congruence).
    - intros Heq Heval.
      destruct addr; simpl in *; try rewrite Harchi in *;
        repeat (destruct args; inv_Forall; simpl in *; try congruence).
  Qed.

  Lemma rs_eq_eval_condition cond rs1 rs2 args m b :
    Forall (fun r => rs1 # r = rs2 # r) args ->
    Op.eval_condition cond rs1 ## args m = Some b ->
    Op.eval_condition cond rs2 ## args m = Some b.
  Proof.
    intros Hforall Heval.
    destruct cond; simpl in *;
      repeat (destruct args; simpl in *; inv_Forall; try congruence).
  Qed.

  Lemma rs_eq_eval_operation rs1 rs2 sp op args m v :
    Forall (fun a => rs1 # a = rs2 # a) args ->
    Op.eval_operation (Genv.globalenv prog) sp op rs1 ## args m = Some v ->
    Op.eval_operation (Genv.globalenv prog) sp op rs2 ## args m = Some v.
  Proof.
    intros Heq Hop.
    destruct op; simpl in *;
      try (destruct args; simpl in *; try congruence);
      inv_Forall;
      try (destruct args; simpl in *; try congruence);
      inv_Forall;
      try (destruct args; simpl in *; try congruence);
      inv_Forall.
    - rewrite <- H1, <- H2, <- H3; auto.
    - rewrite <- H1, <- H2, <- H3; auto.
    - rewrite <- H1, <- H2, <- H3; auto.
    - inv Hop.
      rewrite <- H1, <- H2, <- H3; auto.
      f_equal.
      f_equal.
      replace (rs1 # p1 :: rs2 ## args) with (rs2 ## (p1 :: args)).
      2: { simpl; rewrite H2; reflexivity. }
      (* TODO: probably need another lemma for this equation. *)
  Admitted.

  Fixpoint builtin_arg_rs_eq (rs1 rs2 : Regmap.t val) (barg : builtin_arg reg) : Prop :=
    match barg with
    | BA r => rs1 # r = rs2 # r
    | BA_splitlong hi lo => builtin_arg_rs_eq rs1 rs2 hi /\ builtin_arg_rs_eq rs1 rs2 lo
    | BA_addptr a1 a2 => builtin_arg_rs_eq rs1 rs2 a1 /\ builtin_arg_rs_eq rs1 rs2 a2
    | _ => True
    end.

  Lemma in_builtin_arg_rs_eq rs1 rs2 arg :
    (forall r, in_builtin_arg r arg -> rs1 # r = rs2 # r) ->
    builtin_arg_rs_eq rs1 rs2 arg.
  Proof.
    induction arg; simpl; intros Hin; auto.
    - apply Hin; constructor.
    - split; try apply IHarg1; try apply IHarg2;
        intros x Hx; apply Hin; solve [constructor; auto].
    - split; try apply IHarg1; try apply IHarg2;
        intros x Hx; apply Hin; solve [constructor; auto].
  Qed.

  Lemma rs_eq_eval_builtin_arg rs1 rs2 barg sp m b :
    builtin_arg_rs_eq rs1 rs2 barg ->
    eval_builtin_arg (Genv.globalenv prog) (fun r : positive => rs1 # r) sp m barg b ->
    eval_builtin_arg (Genv.globalenv prog) (fun r : positive => rs2 # r) sp m barg b.
  Proof.
    revert b.
    induction barg; simpl; intros b Heq Heval; inv Heval; try solve [constructor; auto].
    - rewrite Heq; constructor.
    - destruct Heq as [Heq0 Heq1]; constructor; auto.
    - destruct Heq as [Heq0 Heq1]; constructor; auto.
  Qed.

  Lemma rs_eq_eval_builtin_args rs1 rs2 sp m args vargs :
    Forall (builtin_arg_rs_eq rs1 rs2) args ->
    eval_builtin_args (Genv.globalenv prog) (fun r : positive => rs1 # r) sp m args vargs ->
    eval_builtin_args (Genv.globalenv prog) (fun r : positive => rs2 # r) sp m args vargs.
  Proof.
    revert vargs; induction args; intro vargs;
      intros Hforall Heval; inv Heval; constructor; inv Hforall.
    - eapply rs_eq_eval_builtin_arg; eauto.
    - apply IHargs; auto.
  Qed.

  Ltac inv_stk :=
    match goal with
    | [ H : Forall2 (match_stackframes false)
              (Stackframe ?res ?f ?sp ?pc ?rs :: ?s) ?stk2 |- _ ] =>
        inv H
    end.

  Lemma faulty_progress i s1 s2 :
    match_states i s1 s2 ->
    safe (@RTL.semantics Three VoteSemantics_Three prog) s1 ->
    (exists r : Integers.Int.int, final_state (faulty_semantics prog) s2 r) \/
      (exists (t : trace) (s2' : state (faulty_semantics prog)),
          Step (faulty_semantics prog) s2 t s2').
  Proof.
    intros Hmatch Hsafe.
    unfold safe in *.
    destruct (final_state_dec s2).
    { left; auto. }
    right.
    specialize (Hsafe _ (star_refl _ _ _)).
    destruct Hsafe as [[r Hfin] | (t & s'' & Hstep)].
    { exfalso; apply n; eexists; eauto.
      eapply match_states_final; eauto. }
    clear n.
    exists t.
    destruct s2.
    destruct i.
    - (* Fault has occurred *)
      replace fault with true in *.
      2: { eapply match_states_fault_inv; eauto. }
      eexists; constructor.
      admit.
    - (* Fault has NOT occurred *)
      replace fault with false in *.
      2: { eapply match_states_fault_inv; eauto. }
      simpl.
      inv Hstep; inv Hmatch; try (inv_stk; destruct y);
        (* try (eapply rs_compat_eval_operation in H0; eauto; *)
        (*      destruct H0 as [v' Hv']); *)
        eexists; econstructor; try solve [apply maybe_zap_refl].
      + eapply exec_Inop; eauto.
      + eapply exec_Iop; eauto.
        admit.
      + eapply exec_Iload; eauto.
        eapply rs_eq_eval_addressing; eauto.
        apply Forall_forall; intros; auto.
      + eapply exec_Istore; eauto.
        * eapply rs_eq_eval_addressing; eauto.
          apply Forall_forall; intros; auto.
        * rewrite <- RS; eauto.
      + eapply exec_Icall; eauto.
        destruct ros; simpl in *; auto.
        rewrite <- RS; auto.
      + eapply exec_Itailcall; eauto.
        destruct ros; simpl in *; auto.
        rewrite <- RS; auto.
      + eapply exec_Ibuiltin; eauto.
        eapply rs_eq_eval_builtin_args; eauto.
        apply Forall_forall; intros r Hr.
        apply in_builtin_arg_rs_eq.
        intros; apply RS.
      + eapply exec_Icond; eauto.
        eapply rs_eq_eval_condition; eauto.
        apply Forall_forall; intros; auto.
      + eapply exec_Ijumptable; eauto.
        rewrite <- RS; assumption.
      + eapply exec_Ireturn; eauto.
      + eapply exec_function_internal; eauto.
      + eapply exec_function_external; eauto.
      + apply exec_return.
  Admitted.

  Lemma step_simulation {VT: Builtins2.vote_type} {vsem: Builtins2.VoteSemantics VT}
    s2 t s2' b :
    b = (vote_eqb VT Two) ->
    Step (RTL.semantics prog) s2 t s2' ->
    forall i (s1 : state (@RTL.semantics Three VoteSemantics_Three prog)),
      match_states i s1 {| fs_state := s2; fault := b |} ->
      safe (RTL.semantics prog) s1 ->
      exists i' s1',
        Plus (RTL.semantics prog) s1 t s1' /\
          match_states i' s1' {| fs_state := s2'; fault := b |}.
  Proof.
    simpl; intros ? Hstep i s1 Hmatch Hsafe; subst.
    exists i.
    inv Hstep.

    (* exec_Inop *)
    - inv Hmatch.
      eexists; split.
      + econstructor.
        2: { apply star_refl. }
        2: { rewrite E0_right; reflexivity. }
        eapply RTL.exec_Inop; eauto.
      + econstructor; eauto.
        inv WC_FUN.
        apply wc_fn_code in H; inv H.
        unfold match_rs in *.
        destruct VT; simpl in *; auto.
        destruct RS as (c & Hc & RS).
        exists c; split; auto.

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

  Lemma faulty_simulation s2 t s2' :
    Step (faulty_semantics prog) s2 t s2' ->
    forall i (s1 : state (@RTL.semantics Three VoteSemantics_Three prog)),
      match_states i s1 s2 ->
      safe (RTL.semantics prog) s1 ->
      exists i' s1',
        (Plus (RTL.semantics prog) s1 t s1' \/
           Star (RTL.semantics prog) s1 t s1' /\ fault_order i' i) /\
          match_states i' s1' s2'.
  Proof.
    intros Hstep i s1 Hmatch Hsafe.
    inv Hstep.
    - (* Fault hasn't occurred yet, may happen here after this step *)
      eapply (@step_simulation Three VoteSemantics_Three) in STEP; eauto.
      destruct STEP as (i' & s1' & Hstep & Hmatch').
      exists b, s1'; split.
      + left; auto.
      + eapply maybe_zap_preserves_match_states; eauto.
        replace i' with false in *.
        2: { apply match_states_fault_inv in Hmatch'; auto. }
        assumption.
    - (* Fault has occurred already *)
      eapply step_simulation in STEP; eauto.
      destruct STEP as (i' & s1' & Hplus & Hmatch').
      exists i', s1'; split; auto.
  Qed.

  Theorem faulty_backward_simulation :
    backward_simulation
      (@RTL.semantics Builtins2.Three VoteSemantics_Three prog)
      (faulty_semantics prog).
  Proof.
    apply Backward_simulation with (order := fault_order)
                                   (match_states := match_states).
    constructor.
    - (* bsim_order_wf *)
      apply well_founded_fault_order.
    - (* bsim_initial_states_exist *)
      intros s Hs.
      exists {| fs_state := s; fault := false |}.
      constructor; auto.
    - (* bsim_match_initial_states *)
      intros s1 [s2 b] Hs1 Hs2; inv Hs2.
      exists false, s2; split; auto.
      eapply init_match_states_refl; eauto.
    - (* bsim_match_final_states *)
      intros b s1 [s2 b'] r Hmatch Hsafe Hfin.
      inv Hfin; simpl in *; subst.
      inv Hmatch; inv STK; eexists; split.
      + apply star_refl.
      + constructor.
    - (* bsim_progress *)
      apply faulty_progress.
    - (* bsim_simulation *)
      apply faulty_simulation.
    - (* bsim_public_preserved *)
      intros; reflexivity.
  Qed.

End TOLERANCE.
