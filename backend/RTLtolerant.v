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

Definition rs_compat (rs1 rs2 : regset) : Prop :=
  forall r, val_compat (rs1 # r) (rs2 # r).

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
      (RS_COMPAT: rs_compat rs1 rs2)
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
    - unfold rs_compat.
      intro x.
      unfold rs_compat in RS_COMPAT.
      specialize (RS_COMPAT x).
      destruct (peq x r); subst.
      + rewrite Regmap.gss; auto.
        eapply val_compat_trans; eauto.
      + rewrite Regmap.gso; auto.
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

  (* Lemma kdfgfd v1 v2 n v : *)
  (*   val_compat v1 v2 -> *)
  (*   Val.shrx v1 (Vint n) = Some v -> *)
  (*   exists v', Val.shrx v2 (Vint n) = Some v'. *)
  (* Proof. *)
  (*   intro Hcompat; inv Hcompat; simpl; intro H; try congruence. *)
    
  (*   unfold Val.shrx. *)
  (*   destruct v2. simpl. *)

  Ltac inv_Forall2 :=
    repeat match goal with
      | [H : Forall2 _ nil _ |- _] => inv H
      | [H : Forall2 _ _ nil |- _] => inv H
      | [H : Forall2 _ (_ :: _) _ |- _] => inv H
      | [H : Forall2 _ _ (_ :: _) |- _] => inv H
      end.

  Ltac inv_rs :=
    match goal with
    | [ H : exists c : color,
          is_basic c /\ (forall r : reg, ?col ?pc r <> Some c -> ?rs1 # r = ?rs2 # r) |- _ ] =>
        destruct H as (c & Hc & H)
    | [ H : match_rs _ true _ _ |- _ ] => destruct H as (c & Hc & H)
    end.

  Lemma val_compat_eval_addressing32 args1 args2 sp a v :
    Forall2 val_compat args1 args2 ->
    Op.eval_addressing32 (Genv.globalenv prog) sp a args1 = Some v ->
    exists v', Op.eval_addressing32 (Genv.globalenv prog) sp a args2 = Some v'.
  Proof.
    intros Hforall Hop.
    destruct a; simpl in *; try congruence;
      try solve [repeat (destruct args1; try congruence);
                 destruct Archi.ptr64; inv_Forall2; eexists; eauto].
  Qed.

  Lemma val_compat_eval_addressing64 args1 args2 sp a v :
    Forall2 val_compat args1 args2 ->
    Op.eval_addressing64 (Genv.globalenv prog) sp a args1 = Some v ->
    exists v', Op.eval_addressing64 (Genv.globalenv prog) sp a args2 = Some v'.
  Proof.
    intros Hforall Hop.
    destruct a; simpl in *; try congruence;
      try solve [repeat (destruct args1; try congruence);
                 destruct Archi.ptr64; inv_Forall2; eexists; eauto].
  Qed.

  Lemma rs_compat_eval_operation rs1 rs2 sp op args m v :
    ~ is_unsafe op ->
    rs_compat rs1 rs2 ->
    Op.eval_operation (Genv.globalenv prog) sp op rs1 ## args m = Some v ->
    exists v', Op.eval_operation (Genv.globalenv prog) sp op rs2 ## args m = Some v'.
  Proof.
    intros Hnodiv Hcompat Hop.
    destruct op; simpl in *;
      try (destruct args; simpl in *; try congruence);
      try (destruct args; simpl in *; try congruence);
      try (destruct args; simpl in *; try congruence);
      inv Hop; try solve [eexists; eauto];
      try solve [exfalso; apply Hnodiv; constructor].
    - eapply val_compat_eval_addressing32; eauto.
    - eapply val_compat_eval_addressing32; eauto.
    - eapply val_compat_eval_addressing64; eauto.
    - eapply val_compat_eval_addressing64; eauto.
  Admitted.

  Lemma eval_operation_val_compat rs1 rs2 sp op args m v v' :
    rs_compat rs1 rs2 ->
    Op.eval_operation (Genv.globalenv prog) sp op rs1 ## args m = Some v ->
    Op.eval_operation (Genv.globalenv prog) sp op rs2 ## args m = Some v' ->
    val_compat v v'.
  Proof.
    (* intros Hcompat H0 H1. *)
    (* destruct op; simpl in *; *)
    (*   try solve [destruct args; simpl in *; try congruence; *)
    (*              try solve [inv H0; inv H1; constructor]; *)
    (*              try solve [inv H0; inv H1; apply val_compat_refl]; *)
    (*              destruct args; simpl in *; try congruence; *)
    (*              inv H0; inv H1; auto]. *)
    (* - destruct args; simpl in *; try congruence. *)
    (*   destruct args; simpl in *; try congruence. *)
    (*   inv H0; inv H1. *)
    (*   apply val_compat_refl. *)
    (*   destruct args; simpl in *; try congruence. *)
  Admitted.

  (* Lemma eval_addressing_val_compat rs1 rs2 sp addr args a a' : *)
  (*   rs_compat rs1 rs2 -> *)
  (*   Op.eval_addressing (Genv.globalenv prog) sp addr rs1 ## args = Some a -> *)
  (*   Op.eval_addressing (Genv.globalenv prog) sp addr rs2 ## args = Some a' -> *)
  (*   val_compat a a'. *)
  (* Admitted. *)
                                                         
  (* Lemma not_div_eval_operation rs1 rs2 sp op args m v : *)
  (*   ~ is_div op -> *)
  (*   Op.eval_operation (Genv.globalenv prog) sp op rs1 ## args m = Some v -> *)
  (*   exists v', Op.eval_operation (Genv.globalenv prog) sp op rs2 ## args m = Some v'. *)
  (* Proof. *)
  (*   intros Hnodiv Hop. *)
  (*   destruct op; simpl in *; *)
  (*     try (destruct args; simpl in *; try congruence); *)
  (*     try (destruct args; simpl in *; try congruence); *)
  (*     try (destruct args; simpl in *; try congruence); *)
  (*     inv Hop; eexists; eauto; *)
  (*     try solve [exfalso; apply Hnodiv; constructor].     *)
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

  Lemma rs_eq_map {A : Type} (rs1 rs2 : Regmap.t A) args :
    Forall (fun a => rs1 # a = rs2 # a) args ->
    rs1 ## args = rs2 ## args.
  Proof.
    induction args; simpl; intro Hforall; auto.
    inv Hforall; rewrite H1, IHargs; auto.
  Qed.
  
  (* Lemma rs_eq_eval_addressing sp addr rs1 rs2 args a : *)
  (*   Forall (fun r => rs1 # r = rs2 # r) args -> *)
  (*   Op.eval_addressing (Genv.globalenv prog) sp addr rs1 ## args = Some a -> *)
  (*   Op.eval_addressing (Genv.globalenv prog) sp addr rs2 ## args = Some a. *)
  (* Proof. intros Hforall Hop; erewrite <- rs_eq_map; eauto. Qed. *)

  (* Lemma rs_eq_eval_condition cond rs1 rs2 args m b : *)
  (*   Forall (fun r => rs1 # r = rs2 # r) args -> *)
  (*   Op.eval_condition cond rs1 ## args m = Some b -> *)
  (*   Op.eval_condition cond rs2 ## args m = Some b. *)
  (* Proof. intros Hforall Heval; erewrite <- rs_eq_map; eauto. Qed. *)

  (* Lemma rs_eq_eval_operation rs1 rs2 sp op args m v : *)
  (*   Forall (fun a => rs1 # a = rs2 # a) args -> *)
  (*   Op.eval_operation (Genv.globalenv prog) sp op rs1 ## args m = Some v -> *)
  (*   Op.eval_operation (Genv.globalenv prog) sp op rs2 ## args m = Some v. *)
  (* Proof. intros Hforall Heval; erewrite <- rs_eq_map; eauto. Qed. *)

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

  Ltac inv_wc :=
    match goal with
    | [ H : wc_function _ _ |- _ ] => inv H
    end;
    match goal with
    | [ Hwc : wc_code _ _, Hpc : (fn_code _) ! _ = Some _ |- _ ] =>
        apply Hwc in Hpc; inv Hpc; try congruence
    end.

  Ltac inv_match_rs :=
    inv_wc;
    erewrite rs_eq_map; eauto; apply Forall_forall; intros r Hin;
    match goal with
    | [ Hrs : match_rs _ true _ _ |- _ ] =>
        destruct Hrs as (c & Hc & Hrs); rewrite Hrs; auto;
        match goal with
        | [ H : Forall (fun arg : reg => is_white _ /\ is_red _) _ |- _ ] =>
            rewrite Forall_forall in H;
            apply H in Hin; destruct Hin as [Hwhite _];
            intros HC; rewrite Hwhite in HC; inv HC; inv Hc
        end
    end.

  Ltac inv_match_rs' :=
    inv_wc;
    match goal with
    | [ Hrs : match_rs _ true _ _, Hwhite : is_white _ |- _ ] =>
        destruct Hrs as (c & Hc & Hrs); rewrite <- Hrs; eauto;
        intros HC; rewrite Hwhite in HC; inv HC; inv Hc
    end.

  Lemma known_builtin_sem_Three_Two b vargs m t v m' :
    @known_builtin_sem Three VoteSemantics_Three b (Genv.globalenv prog) vargs m t v m' ->
    exists v' m'',
      @known_builtin_sem Two VoteSemantics_Two b (Genv.globalenv prog) vargs m t v' m''.
  Proof.
    intro H; inv H.
    destruct b; simpl in *.
    - exists v, m'; constructor; auto.
    - exists v, m'; constructor; auto.
    - destruct b; simpl in *;
        repeat (destruct vargs; try congruence);
        destruct v0; inv H0; eexists; eexists; constructor; reflexivity.
  Qed.
    
  Lemma builtin_or_external_sem_Three_Two name sg vargs m t v m' :
    @builtin_or_external_sem Three VoteSemantics_Three
      name sg (Genv.globalenv prog) vargs m t v m' ->
    exists v' m'', @builtin_or_external_sem Two VoteSemantics_Two
                name sg (Genv.globalenv prog) vargs m t v' m''.
  Proof.
    unfold builtin_or_external_sem.
    intro Hsem.
    destruct (Builtins.lookup_builtin_function _ _) eqn:Hlookup.
    -  unfold Builtins.lookup_builtin_function in *.
       simpl in *.
       destruct (string_dec name _ && signature_eq sg _%asttyp);
         eapply known_builtin_sem_Three_Two; eauto.
    - eexists; eexists; eauto.
  Qed.

  Lemma external_call_Three_Two ef vargs m t v m' :
    @external_call Three VoteSemantics_Three
      ef (Genv.globalenv prog) vargs m t v m' ->
    exists v' m'', @external_call Two VoteSemantics_Two
                ef (Genv.globalenv prog) vargs m t v' m''.
  Proof.
    intro Hef.
    destruct ef; simpl in *;
      try solve [eexists; eexists; eauto];
      eapply builtin_or_external_sem_Three_Two; eauto.
  Qed.

  Inductive list_eq_mod_1 {A : Type} : list A -> list A -> Prop :=
  | list_eq_mod_1_nil : list_eq_mod_1 nil nil
  | list_eq_mod_1_cons_eq : forall x l1 l2,
      list_eq_mod_1 l1 l2 ->
      list_eq_mod_1 (x :: l1 ) (x :: l2)
  | list_eq_mod_1_cons_neq : forall x y l,
      x <> y ->
      list_eq_mod_1 (x :: l) (y :: l).
  
  Lemma idgf ef vs1 vs2 m t v m' :
    is_vote_builtin ef ->
    list_eq_mod_1 vs1 vs2 ->
    @external_call Three VoteSemantics_Three ef (Genv.globalenv prog) vs1 m t v m' ->
    @external_call Two VoteSemantics_Two ef (Genv.globalenv prog) vs2 m t v m'.
  Proof.
    intros Hbuiltin Heq Hext.
    inv Hbuiltin; simpl in *.
    - unfold builtin_or_external_sem in *.
      unfold Builtins.lookup_builtin_function in *; simpl in *.
      destruct (signature_eq _ _); simpl in *; try congruence.
      clear e.
      inv Hext; constructor; simpl in *.
      inv Heq; try congruence.
      + inv H0; try congruence.
        * inv H1; try congruence.
          { inv H0; try congruence.
            admit. }
          destruct l; try congruence.
          admit.
        * destruct l; try congruence.
          destruct l; try congruence.
          admit.
      + destruct l; try congruence.
        destruct l; try congruence.
        destruct l; try congruence.
        admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  Lemma faulty_progress i s1 s2 :
    match_states i s1 s2 ->
    safe (@RTL.semantics Three VoteSemantics_Three prog) s1 ->
    (exists r, final_state (faulty_semantics prog) s2 r) \/
      (exists t s2', Step (faulty_semantics prog) s2 t s2').
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
      inv Hstep; inv Hmatch; try (inv_stk; destruct y).
      + eexists; constructor.
        eapply exec_Inop; eauto.
      + destruct (is_unsafeb_spec op).
        * (* op is unsafe *)
          eexists; constructor.
          eapply exec_Iop; eauto.
          inv_match_rs.
        (* inv WC_FUN. *)
        (* apply wc_fn_code in H; inv H; try congruence. *)
        (* erewrite rs_eq_map; eauto. *)
        (* apply Forall_forall; intros r Hin. *)
        (* destruct RS as (c & Hc & RS). *)
        (* rewrite RS; auto. *)
        (* intro HC. *)
        (* rewrite Forall_forall in H6. *)
        (* apply H6 in Hin; destruct Hin as [Hwhite _]. *)
        (* rewrite Hwhite in HC; inv HC; inv Hc. *)
        * (* op is safe *)
          eapply rs_compat_eval_operation in H0; eauto.
          destruct H0 as [v' Hop].
          eexists; constructor.
          eapply exec_Iop; eauto.
      + eexists; constructor.
        eapply exec_Iload; eauto.
        inv_match_rs.
      + eexists; constructor.
        eapply exec_Istore with (a:=a); eauto.
        * inv_match_rs.
        * inv_match_rs'.
      + eexists; constructor.
        eapply exec_Icall; eauto.
        destruct ros; auto; simpl.
        inv_wc.
        destruct (H5 _ eq_refl) as [Hwhite _].
        inv_rs.
        rewrite <- RS; auto.
        intro HC; rewrite Hwhite in HC; inv HC; inv Hc.
      + eexists; constructor.
        eapply exec_Itailcall; eauto.
        destruct ros; auto; simpl.
        inv_wc.
        inv_rs.
        rewrite <- RS; auto.
        intro HC; rewrite H4 in HC; auto; inv HC; inv Hc.
        
      (* + eapply external_call_Three_Two in H1. *)
      (*   destruct H1 as (v' & m'' & Hef). *)
      (*   eexists; constructor. *)
      (*   eapply exec_Ibuiltin; eauto; simpl. *)
      (*   * unfold match_rs in RS. *)
      (*     eapply rs_eq_eval_builtin_args; eauto. *)
      (*     apply Forall_forall; intros r Hr. *)
      (*     apply in_builtin_arg_rs_eq. *)
      (*     inv_rs. *)
      (*     intros x Hin; apply RS. *)
      (*     intro HC. *)
      (*     inv_wc. *)
      (*     { inv Hr. *)
      (*       2: { inv H. } *)
      (*       eapply in_builtin_arg_forall in H6; eauto. *)
      (*       rewrite H6 in HC; inv HC; inv Hc. } *)
      (*     { inv Hr. *)
      (*       2: { inv H. } *)
      (*       eapply in_builtin_arg_forall in H6; eauto. *)
      (*       rewrite H6 in HC; inv HC; inv Hc. } *)
      (*     { admit. } *)
      (*     rewrite Forall_forall in H7. *)
      (*     apply H7 in Hr. *)
      (*     destruct Hr as [Hwhite _]. *)
      (*     eapply in_builtin_arg_forall in Hin; eauto. *)
      (*     rewrite Hin in HC; inv HC; inv Hc. *)

      + pose proof H1 as Hcall.
        eapply external_call_Three_Two in H1.
        destruct H1 as (v' & m'' & Hef).
        inv_rs.
        eexists; constructor.
        simpl.
        destruct (is_vote_builtinb_spec ef) as [Hbuiltin|Hbuiltin].
        { inv_wc; try solve [apply vote_not_smove in Hbuiltin; congruence].
          simpl in *.
          destruct vargs.
          { inv H0. }
          destruct vargs.
          { inv H0; inv H11. }
          destruct vargs.
          { inv H0; inv H11; inv H12. }
          destruct vargs.
          2: { inv H0; inv H11; inv H12; inv H13. }
          inv H0.
          inv H11.
          inv H12.
          inv H13.

          
          
          eval_builtin_args
          eapply exec_Ibuiltin.
          { eauto. }
          
        
        eapply exec_Ibuiltin; eauto; simpl.
        * unfold match_rs in RS.
          eapply rs_eq_eval_builtin_args; eauto.
          apply Forall_forall; intros r Hr.
          apply in_builtin_arg_rs_eq.
          intros x Hin; apply RS.
          intro HC.
          inv_wc.
          { inv Hr.
            2: { inv H. }
            eapply in_builtin_arg_forall in H6; eauto.
            rewrite H6 in HC; inv HC; inv Hc. }
          { inv Hr.
            2: { inv H. }
            eapply in_builtin_arg_forall in H6; eauto.
            rewrite H6 in HC; inv HC; inv Hc. }
          rewrite Forall_forall in H7.
          apply H7 in Hr.
          destruct Hr as [Hwhite _].
          eapply in_builtin_arg_forall in Hin; eauto.
          rewrite Hin in HC; inv HC; inv Hc.

      + eexists; constructor.
        eapply exec_Icond; eauto.
        inv_wc.
        erewrite rs_eq_map; eauto.
        apply Forall_forall; intros r Hr.
        rewrite Forall_forall in H2; apply H2 in Hr.
        inv_rs; rewrite RS; auto.
        intro HC; rewrite Hr in HC; inv HC; inv Hc.
      + eexists; constructor.
        eapply exec_Ijumptable; eauto.
        inv_rs; rewrite <- RS; auto.
        inv_wc.
        intro HC; rewrite H3 in HC; inv HC; inv Hc.
      + eexists; constructor.
        eapply exec_Ireturn; eauto.
      + eexists; constructor.
        eapply exec_function_internal; eauto.
      + apply external_call_Three_Two in H.
        destruct H as (v' & m'' & Hef).
        eexists; constructor.
        eapply exec_function_external; eauto.
      + inv STK; inv H1.
        eexists; constructor.
        eapply exec_return.
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
        erewrite rs_eq_map; eauto.
        apply Forall_forall; intros; auto.
      + eapply exec_Iload; eauto.
        erewrite rs_eq_map; eauto.
        apply Forall_forall; intros; auto.
      + eapply exec_Istore; eauto.
        * erewrite rs_eq_map; eauto.
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
        erewrite rs_eq_map; eauto.
        apply Forall_forall; intros; auto.
      + eapply exec_Ijumptable; eauto.
        rewrite <- RS; assumption.
      + eapply exec_Ireturn; eauto.
      + eapply exec_function_internal; eauto.
      + eapply exec_function_external; eauto.
      + apply exec_return.
  Qed.

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
        eapply exec_Inop; eauto.
      + econstructor; eauto.
        inv WC_FUN.
        apply wc_fn_code in H; inv H.
        unfold match_rs in *.
        destruct VT; simpl in *; auto.
        inv_rs; exists c; split; auto.

    (* exec_Iop *)
    - inv Hmatch.
      
      specialize (Hsafe _ (star_refl _ _ _)).
      destruct Hsafe as [[r Hfin] | (t & s'' & Hstep)].
      { inv Hfin. }

      inv Hstep; try congruence.
      eexists; split.
      { apply plus_one.
        eapply exec_Iop; eauto. }
      rewrite H in H9; inv H9.
      econstructor; eauto.
      + intro r.
        destruct (peq r res0); subst.
        * rewrite 2!Regmap.gss.
          eapply eval_operation_val_compat; eauto.
        * rewrite 2!Regmap.gso; auto.
      + unfold match_rs in *.
        destruct VT; simpl in *.
        * inv_rs; exists c; split; auto.
          intros r Hr.
          destruct (peq r res0); subst.
          { rewrite 2!Regmap.gss.
            erewrite rs_eq_map in H10.
            2: { apply Forall_forall; intros r Hin.
                 apply RS.
                 inv_wc.
                 - (* Safe op (replicated) *)
                   intro HC; apply Hr.
                   rewrite Forall_forall in H7.
                   apply H7 in Hin.
                   rewrite <- Hin; auto.
                 - (* Unsafe op (voted) *)
                   rewrite Forall_forall in H6; apply H6 in Hin.
                   destruct Hin as [Hwhite _]; rewrite Hwhite.
                   intro HC; inv HC; inv Hc. }
            rewrite H0 in H10; inv H10; reflexivity. }
          rewrite 2!PMap.gso; auto.
          inv_wc.
          { apply RS; intro HC; apply H8 in HC; congruence. }
          { apply RS; intro HC.
            destruct (in_dec peq r args0).
            - rewrite Forall_forall in H6.
              apply H6 in i.
              destruct i as [Hwhite _].
              rewrite Hwhite in HC; inv HC; inv Hc.
            - apply Hr, H8; auto. }
        * intro r.
          destruct (peq r res0); subst.
          { rewrite 2!Regmap.gss.
            erewrite rs_eq_map in H10; eauto.
            2: { apply Forall_forall; intros r Hin; apply RS. }
            rewrite H0 in H10; inv H10; reflexivity. }
          rewrite 2!Regmap.gso; auto.
      
    (* exec_Iload *)
    - inv Hmatch.
      
      specialize (Hsafe _ (star_refl _ _ _)).
      destruct Hsafe as [[r Hfin] | (t & s'' & Hstep)].
      { inv Hfin. }

      inv Hstep; try congruence.
      eexists; split.
      { apply plus_one.
        eapply exec_Iload; eauto. }
      rewrite H in H10; inv H10.
      econstructor; eauto.
      + intro r.
        destruct (peq r dst0); subst.
        * rewrite 2!Regmap.gss.
          erewrite rs_eq_map in H11.
          2: { apply Forall_forall; intros r Hin.
               unfold match_rs in RS.
               destruct VT; simpl in RS.
               - inv_rs; apply RS.
                 inv_wc.
                 rewrite Forall_forall in H5; apply H5 in Hin.
                 destruct Hin as [Hwhite _].
                 rewrite Hwhite; intro HC; inv HC; inv Hc.
               - apply RS. }
          simpl in H11; rewrite H0 in H11; inv H11.
          rewrite H1 in H12; inv H12.
          apply val_compat_refl.
        * rewrite 2!Regmap.gso; auto.
      + unfold match_rs in *.
        destruct VT; simpl in *.
        * inv_rs; exists c; split; auto.
          intros r Hr.
          destruct (peq r dst0); subst.
          { rewrite 2!Regmap.gss.
            erewrite rs_eq_map in H11.
            2: { apply Forall_forall; intros r Hin.
                 apply RS.
                 inv_wc.
                 rewrite Forall_forall in H5; apply H5 in Hin.
                 destruct Hin as [Hwhite _]; rewrite Hwhite.
                 intro HC; inv HC; inv Hc. }
            rewrite H0 in H11; inv H11.
            rewrite H1 in H12; inv H12; reflexivity. }
          rewrite 2!PMap.gso; auto.
          inv_wc.
          apply RS; intro HC.
          destruct (in_dec peq r args0).
          { rewrite Forall_forall in H5.
            apply H5 in i.
            destruct i as [Hwhite _].
            rewrite Hwhite in HC; inv HC; inv Hc. }
          apply Hr, H9; auto.
        * intro r.
          destruct (peq r dst0); subst.
          { rewrite 2!Regmap.gss.
            erewrite rs_eq_map in H11; eauto.
            2: { apply Forall_forall; intros r Hin; apply RS. }
            rewrite H0 in H11; inv H11.
            rewrite H1 in H12; inv H12; reflexivity. }
          rewrite 2!Regmap.gso; auto.

    (* exec_Istore *)
    - inv Hmatch.
      
      specialize (Hsafe _ (star_refl _ _ _)).
      destruct Hsafe as [[r Hfin] | (t & s'' & Hstep)].
      { inv Hfin. }

      inv Hstep; try congruence.
      eexists; split.
      { apply plus_one.
        eapply exec_Istore; eauto. }
      rewrite H in H10; inv H10.

      replace m'0 with m'.
      2: { erewrite rs_eq_map in H11; eauto.
           2: { apply Forall_forall; intros r Hin.
                destruct VT; simpl in *.
                2: { auto. }
                inv_rs; apply RS; intro HC.
                inv_wc.
                rewrite Forall_forall in H9.
                apply H9 in Hin.
                destruct Hin as [Hwhite _].
                rewrite Hwhite in HC; inv HC; inv Hc. }
           simpl in H11; rewrite H0 in H11; inv H11.
           replace (rs1 # src0) with (rs # src0) in H12.
           2: { destruct VT; simpl in *.
                2: { auto. }
                inv_rs; inv_wc.
                rewrite RS; auto.
                intro HC; rewrite H6 in HC; inv HC; inv Hc. }
           rewrite H1 in H12; inv H12; reflexivity. }
      econstructor; eauto.
      unfold match_rs in *.
      destruct VT; simpl in *; auto.
      inv_rs; exists c; split; auto.
      intros r Hr.
      inv_wc.
      apply RS; intro HC.
      destruct (peq r src0); subst.
      { rewrite H6 in HC; inv HC; inv Hc. }
      destruct (in_dec peq r args0).
      { rewrite Forall_forall in H9; apply H9 in i.
        destruct i as [Hwhite _].
        rewrite Hwhite in HC; inv HC; inv Hc. }
      apply Hr, H10; auto.

    (* exec_Icall *)
    - admit.
    (* exec_Itailcall *)
    - admit.

    (* exec_Ibuiltin *)
    - inv Hmatch.
      
      specialize (Hsafe _ (star_refl _ _ _)).
      destruct Hsafe as [[r Hfin] | (t' & s'' & Hstep)].
      { inv Hfin. }

      inv Hstep; try congruence.

      rewrite H in H10; inv H10.
      replace vargs0 with vargs in *.
      2: { admit. }

      destruct VT; simpl in *.
      inv_rs.
      
      eexists; split.
      { apply plus_one.
        eapply exec_Ibuiltin; eauto.
        apply H1.
        eauto.
        admit.
        
      rewrite H in H10; inv H10.


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
