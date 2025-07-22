Require Import
  AST
  Builtins2
  Coqlib
  Errors
  Events
  Integers
  Maps
  Op
  Ordered
  Registers
  RTL
  RTLgen
  RTLtyping
  Liveness
  Replicate
  Values
.
Import ListNotations.

(* Inductive step: state -> trace -> state -> Prop := *)

(* Lemma vundef_arg_stuck ge (s s' : RTL.state) (t : trace) pc : *)  
(* ~ RTL.step ge s t s'. *)

Section stuck.
  Variable ge : genv.

  Lemma eval_addressing_vundef sp addr rs args :
    Exists (fun arg => rs # arg = Vundef) args ->
    eval_addressing ge sp addr rs ## args = None \/
      eval_addressing ge sp addr rs ## args = Some Vundef.
  Proof.
    intro Hargs.
    unfold eval_addressing.
    destruct Archi.ptr64.
    - unfold eval_addressing64.
      destruct addr; auto; repeat (destruct args; simpl; auto).
      + inv Hargs; auto.
        2: { inv H0. }
        unfold Val.addl.
        rewrite H0.
        right; reflexivity.
      + inv Hargs.
        { unfold Val.addl; rewrite H0; auto. }
        inv H0.
        { unfold Val.addl; rewrite H1; simpl.
          destruct (rs # p); auto. }
        inv H1.
      + inv Hargs.
        { unfold Val.addl; rewrite H0; simpl; auto. }
        inv H0.
      + inv Hargs.
        { unfold Val.addl; rewrite H0; auto. }
        inv H0.
        { unfold Val.addl; rewrite H1; simpl.
          destruct (rs # p); auto. }
        inv H1.
      + inv Hargs.
      + inv Hargs.
    - unfold eval_addressing32.
      destruct addr; repeat (destruct args; simpl; auto).
      + inv Hargs; auto.
        2: { inv H0. }
        unfold Val.addl.
        rewrite H0.
        right; reflexivity.
      + inv Hargs.
        { unfold Val.addl; rewrite H0; auto. }
        inv H0.
        { unfold Val.addl; rewrite H1; simpl.
          destruct (rs # p); auto. }
        inv H1.
      + inv Hargs.
        { unfold Val.addl; rewrite H0; simpl; auto. }
        inv H0.
      + repeat (destruct args; simpl; auto).
        inv Hargs.
        { unfold Val.addl; rewrite H0; auto. }
        inv H0.
        { unfold Val.addl; rewrite H1; simpl.
          destruct (rs # p); auto. }
        inv H1.
  Qed.
        
  Lemma vundef_iload_stuck stk sp rs m f pc chunk addr args dst pc' t s' :
    (fn_code f)!pc = Some (Iload chunk addr args dst pc') ->
    Exists (fun arg => rs # arg = Vundef) args ->
    step ge (State stk f sp pc rs m) t s' ->
    False.
  Proof.
    intros Hpc Hargs Hstep.
    inv Hstep; try congruence.
    rewrite Hpc in H7; inv H7.
    eapply eval_addressing_vundef in Hargs.
    destruct Hargs as [Heval | Heval].
    { rewrite Heval in H8; discriminate. }
    rewrite Heval in H8; inv H8.
    inv H9.
  Qed.
  
  Lemma vundef_istore_stuck stk sp rs m f pc chunk addr args src pc' t s' :
    (fn_code f)!pc = Some (Istore chunk addr args src pc') ->
    Exists (fun arg => rs # arg = Vundef) args \/ rs # src = Vundef ->
    step ge (State stk f sp pc rs m) t s' ->
    False.
  Proof.
    intros Hpc [Hargs | Hsrc] Hstep; inv Hstep; try congruence;
      rewrite Hpc in H7; inv H7.
    - eapply eval_addressing_vundef in Hargs.
      destruct Hargs as [Heval | Heval].
      { rewrite Heval in H8; discriminate. }
      rewrite Heval in H8; inv H8.
      inv H9.
    - unfold Memory.Mem.storev in H9.
      destruct a; try congruence.
      (* STUCK *)
  Abort.

  Lemma vundef_function_internal_stuck s f args m t s'  :
    Exists (eq Vundef) args ->
    step ge (Callstate s (Internal f) args m) t s' ->
    False.
  Proof.
    intros Hargs Hstep; inv Hstep.
    (* STUCK *)
  Admitted.

  Lemma vundef_function_external_stuck s ef args m t s'  :
    Exists (eq Vundef) args ->
    step ge (Callstate s (External ef) args m) t s' ->
    False.
  Proof.
    intros Hargs Hstep; inv Hstep.
    destruct (external_call_spec ef).
    eapply ec_undef.
    2: { eauto. }
    auto.
  Qed.

  Lemma vundef_icall_stuck stk sp rs m f pc sig ros args res pc' t s' t' s'' :
    (fn_code f)!pc = Some (Icall sig ros args res pc') ->
    (Exists (fun arg => rs # arg = Vundef) args \/
       exists r, ros = inl r /\ rs # r = Vundef) ->
    step ge (State stk f sp pc rs m) t s' ->
    step ge s' t' s'' ->
    False.
  Proof.
    intros Hpc [Hargs | [r Hros]] Hstep1 Hstep2; inv Hstep1; try congruence;
      rewrite Hpc in H7; inv H7.
    - destruct fd.
      + eapply vundef_function_internal_stuck.
        2: { eauto. }
        apply Exists_map.
        eapply Exists_impl; eauto.
        intros; simpl; auto.
      + eapply vundef_function_external_stuck.
        2: { eauto. }
        apply Exists_map.
        eapply Exists_impl; eauto.
        intros; simpl; auto.
    - destruct Hros as [? Hr]; subst.
      simpl in H8.
      unfold Globalenvs.Genv.find_funct in H8.
      rewrite Hr in H8; discriminate.
  Qed.

  Lemma vundef_itailcall_stuck stk sp rs m f pc sig ros args t s' t' s'' :
    (fn_code f)!pc = Some (Itailcall sig ros args) ->
    (Exists (fun arg => rs # arg = Vundef) args \/
       exists r, ros = inl r /\ rs # r = Vundef) ->
    step ge (State stk f sp pc rs m) t s' ->
    step ge s' t' s'' ->
    False.
  Proof.
    intros Hpc [Hargs | [r Hros]] Hstep1 Hstep2; inv Hstep1; try congruence;
      rewrite Hpc in H7; inv H7.
    - inv Hstep2.
      + admit.
        (* wt_function *)
        (* Val.has_argtype_list *)
      + destruct (external_call_spec ef).
        eapply ec_undef.
        2: { eauto. }
        apply Exists_map.
        eapply Exists_impl; eauto.
        intros; simpl; auto.        
    - destruct Hros as [? Hr]; subst.
      simpl in H8.
      unfold Globalenvs.Genv.find_funct in H8.
      rewrite Hr in H8; discriminate.
  Admitted.

  Inductive builtin_arg_vundef (rs : regset) : builtin_arg reg -> Prop :=
  | builtin_arg_vundef_BA : forall r,
      rs # r = Vundef ->
      builtin_arg_vundef rs (BA r)
  | builtin_arg_vundef_splitlong_hi : forall hi lo,
      builtin_arg_vundef rs hi ->
      builtin_arg_vundef rs (BA_splitlong hi lo)
  | builtin_arg_vundef_splitlong_lo : forall hi lo,
      builtin_arg_vundef rs lo ->
      builtin_arg_vundef rs (BA_splitlong hi lo)
  | builtin_arg_vundef_addptr_1 : forall a1 a2,
      builtin_arg_vundef rs a1 ->
      builtin_arg_vundef rs (BA_addptr a1 a2)
  | builtin_arg_vundef_addptr_2 : forall a1 a2,
      builtin_arg_vundef rs a2 ->
      builtin_arg_vundef rs (BA_addptr a1 a2).

  Lemma eval_builtin_arg_vundef rs sp m a b :
    eval_builtin_arg (Globalenvs.Genv.to_senv ge) (fun r => rs # r) sp m a b ->
    builtin_arg_vundef rs a ->
    b = Vundef.
  Proof.
    revert b; induction a; intros b Heval Hundef; inv Hundef; inv Heval; auto.
    - apply IHa1 in H2; auto.
      rewrite H2; reflexivity.
    - apply IHa2 in H4; auto.
      rewrite H4.
      unfold Val.longofwords.
      destruct vhi; reflexivity.
    - destruct Archi.ptr64.
      + admit.
      + admit.
    - destruct Archi.ptr64.
      + admit.
      + admit.
  Admitted.

  Lemma eval_builtin_args_vundef rs args vargs sp m :
    Exists (fun arg => builtin_arg_vundef rs arg) args ->
    eval_builtin_args (Globalenvs.Genv.to_senv ge) (fun r => rs # r) sp m
      args vargs ->
    Exists (eq Vundef) vargs.
  Proof.
    revert vargs; induction args; intros vargs Hargs Heval.
    { inv Hargs. }
    inv Heval.
    inv Hargs.
    - left; symmetry.
      eapply eval_builtin_arg_vundef; eauto.
    - right.
      apply IHargs; auto.
  Qed.

  Lemma vundef_ibuiltin_stuck stk sp rs m f pc ef args res pc' t s' :
    (fn_code f)!pc = Some (Ibuiltin ef args res pc') ->
    Exists (fun arg => builtin_arg_vundef rs arg) args ->
    step ge (State stk f sp pc rs m) t s' ->
    False.
  Proof.
    intros Hpc Hargs Hstep; inv Hstep; try congruence;
      rewrite Hpc in H7; inv H7.
    destruct (external_call_spec ef0).
    eapply ec_undef.
    2: { eauto. }
    eapply eval_builtin_args_vundef; eauto.
  Qed.

  Lemma vundef_icond_stuck stk sp rs m f pc cond args ifso ifnot t s' :
    (fn_code f)!pc = Some (Icond cond args ifso ifnot) ->
    Exists (fun arg => rs # arg = Vundef) args ->
    step ge (State stk f sp pc rs m) t s' ->
    False.
  Proof.
    intros Hpc Hargs Hstep; inv Hstep; try congruence;
      rewrite Hpc in H7; inv H7.
    unfold eval_condition in H8.
    destruct cond0; simpl; repeat (destruct args0; simpl in *; try discriminate);
      inv Hargs; try (rewrite H0 in H8; inv H8); inv H0; try solve [inv H1];
      rewrite H1 in H8; destruct (rs # r); discriminate.
  Qed.

  Lemma vundef_ijumptable_stuck stk sp rs m f pc arg tbl t s' :
    (fn_code f)!pc = Some (Ijumptable arg tbl) ->
    rs # arg = Vundef ->
    step ge (State stk f sp pc rs m) t s' ->
    False.
  Proof. intros Hpc Hargs Hstep; inv Hstep; try congruence. Qed.

  Lemma vundef_ireturn_stuck stk sp rs m f pc r t s' :
    (fn_code f)!pc = Some (Ireturn (Some r)) ->
    rs # r = Vundef ->
    step ge (State stk f sp pc rs m) t s' ->
    False.
  Proof.
    intros Hpc Hargs Hstep; inv Hstep; try congruence.
    rewrite Hpc in H7; inv H7.
    (* STUCK *)
  Abort.

  (* Lemma vundef_ireturn_stuck stk sp rs m f pc r t s' t' s'' : *)
  (*   (fn_code f)!pc = Some (Ireturn (Some r)) -> *)
  (*   rs # r = Vundef -> *)
  (*   step ge (State stk f sp pc rs m) t s' -> *)
  (*   step ge s' t' s'' -> *)
  (*   False. *)
  (* Proof. *)
  (*   intros Hpc Hargs Hstep1 Hstep2; inv Hstep1; try congruence. *)
  (*   rewrite Hpc in H7; inv H7. *)
  (*   inv Hstep2. *)
  
End stuck.

Search Regset.empty.
