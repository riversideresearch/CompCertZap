(** Simulation diagram proof for TMR transformation pass. *)

Require Import
  AST
  Coqlib
  Errors
  Events
  Floats
  Globalenvs
  Integers
  Linking
  Maps
  Op
  Registers
  Replicate
  Replicatespec
  RTLgen
  RTLtyping
  Smallstep
  Values
.
Require Import RTL.
Require Import Replicate.
Require Import Errors.
Import ListNotations.

Local Open Scope positive_scope.

Definition match_prog (prog tprog: program) :=
  match_program (fun cu f tf => transf_fundef f = OK tf) eq prog tprog.

Lemma transf_program_match:
  forall prog tprog, transf_program prog = OK tprog -> match_prog prog tprog.
Proof.
  intros. eapply match_transform_partial_program_contextual; eauto.
Qed.

Section PRESERVATION.
  Variable prog: program.
  Variable tprog: program.
  Hypothesis TRANSF: match_prog prog tprog.
  Let ge := Genv.globalenv prog.
  Let tge := Genv.globalenv tprog.

  Lemma symbols_preserved (s : ident) :
    Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof. apply (Genv.find_symbol_match TRANSF). Qed.

  Lemma senv_preserved : Senv.equiv ge tge.
  Proof. apply (Genv.senv_match TRANSF). Qed.

  Lemma functions_translated (v : val) (f : fundef) :
    Genv.find_funct ge v = Some f ->
    exists cu tf,
      Genv.find_funct tge v = Some tf
      /\ transf_fundef f = OK tf
      /\ linkorder cu prog.
  Proof. apply (Genv.find_funct_match TRANSF). Qed.

  Lemma function_ptr_translated (b : block) (f : fundef) :
    Genv.find_funct_ptr ge b = Some f ->
    exists cu tf,
      Genv.find_funct_ptr tge b = Some tf
      /\ transf_fundef f = OK tf
      /\ linkorder cu prog.
  Proof. apply (Genv.find_funct_ptr_match TRANSF). Qed.

  Lemma sig_function_translated f tf :
    transf_fundef f = OK tf ->
    funsig tf = funsig f.
  Proof.
    destruct f as [f|f]; intro Heq; monadInv Heq; auto.
    monadInv EQ.
    unfold transf_fun' in EQ1.
    destruct (transf_fun x0 f _); inv EQ1; auto.
  Qed.

  Lemma stacksize_translated f tf :
    transf_function f = OK tf -> tf.(fn_stacksize) = f.(fn_stacksize).
  Proof.
    unfold transf_function; intro H; monadInv H.
    unfold transf_fun' in EQ0.
    destruct (transf_fun _ _ _); inv EQ0; reflexivity.
  Qed.

  Lemma rm_wf_neq_2_3 (rm : PMap.t (reg * reg)) (l : list positive) (r1 r2 r3 : reg) :
    rm_wf rm l ->
    In r1 l ->
    PMap.get r1 rm = (r2, r3) ->
    r2 <> r3.
  Proof.
    intros Hwf Hn H ?; subst.
    specialize (Hwf r1 r3 r3 Hn H).
    destruct Hwf as [Hnodup Hwf].
    inv Hnodup; inv H3; apply H4; left; reflexivity.
  Qed.

  Lemma rm_wf_neq_1_2 (rm : PMap.t (reg * reg)) l (r1 r2 r3 : reg) :
    rm_wf rm l ->
    In r1 l ->
    PMap.get r1 rm = (r2, r3) ->
    r1 <> r2.
  Proof.
    intros Hwf Hn H ?; subst.
    specialize (Hwf r2 r2 r3 Hn H).
    destruct Hwf as [Hnodup Hwf].
    inv Hnodup; apply H2; left; reflexivity.
  Qed.

  Lemma rm_wf_neq_1_3 (rm : PMap.t (reg * reg)) l (r1 r2 r3 : reg) :
    rm_wf rm l ->
    In r1 l ->
    PMap.get r1 rm = (r2, r3) ->
    r1 <> r3.
  Proof.
    intros Hwf Hn H ?; subst.
    specialize (Hwf r3 r2 r3 Hn H).
    destruct Hwf as [Hnodup Hwf].
    inv Hnodup; apply H2; right; left; reflexivity.
  Qed.

  Lemma rm_wf_neq_2_2 (rm : PMap.t (reg * reg)) l (r1 r2 r3 r1' r2' r3' : reg) :
    rm_wf rm l ->
    r1 <> r1' ->
    In r1 l ->
    In r1' l ->
    PMap.get r1 rm = (r2, r3) ->
    PMap.get r1' rm = (r2', r3') ->
    r2' <> r2.
  Proof.
    intros Hwf Hneq Hn Hn' Hr1 Hr1' ?; subst.
    specialize (Hwf r1 r2 r3 Hn Hr1).
    destruct Hwf as [Hnodup Hwf].
    specialize (Hwf r1' r2 r3' Hn' Hneq Hr1').
    inv Hwf; inv H2; apply H3; right; right; left; reflexivity.
  Qed.

  Lemma rm_wf_neq_2_3' (rm : PMap.t (reg * reg)) l (r1 r2 r3 r1' r2' r3' : reg) :
    rm_wf rm l ->
    In r1 l ->
    In r1' l ->
    PMap.get r1 rm = (r2, r3) ->
    PMap.get r1' rm = (r2', r3') ->
    r2' <> r3.
  Proof.
    intros Hwf Hn Hn' Hr1 Hr1' ?; subst.
    destruct (DecidableTypeEx.Positive_as_DT.eq_dec r1 r1'); subst.
    - rewrite Hr1 in Hr1'; inv Hr1'.
      eapply rm_wf_neq_2_3; eauto.
    - specialize (Hwf r1 r2 r3 Hn Hr1).
      destruct Hwf as [Hnodup Hwf].
      specialize (Hwf r1' r3 r3' Hn' n Hr1').
      inv Hwf; inv H2; inv H4; apply H2; right; left; reflexivity.
  Qed.

  Lemma rm_wf_neq_3_3 (rm : PMap.t (reg * reg)) l (r1 r2 r3 r1' r2' r3' : reg) :
    rm_wf rm l ->
    r1 <> r1' ->
    In r1 l ->
    In r1' l ->
    PMap.get r1 rm = (r2, r3) ->
    PMap.get r1' rm = (r2', r3') ->
    r3' <> r3.
  Proof.
    intros Hwf Hneq Hn Hn' Hr1 Hr1' ?; subst.
    specialize (Hwf r1 r2 r3 Hn Hr1).
    destruct Hwf as [Hnodup Hwf].
    specialize (Hwf r1' r2' r3 Hn' Hneq Hr1').
    inv Hwf; inv H2; inv H4; apply H2; right; right; left; reflexivity.
  Qed.

  (* Lemma not_in_app {A : Type} (l1 l2 : list A) (x : A) : *)
  (*   ~ In x l1 -> *)
  (*   ~ In x l2 -> *)
  (*   ~ In x (l1 ++ l2). *)
  (* Proof. *)
  (*   intros Hl1 Hl2 Hin. *)
  (*   apply in_app_or in Hin; destruct Hin; contradiction. *)
  (* Qed. *)

  Lemma replication_map_wf_aux regs acc s rm s' pf :
    Forall (fun r => r < s.(st_nextreg)) regs ->
    foldM
      (fun rm r1 => do r2 <- new_reg; do r3 <- new_reg; ret rm # r1 <- (r2, r3))
      regs acc s = RTLgen.OK rm s' pf ->
    rm_wf rm regs /\
      Forall (fun r1 => forall r2 r3, PMap.get r1 rm = (r2, r3) ->
                                s.(st_nextreg) <= r2 < s'.(st_nextreg) /\
                                s.(st_nextreg) <= r3 < s'.(st_nextreg)) regs.
  Proof.
    revert acc s rm s' pf.
    induction regs; simpl; intros acc s rm s' pf Hall H.
    { split.
      - intros r1 r2 r3 [].
      - constructor. }
    unfold new_reg in H.
    unfold RTLgen.bind in H.
    simpl in H.
    match goal with
    | [ _: match ?X with | RTLgen.Error _ => _ | RTLgen.OK _ _ _ => _ end = _ |- _ ] => destruct X eqn:HX
    end.
    { inv H. }
    inv H.
    inv Hall.
    rename t into rm.
    assert (rm_wf rm regs).
    { eapply IHregs; eauto. }
    assert (Forall
      (fun r1 : positive =>
       forall r2 r3 : reg,
         rm # r1 = (r2, r3) -> st_nextreg s <= r2 < st_nextreg s'0 /\
                                st_nextreg s <= r3 < st_nextreg s'0) regs).
    { eapply IHregs; eauto. }
    clear HX IHregs.
    rewrite Forall_forall in H0.
    rewrite Forall_forall in H2.
    split.
    - intros r1 r2 r3 Hin Hr1.
      inv s0; simpl in *; unfold Ple in *.
      destruct (DecidableTypeEx.Positive_as_DT.eq_dec a r1); subst.
      + clear Hin.
        rewrite PMap.gss in Hr1; inv Hr1.
        split.
        * constructor.
          { intro Hin; inv Hin; try lia.
            inv H6; try lia; inv H7. }
          constructor.
          { intro Hin; inv Hin; try lia; inv H6. }
          constructor.
          { intros []. }
          constructor.
        * intros r1' r2' r3' Hin Hneq Hr1'.
          inv Hin.
          { congruence. }
          rewrite PMap.gso in Hr1'; auto.
          specialize (H0 r1' H6 r2' r3' Hr1').
          constructor.
          { intro Hin; inv Hin; try lia.
            inv H7; try lia.
            inv H8; try congruence.
            inv H7; try lia.
            inv H8; try lia.
            inv H7. }
          constructor.
          { intro Hin; inv Hin; try lia.
            specialize (H2 r1' H6).
            inv pf; simpl in *; unfold Ple in *.
            inv H7; lia. }
          constructor.
          { intro Hin; inv Hin.
            - specialize (H2 (Pos.succ (st_nextreg s'0)) H6); lia.
            - inv H7; try lia.
              inv H8; try lia.
              inv H7. }
          specialize (H r1' r2' r3' H6 Hr1'); intuition.
      + destruct Hin as [? | Hin]; try congruence.
        rewrite PMap.gso in Hr1; auto.
        specialize (H2 r1 Hin).
        split.
        * specialize (H r1 r2 r3 Hin Hr1); intuition.
        * specialize (H r1 r2 r3 Hin Hr1); destruct H as [H H'].
          intros r1' r2' r3' Hin' Hneq Hr1'; try congruence.
          destruct (DecidableTypeEx.Positive_as_DT.eq_dec a r1'); subst.
          { rewrite PMap.gss in Hr1'; inv Hr1'.
            clear Hin' n.
            constructor.
            { intro HC; inv HC.
              { inv H; apply H8; left; reflexivity. }
              inv H6.
              { inv H; apply H8; right; left; reflexivity. }
              inv H7; try contradiction.
              inv H6; try lia.
              inv H7; try lia.
              inv H6. }
            constructor.
            { intro HC; inv HC.
              { inv H; inv H9; apply H7; left; reflexivity. }
              inv H6.
              { specialize (H0 r1 Hin r2 r3 Hr1); lia. }
              inv H7.
              { specialize (H0 r1 Hin (st_nextreg s'0) r3 Hr1); lia. }
              inv H6.
              { specialize (H0 r1 Hin (Pos.succ (st_nextreg s'0)) r3 Hr1); lia. }
              destruct H7. }
            constructor.
            { intro HC; inv HC.
              { specialize (H0 r1 Hin r2 r3 Hr1); lia. }
              inv H6.
              { specialize (H0 r1 Hin r2 (st_nextreg s'0) Hr1); lia. }
              inv H7.
              { specialize (H0 r1 Hin r2 (Pos.succ (st_nextreg s'0)) Hr1); lia. }
              destruct H6. }
            constructor.
            { intro HC; inv HC; try lia.
              inv H6; try lia; destruct H7. }
            constructor.
            { intro HC; inv HC; try lia; destruct H6. }
            constructor; auto; constructor. }
          destruct Hin' as [? | Hin']; try contradiction.
          rewrite PMap.gso in Hr1'; auto.
    - simpl.
      apply Forall_forall; intros r1 Hin r2 r3 Hr1.
      inv s0; simpl in *; unfold Ple in *.
      destruct (DecidableTypeEx.Positive_as_DT.eq_dec a r1); subst.
      { rewrite PMap.gss in Hr1; inv Hr1; lia. }
      inv Hin; try congruence.
      rewrite PMap.gso in Hr1; auto.
      specialize (H0 r1 H6 r2 r3 Hr1); lia.
  Qed.

  Lemma in_elements p s :
    In p (PSet.elements s) <-> PSet.In p s.
  Proof.
    split; intro Hin.
    - apply SetoidList.In_InA with (eqA := eq) in Hin.
      2: { apply Eqsth. }
      apply PSet.elements_2; assumption.
    - apply PSet.elements_1 in Hin.
      apply SetoidList.InA_alt in Hin.
      destruct Hin as [? [? Hin]]; subst; assumption.
  Qed.

  Lemma in_lt_max_reg r s :
    In r (PSet.elements s) ->
    r < max_reg s + 1.
  Proof.
    unfold max_reg. simpl.
    intro Hin.
    apply in_elements in Hin.
    destruct (PSet.max_elt s) eqn:Hmax.
    { eapply PSet.max_elt_2 in Hmax; eauto.
      unfold Plt in Hmax; lia. }
    apply PSet.max_elt_3 in Hmax.
    apply PSet.is_empty_1 in Hmax.
    destruct s; simpl in *.
    compute in Hmax.
    destruct this.
    2: { congruence. }
    inv Hin.
  Qed.

  Lemma replication_map_wf f rm s pf :
    replication_map f (init_state f) = RTLgen.OK rm s pf ->
    rm_wf rm (fun_regs_list f).
  Proof.
    intro H; eapply replication_map_wf_aux; eauto.
    apply Forall_forall; intros r Hin.
    apply in_lt_max_reg; auto.
  Qed.

  Lemma rs_args1_rs'_args2 c rm args1 args2 args3 rs rs' :
    rm_inv c rm rs rs' ->
    Forall (reg_used_in_code c) args1 ->
    match_regs rm args1 args2 args3 ->
    rs ## args1 = rs' ## args2.
  Proof.
    revert args2 args3.
    induction args1; intros args2 args3 Hrm Hall Hmatch.
    - inv Hmatch; auto.
    - inv Hmatch.
      inv Hall.
      simpl; f_equal; eauto.
      specialize (Hrm a H2).
      rewrite H1 in Hrm; intuition.
  Qed.

  Lemma rs_args1_rs'_args3 c rm args1 args2 args3 rs rs' :
    rm_inv c rm rs rs' ->
    Forall (reg_used_in_code c) args1 ->
    match_regs rm args1 args2 args3 ->
    rs ## args1 = rs' ## args3.
  Proof.
    revert args2 args3.
    induction args1; intros args2 args3 Hrm Hall Hmatch.
    - inv Hmatch; auto.
    - inv Hmatch.
      inv Hall.
      simpl; f_equal; eauto.
      specialize (Hrm a H2).
      rewrite H1 in Hrm; intuition.
  Qed.

  Lemma rm_inv_get c rm r rs rs' :
    rm_inv c rm rs rs' ->
    reg_used_in_code c r ->
    rs # r = rs' # r.
  Proof.
    intros Hinv Hused; apply Hinv in Hused.
    destruct (rm # r); intuition.
  Qed.

  Lemma rm_inv_get_2 c rm r1 r2 r3 rs rs' :
    rm_inv c rm rs rs' ->
    reg_used_in_code c r1 ->
    rm # r1 = (r2, r3) ->
    rs # r1 = rs' # r2.
  Proof.
    intros Hinv Hused Hr; apply Hinv in Hused.
    destruct (rm # r1); inv Hr; intuition.
  Qed.

  Lemma rm_inv_get_3 c rm r1 r2 r3 rs rs' :
    rm_inv c rm rs rs' ->
    reg_used_in_code c r1 ->
    rm # r1 = (r2, r3) ->
    rs' # r2 = rs' # r3.
  Proof.
    intros Hinv Hused Hr; apply Hinv in Hused.
    destruct (rm # r1); inv Hr.
    destruct Hused as (H0 & H1 & H2 & H3).
    rewrite <- H1, <- H2; reflexivity.
  Qed.

  Lemma rs_args_rs'_args c rm args rs rs' :
    rm_inv c rm rs rs' ->
    Forall (reg_used_in_code c) args ->
    rs ## args = rs' ## args.
  Proof.
    induction args; intros Hinv Hall.
    - reflexivity.
    - inv Hall.
      simpl; f_equal; auto.
      specialize (Hinv _ H1).
      destruct (rm # a); intuition.
  Qed.

  Lemma genv_symb_add_globals
    p (prog_defs0 : list (ident * globdef fundef unit)) prog_defs x env1 env2 :
    Genv.genv_symb env1 = Genv.genv_symb env2 ->
    Genv.genv_next env1 = Genv.genv_next env2 ->
    list_forall2
      (match_ident_globdef (fun (_ : AST.program fundef unit) (f tf : fundef) =>
                              transf_fundef f = OK tf) eq p)
      prog_defs0 prog_defs ->
    (Genv.genv_symb (Genv.add_globals env1 prog_defs)) ! x =
      (Genv.genv_symb (Genv.add_globals env2 prog_defs0)) ! x.
  Proof.
    revert x prog_defs env1 env2.
    induction prog_defs0; simpl;
      intros x prog_defs env1 env2 Henv1 Henv2 Hall;
      inv Hall; simpl.
    - rewrite Henv1; reflexivity.
    - erewrite IHprog_defs0; eauto.
      + destruct H1, a, b1; simpl in *; subst.
        rewrite Henv1, Henv2; reflexivity.
      + simpl; rewrite Henv2; reflexivity.
  Qed.

  Lemma find_symbol_tge_ge x :
    Genv.find_symbol tge x = Genv.find_symbol ge x.
  Proof.
    unfold ge, tge.
    unfold Genv.find_symbol.
    destruct tprog, prog.
    simpl in *.
    unfold Genv.globalenv.
    simpl.
    destruct TRANSF as (H0 & H1 & H2).
    simpl in *; subst.
    eapply genv_symb_add_globals; eauto.
  Qed.

  Lemma symbol_address_tge_ge x i :
    Genv.symbol_address tge x i = Genv.symbol_address ge x i.
  Proof.
    unfold Genv.symbol_address.
    rewrite find_symbol_tge_ge; reflexivity.
  Qed.

  Lemma rs_map_ext (rs rs' : Regmap.t val) args :
    (forall r, rs # r = rs' # r) ->
    rs ## args = rs' ## args.
  Proof.
    induction args; simpl; intro Heq; auto.
    rewrite IHargs; auto.
    rewrite Heq; reflexivity.
  Qed.

  Lemma rm_inv_eval_addressing c rm sp a rs rs' args v :
    rm_inv c rm rs rs' ->
    Forall (reg_used_in_code c) args ->
    eval_addressing ge sp a rs ## args = Some v ->
    eval_addressing tge sp a rs' ## args = Some v.
  Proof.
    intros Hrm Hall Heval.
    erewrite <- rs_args_rs'_args; eauto.
    erewrite eval_addressing_preserved; eauto.
    apply symbols_preserved.
  Qed.

  Lemma rm_inv_storev c rm a rs rs' v m chunk src :
    rm_inv c rm rs rs' ->
    reg_used_in_code c src ->
    Memory.Mem.storev chunk m a rs # src = Some v ->
    Memory.Mem.storev chunk m a rs' # src = Some v.
  Proof. intros Hinv Hused Hstore; erewrite <- rm_inv_get; eauto. Qed.

  Lemma match_regs_1_2_eval_operation c sp op rm args1 args2 args3 rs rs' m v :
    rm_inv c rm rs rs' ->
    Forall (reg_used_in_code c) args1 ->
    match_regs rm args1 args2 args3 ->
    eval_operation ge sp op rs ## args1 m = Some v ->
    eval_operation tge sp op rs' ## args2 m = Some v.
  Proof.
    intros Hrm Hall Hmatch Hop.
    erewrite <- rs_args1_rs'_args2; eauto.
    erewrite eval_operation_preserved; eauto.
    apply symbols_preserved.
  Qed.

  Lemma match_regs_1_2_eval_addressing c rm sp a rs rs' args1 args2 args3 v :
    rm_inv c rm rs rs' ->
    Forall (reg_used_in_code c) args1 ->
    match_regs rm args1 args2 args3 ->
    eval_addressing ge sp a rs ## args1 = Some v ->
    eval_addressing tge sp a rs' ## args2 = Some v.
  Proof.
    intros Hrm Hall Hmatch Heval.
    erewrite <- rs_args1_rs'_args2; eauto.
    erewrite eval_addressing_preserved; eauto.
    apply symbols_preserved.
  Qed.

  Lemma not_in_regs_set (rs : regset) r regs v :
    ~ In r regs ->
    (rs # r <- v) ## regs = rs ## regs.
  Proof.
    induction regs; simpl; auto; intros Hnotin.
    f_equal; auto; rewrite PMap.gso; auto.
  Qed.

  Lemma match_regs_1_3_eval_operation c sp op rm args1 args2 args3 res2 rs rs' m v :
    rm_inv c rm rs rs' ->
    ~ In res2 args3 ->
    Forall (reg_used_in_code c) args1 ->
    match_regs rm args1 args2 args3 ->
    eval_operation ge sp op rs ## args1 m = Some v ->
    eval_operation tge sp op (rs' # res2 <- v) ## args3 m = Some v.
  Proof.
    intros Hrm Hnotin Hall Hmatch Hop.
    rewrite not_in_regs_set; auto.
    erewrite <- rs_args1_rs'_args3; eauto; auto.
    erewrite eval_operation_preserved; eauto.
    apply symbols_preserved.
  Qed.

  Lemma match_regs_1_3_eval_addressing c sp a rm args1 args2 args3 res2 rs rs' v x :
    rm_inv c rm rs rs' ->
    ~ In res2 args3 ->
    Forall (reg_used_in_code c) args1 ->
    match_regs rm args1 args2 args3 ->
    eval_addressing ge sp a rs ## args1 = Some x ->
    eval_addressing tge sp a (rs' # res2 <- v) ## args3 = Some x.
  Proof.
    intros Hrm Hnotin Hall Hmatch Hop.
    rewrite not_in_regs_set; auto.
    erewrite <- rs_args1_rs'_args3; eauto.
    erewrite eval_addressing_preserved; eauto.
    apply symbols_preserved.
  Qed.

  Lemma regular_eval_operation c sp op rm args res2 res3 rs rs' m v :
    rm_inv c rm rs rs' ->
    ~ In res2 args ->
    ~ In res3 args ->
    Forall (reg_used_in_code c) args ->
    eval_operation ge sp op rs ## args m = Some v ->
    eval_operation tge sp op ((rs' # res2 <- v) # res3 <- v) ## args m = Some v.
  Proof.
    intros Hrm Hnotin2 Hnotin3 Hall Hop.
    rewrite 2!not_in_regs_set; auto.
    erewrite <- rs_args_rs'_args; eauto.
    erewrite eval_operation_preserved; eauto.
    apply symbols_preserved.
  Qed.

  Lemma regular_eval_addressing c sp a rm args res2 res3 rs rs' v x :
    rm_inv c rm rs rs' ->
    ~ In res2 args ->
    ~ In res3 args ->
    Forall (reg_used_in_code c) args ->
    eval_addressing ge sp a rs ## args = Some x ->
    eval_addressing tge sp a ((rs' # res2 <- v) # res3 <- v) ## args = Some x.
  Proof.
    intros Hrm Hnotin2 Hnotin3 Hall Hop.
    rewrite 2!not_in_regs_set; auto.
    eapply rm_inv_eval_addressing; eauto.
  Qed.

  Lemma res2_not_in_args1 rm l args1 res1 res2 res3 :
    In res1 l ->
    Forall (fun r => In r l) args1 ->
    rm_wf rm l ->
    rm # res1 = (res2, res3) ->
    ~ In res2 args1.
  Proof.
    intros Hres1 Hargs1 Hwf H Hres2.
    rewrite Forall_forall in Hargs1.
    apply Hargs1 in Hres2.
    destruct (DecidableTypeEx.Positive_as_DT.eq_dec res1 res2); subst.
    { eapply rm_wf_neq_1_2 in H; eauto. }
    specialize (Hwf res1 res2 res3 Hres1 H).
    destruct Hwf as [Hnodup Hwf].
    destruct (rm # res2) as [r2' r3'] eqn:H'.
    specialize (Hwf res2 r2' r3' Hres2 n H').
    inv Hwf; inv H3.
    apply H4; right; left; reflexivity.
  Qed.

  Lemma res3_not_in_args1 rm l args1 res1 res2 res3 :
    In res1 l ->
    Forall (fun r => In r l) args1 ->
    rm_wf rm l ->
    rm # res1 = (res2, res3) ->
    ~ In res3 args1.
  Proof.
    intros Hres1 Hargs1 Hwf H Hres3.
    rewrite Forall_forall in Hargs1.
    apply Hargs1 in Hres3.
    destruct (DecidableTypeEx.Positive_as_DT.eq_dec res1 res3); subst.
    { eapply rm_wf_neq_1_3 in H; eauto. }
    specialize (Hwf res1 res2 res3 Hres1 H).
    destruct Hwf as [Hnodup Hwf].
    destruct (rm # res3) as [r2' r3'] eqn:H'.
    specialize (Hwf res3 r2' r3' Hres3 n H').
    inv Hwf; inv H3; inv H5.
    apply H3; left; reflexivity.
  Qed.

  Lemma res2_not_in_args3 rm l args3 res1 res2 res3 :
    In res1 l ->
    rm_wf rm l ->
    Forall (fun r3 => exists r1 r2, In r1 l /\ rm # r1 = (r2, r3)) args3 ->
    rm # res1 = (res2, res3) ->
    ~ In res2 args3.
  Proof.
    intros Hres1 Hwf Hargs3 H Hres2.
    rewrite Forall_forall in Hargs3.
    apply Hargs3 in Hres2.
    destruct Hres2 as (r1 & r2 & Hin & Hr1).
    destruct (DecidableTypeEx.Positive_as_DT.eq_dec res1 res3); subst.
    { eapply rm_wf_neq_1_3 in H; eauto. }
    assert (res2 <> res2).
    { eapply rm_wf_neq_2_3'.
      5: { apply H. }
      4: { eauto. }
      eauto. auto. auto. }
    congruence.
  Qed.

  Lemma pset_in_res_fold_right pc op args res pc' l :
    In (pc, Iop op args res pc') l ->
    PSet.In res
      (fold_right (fun (y : positive * instruction) (x : PSet.t) =>
                     PSet.union x (instr_regs (snd y))) PSet.empty
         l).
  Proof.
    revert pc op args res pc'.
    induction l; simpl; intros pc op args res pc' Hin; try contradiction.
    destruct a as [p i]; simpl.
    destruct Hin as [H | Hin].
    - inv H; apply PSet.union_3, PSet.union_3, PSet.singleton_2; reflexivity.
    - apply PSet.union_2; eapply IHl; eauto.
  Qed.

  Lemma in_pset_of_list p l :
    In p l ->
    PSet.In p (PSet_of_list l).
  Proof.
    revert p; induction l; simpl; intros p Hin; try contradiction.
    destruct Hin as [? | Hin]; subst.
    - apply PSet.add_1; reflexivity.
    - apply PSet.add_2, IHl, Hin.
  Qed.

  Lemma reg_used_fold_right p i l r :
    In (p, i) l ->
    reg_used_in_instr r i ->
    PSet.In r
      (fold_right (fun (y : positive * instruction) (x : PSet.t) =>
                     PSet.union x (instr_regs (snd y))) PSet.empty
         l).
  Proof.
    revert p i r.
    induction l; simpl; intros p i r Hin Hused; try contradiction.
    destruct Hin as [? | Hin]; subst.
    - inv Hused; simpl; try destruct fn; apply PSet.union_3;
        try solve [apply PSet.union_3, PSet.singleton_2; reflexivity];
        try solve [apply PSet.union_2, in_pset_of_list; auto].
      + apply PSet.union_2, PSet.add_1; reflexivity.
      + apply PSet.union_2, PSet.add_2, in_pset_of_list; assumption.
      + apply PSet.add_1; reflexivity.
      + apply PSet.add_2, in_pset_of_list; assumption.
      + apply in_pset_of_list; assumption.
      + apply PSet.union_3, in_pset_of_list; assumption.
    - inv Hused; simpl;
        solve [apply PSet.union_2; eapply IHl; eauto; constructor; auto].
  Qed.

  Lemma reg_used_in_code_pset_in_code_regs c r :
    reg_used_in_code c r ->
    PSet.In r (code_regs c).
  Proof.
    intros (p & i & Hget & Hused).
    apply PTree.elements_correct in Hget.
    unfold code_regs.
    rewrite PTree.fold_spec.
    rewrite <- fold_left_rev_right.
    apply in_rev in Hget.
    eapply reg_used_fold_right; eauto.
  Qed.

  Lemma reg_used_in_code_in_elements_code_regs c r :
    reg_used_in_code c r ->
    In r (PSet.elements (code_regs c)).
  Proof.
    intro Hused.
    apply in_elements, reg_used_in_code_pset_in_code_regs; auto.
  Qed.

  Lemma reg_used_in_code_in_fun_regs_list f r :
    reg_used_in_code f.(fn_code) r ->
    In r (fun_regs_list f).
  Proof.
    intro Hused.
    apply in_elements, PSet.union_3, in_elements.
    apply reg_used_in_code_in_elements_code_regs; assumption.
  Qed.

  Lemma match_regs_in_args3_exists_in_args1 rm  args1 args2 args3 r3 :
    match_regs rm args1 args2 args3 ->
    In r3 args3 ->
    exists (r1 : positive) (r2 : reg), In r1 args1 /\ rm # r1 = (r2, r3).
  Proof.
    induction 1; intro Hin.
    { destruct Hin. }
    destruct Hin as [?|Hin]; subst.
    - eexists; eexists; split; eauto; left; reflexivity.
    - apply IHmatch_regs in Hin.
      destruct Hin as (r1' & r2' & Hin&  Hr'); eexists r1', r2'.
      split; auto; right; assumption.
  Qed.

  (* Lemma iop_match_regs_exists_r1 rm c pc pc' op res args1 args2 args3 r : *)
  (*   c ! pc = Some (Iop op args1 res pc') -> *)
  (*   match_regs rm args1 args2 args3 -> *)
  (*   In r args3 -> *)
  (*   exists (r1 : positive) (r2 : reg), In r1 (PSet.elements (code_regs c)) /\ rm # r1 = (r2, r). *)
  (* Proof. *)
  (*   intros Hget Hmatch Hin. *)
  (*   eapply match_regs_in_args3_exists_in_args1 in Hmatch; eauto. *)
  (*   destruct Hmatch as (r1 & r2 & Hin' & Hr1). *)
  (*   exists r1, r2; split; auto. *)
  (*   apply reg_used_in_code_in_elements_code_regs. *)
  (*   eexists; eexists; split; eauto. *)
  (*   constructor; assumption. *)
  (* Qed. *)

  Lemma match_regs_exists_r1 rm c args1 args2 args3 r :
    Forall (reg_used_in_code c) args1 ->
    match_regs rm args1 args2 args3 ->
    In r args3 ->
    exists (r1 : positive) (r2 : reg),
      In r1 (PSet.elements (code_regs c)) /\ rm # r1 = (r2, r).
  Proof.
    intros Hget Hmatch Hin.
    eapply match_regs_in_args3_exists_in_args1 in Hmatch; eauto.
    destruct Hmatch as (r1 & r2 & Hin' & Hr1).
    exists r1, r2; split; auto.
    apply reg_used_in_code_in_elements_code_regs.
    rewrite Forall_forall in Hget; intuition.
  Qed.

  Lemma match_regs_exists_r1' rm f args1 args2 args3 r3 :
    Forall (reg_used_in_code f.(fn_code)) args1 ->
    match_regs rm args1 args2 args3 ->
    In r3 args3 ->
    exists (r1 : positive) (r2 : reg),
      In r1 (fun_regs_list f) /\ rm # r1 = (r2, r3).
  Proof.
    intros Hall Hmatch Hin.
    eapply match_regs_exists_r1 in Hin; eauto.
    destruct Hin as (r1 & r2 & Hin & Hr1).
    exists r1, r2; split; auto.
    apply in_elements.
    apply in_elements in Hin.
    apply PSet.union_3; assumption.
  Qed.

  (* Lemma iload_match_regs_exists_r1 rm c pc chunk addr dst succ args1 args2 args3 r : *)
  (*   c ! pc = Some (Iload chunk addr args1 dst succ) -> *)
  (*   match_regs rm args1 args2 args3 -> *)
  (*   In r args3 -> *)
  (*   exists (r1 : positive) (r2 : reg), In r1 (PSet.elements (code_regs c)) /\ rm # r1 = (r2, r). *)
  (* Proof. *)
  (*   intros Hget Hmatch Hin. *)
  (*   eapply match_regs_in_args3_exists_in_args1 in Hmatch; eauto. *)
  (*   destruct Hmatch as (r1 & r2 & Hin' & Hr1). *)
  (*   exists r1, r2; split; auto. *)
  (*   apply reg_used_in_code_in_elements_code_regs. *)
  (*   eexists; eexists; split; eauto. *)
  (*   constructor; assumption. *)
  (* Qed. *)

  (* Lemma in_args_code_regs c pc op args res pc' r : *)
  (*   c ! pc = Some (Iop op args res pc') -> *)
  (*   In r args -> *)
  (*   In r (PSet.elements (code_regs c)). *)
  (* Proof. *)
  (*   intros Hget Hin. *)
  (*   apply reg_used_in_code_in_elements_code_regs; *)
  (*     eexists; eexists; split; eauto; constructor; auto. *)
  (* Qed. *)

  (* Lemma iop_in_res_code_regs c pc op args res pc' : *)
  (*   c ! pc = Some (Iop op args res pc') -> *)
  (*   In res (PSet.elements (code_regs c)). *)
  (* Proof. *)
  (*   intro Hget. *)
  (*   apply reg_used_in_code_in_elements_code_regs; *)
  (*     eexists; eexists; split; eauto; solve [constructor; auto]. *)
  (* Qed. *)

  (* Lemma iload_in_res_code_regs c pc chunk addr args dst succ : *)
  (*   c ! pc = Some (Iload chunk addr args dst succ) -> *)
  (*   In dst (PSet.elements (code_regs c)). *)
  (* Proof. *)
  (*   intro Hget. *)
  (*   apply reg_used_in_code_in_elements_code_regs; *)
  (*     eexists; eexists; split; eauto; solve [constructor; auto]. *)
  (* Qed. *)

  (* forall r, Val.has_type (rs#r) (env r). *)

  (* Definition is_defined (v : val) : Prop := *)
  (*   match v with *)
  (*   | Vundef => False *)
  (*   | _ => True *)
  (*   end. *)

  (* Lemma int_canon v : *)
  (* Val.has_type v Tint -> *)
  (* is_defined v -> *)
  (* (exists i, v = Vint i) \/ (exists i b, v = Vptr b i). *)
  (* Proof. *)
  (*   intros Hty Hdef. *)
  (*   destruct v; simpl in *; try contradiction. *)
  (*   - left; exists i; reflexivity. *)
  (*   - right; exists i, b; reflexivity. *)
  (* Qed. *)

  (* Lemma int_canon_32 v : *)
  (*   Archi.ptr64 = false -> *)
  (*   Val.has_type v Tint -> *)
  (*   is_defined v -> *)
  (*   (exists i, v = Vint i) \/ (exists b i, v = Vptr b i). *)
  (* Proof. *)
  (*   intros Harchi Hty Hdef. *)
  (*   destruct v; simpl in *; try contradiction. *)
  (*   - left; exists i; reflexivity. *)
  (*   - right; exists b, i; reflexivity. *)
  (* Qed. *)

  (* Lemma int_canon_64 v : *)
  (*   Archi.ptr64 = true -> *)
  (*   Val.has_type v Tint -> *)
  (*   is_defined v -> *)
  (*   exists i, v = Vint i. *)
  (* Proof. *)
  (*   intros Harchi Hty Hdef. *)
  (*   destruct v; simpl in *; try contradiction. *)
  (*   - exists i; reflexivity. *)
  (*   - congruence. *)
  (* Qed. *)

  (* Lemma long_canon_32 v : *)
  (*   Archi.ptr64 = false -> *)
  (*   Val.has_type v Tlong -> *)
  (*   is_defined v -> *)
  (*   exists i, v = Vlong i. *)
  (* Proof. *)
  (*   intros Harchi Hty Hdef. *)
  (*   destruct v; simpl in *; try contradiction. *)
  (*   - exists i; reflexivity. *)
  (*   - congruence. *)
  (* Qed. *)

  (* Lemma long_canon_64 v : *)
  (*   Archi.ptr64 = true -> *)
  (*   Val.has_type v Tlong -> *)
  (*   is_defined v -> *)
  (*   (exists i, v = Vlong i) \/ (exists b i, v = Vptr b i). *)
  (* Proof. *)
  (*   intros Harchi Hty Hdef. *)
  (*   destruct v; simpl in *; try contradiction. *)
  (*   - left; exists i; reflexivity. *)
  (*   - right; exists b, i; reflexivity. *)
  (* Qed. *)

  (* Lemma single_canon v : *)
  (*   Val.has_type v Tsingle -> *)
  (*   is_defined v -> *)
  (*   exists f, v = Vsingle f. *)
  (* Proof. *)
  (*   intros Hty Hdef. *)
  (*   destruct v; simpl in *; try contradiction. *)
  (*   exists f; reflexivity. *)
  (* Qed. *)

  (* Lemma float_canon v : *)
  (*   Val.has_type v Tfloat -> *)
  (*   is_defined v -> *)
  (*   exists f, v = Vfloat f. *)
  (* Proof. *)
  (*   intros Hty Hdef. *)
  (*   destruct v; simpl in *; try contradiction. *)
  (*   exists f; reflexivity. *)
  (* Qed. *)

  (* Lemma eval_condition_not_none ty cond rs r1 r2 m : *)
  (*   eval_condition (comp_of_typ ty cond) rs ## [r1; r2] m <> None. *)
  (* Proof. *)
  (*   intro Hr12. *)
  (*   simpl in *. *)
  (*   rewrite <- Hr2 in Hr12. *)
  (*        destruct ty; simpl in *; try contradiction. *)
  (*        - destruct Archi.ptr64 eqn:Harchi. *)
  (*          + eapply int_canon_64 in Hty; eauto. *)
  (*            destruct Hty as [i Hi]. *)
  (*            rewrite Hi in Hr12. *)
  (*            inv Hr12. *)
  (*          + eapply int_canon_32 in Hty; eauto. *)
  (*            destruct Hty as [[i Hi] | (b & i & Hi)]. *)
  (*            * rewrite Hi in Hr12; inv Hr12. *)
  (*            * rewrite Hi in Hr12. *)
  (*              simpl in Hr12; rewrite Harchi in Hr12. *)
  (*              destruct (eq_block b b) eqn:Hblock; try congruence. *)
  (*              apply Hptr in Hi; rewrite Hi in Hr12; inv Hr12. *)
  (*        - eapply float_canon in Hty; eauto. *)
  (*          destruct Hty as [f Hf]. *)
  (*          rewrite Hf in Hr12. *)
  (*          inv Hr12. *)
  (*        - destruct Archi.ptr64 eqn:Harchi. *)
  (*          + eapply long_canon_64 in Hty; eauto. *)
  (*            destruct Hty as [[i Hi] | (b & i & Hi)]. *)
  (*            * rewrite Hi in Hr12; inv Hr12. *)
  (*            * rewrite Hi in Hr12; simpl in Hr12. *)
  (*              rewrite Harchi in Hr12; simpl in Hr12. *)
  (*              destruct (eq_block b b) eqn:Hblock; try congruence. *)
  (*              apply Hptr in Hi; rewrite Hi in Hr12; inv Hr12. *)
  (*          + eapply long_canon_32 in Hty; eauto. *)
  (*            destruct Hty as [i Hi]. *)
  (*            rewrite Hi in Hr12. *)
  (*            inv Hr12. *)
  (*        - eapply single_canon in Hty; eauto. *)
  (*          destruct Hty as [f Hf]. *)
  (*          rewrite Hf in Hr12. *)
  (*          inv Hr12. } *)

  Lemma maj_voteR_step
    r1 r2 r3 ty pc succ tstk sig params stacksize c entrypoint sp rs m :
    is_actual_type ty ->
    Val.has_type (rs # r1) ty ->
    rs # r1 = rs # r2 ->
    rs # r2 = rs # r3 ->
    maj_voteR c ty r1 r2 r3 pc succ ->
    exists rs', plus step tge
             (State tstk
                    {| fn_sig := sig
                    ; fn_params := params
                    ; fn_stacksize := stacksize
                    ; fn_code := c
                    ; fn_entrypoint := entrypoint |}
                    sp pc rs m) []
             (State tstk
                    {| fn_sig := sig
                    ; fn_params := params
                    ; fn_stacksize := stacksize
                    ; fn_code := c
                    ; fn_entrypoint := entrypoint |}
                    sp succ rs' m) /\ (forall r, rs # r = rs' # r).
  Proof.
    intros Hact Hty Hr2 Hr3 Hmaj; inv Hmaj.
    (* TODO: all four cases are very similar. combine them somehow or
       factor out commonality? *)
    destruct ty; simpl in *; try contradiction; clear H.
    { inv H0.
      eexists; split.
      - econstructor.
        + eapply exec_Ibuiltin with (vargs := [rs # r1; rs # r2; rs # r3]);
            eauto; repeat constructor.
        + apply star_refl.
        + reflexivity.
      - intro r; simpl.
        unfold Builtins2.vote_int.
        rewrite <- Hr3, <- Hr2.
        destruct (DecidableTypeEx.Positive_as_DT.eq_dec r r1); subst.
        2: { rewrite PMap.gso; auto. }
        destruct (rs # r1) eqn:Hr1; simpl; try solve [inv Hty].
        * rewrite PMap.gss; reflexivity.
        * destruct (Int.eq_dec i i); simpl; try congruence.
          rewrite PMap.gss; reflexivity.
        * destruct Archi.ptr64 eqn:Harchi; simpl.
          { inv Hty; congruence. }
          destruct (eq_block _ _); simpl; try congruence.
          destruct (Ptrofs.eq_dec _ _); simpl; try congruence.
          rewrite PMap.gss; reflexivity. }
    { inv H0.
      eexists; split.
      - econstructor.
        + eapply exec_Ibuiltin with (vargs := [rs # r1; rs # r2; rs # r3]);
            eauto; repeat constructor.
        + apply star_refl.
        + reflexivity.
      - intro r; simpl.
        unfold Builtins2.vote_float.
        rewrite <- Hr3, <- Hr2.
        destruct (DecidableTypeEx.Positive_as_DT.eq_dec r r1); subst.
        2: { rewrite PMap.gso; auto. }
        destruct (rs # r1) eqn:Hr1; simpl; try solve [inv Hty].
        * rewrite PMap.gss; reflexivity.
        * destruct (Float.eq_dec f f); simpl; try congruence.
          rewrite PMap.gss; reflexivity. }
    { inv H0.
      eexists; split.
      - econstructor.
        + eapply exec_Ibuiltin with (vargs := [rs # r1; rs # r2; rs # r3]);
            eauto; repeat constructor.
        + apply star_refl.
        + reflexivity.
      - intro r; simpl.
        unfold Builtins2.vote_long.
        rewrite <- Hr3, <- Hr2.
        destruct (DecidableTypeEx.Positive_as_DT.eq_dec r r1); subst.
        2: { rewrite PMap.gso; auto. }
        destruct (rs # r1) eqn:Hr1; simpl; try solve [inv Hty].
        * rewrite PMap.gss; reflexivity.
        * destruct (Int64.eq_dec i i); simpl; try congruence.
          rewrite PMap.gss; reflexivity.
        * destruct Archi.ptr64 eqn:Harchi; simpl.
          2: { inv Hty; congruence. }
          destruct (eq_block _ _); simpl; try congruence.
          destruct (Ptrofs.eq_dec _ _); simpl; try congruence.
          rewrite PMap.gss; reflexivity. }
    { inv H0.
      eexists; split.
      - econstructor.
        + eapply exec_Ibuiltin with (vargs := [rs # r1; rs # r2; rs # r3]);
            eauto; repeat constructor.
        + apply star_refl.
        + reflexivity.
      - intro r; simpl.
        unfold Builtins2.vote_single.
        rewrite <- Hr3, <- Hr2.
        destruct (DecidableTypeEx.Positive_as_DT.eq_dec r r1); subst.
        2: { rewrite PMap.gso; auto. }
        destruct (rs # r1) eqn:Hr1; simpl; try solve [inv Hty].
        * rewrite PMap.gss; reflexivity.
        * destruct (Float32.eq_dec f f); simpl; try congruence.
          rewrite PMap.gss; reflexivity. }
  Qed.

  Lemma maj_vote_regR_star_step
    c re (rm : PMap.t (reg * reg))
    args pc n tstk sig params stacksize entrypoint sp rs m :
    Forall (fun r1 => Val.has_type (rs # r1) (re r1) /\
                     forall r2 r3,
                       rm # r1 = (r2, r3) ->
                       rs # r1 = rs # r2 /\ rs # r2 = rs # r3) args ->
    maj_vote_regsR c re rm args pc n ->
    exists rs', star step tge
             (State tstk
                    {| fn_sig := sig
                    ; fn_params := params
                    ; fn_stacksize := stacksize
                    ; fn_code := c
                    ; fn_entrypoint := entrypoint |}
                    sp pc rs m) Events.E0
             (State tstk
                    {| fn_sig := sig
                    ; fn_params := params
                    ; fn_stacksize := stacksize
                    ; fn_code := c
                    ; fn_entrypoint := entrypoint |}
                    sp n rs' m) /\ (forall r, rs # r = rs' # r).
  Proof.
    revert pc n.
    induction args; intros pc n Hall Hmaj; inv Hmaj.
    { eexists; split.
      - apply star_refl.
      - intro; reflexivity. }
    inv Hall.
    destruct H3 as (Hty & H3); destruct (H3 r2 r3 H1) as [Hr2 Hr3].
    eapply IHargs in H4.
    2: { eauto. }
    destruct H4 as (rs' & H4 & Hrs').
    generalize (Hrs' a); intro Ha.
    eapply maj_voteR_step with (rs:=rs') in H5.
    2: { inv H5; auto. }
    2: { rewrite <- Ha; auto. }
    2: { rewrite <- 2!Hrs'; auto. }
    2: { rewrite <- 2!Hrs'; auto. }
    destruct H5 as (rs'' & H5 & Hr'').
    eexists; split.
    { apply plus_star.
      eapply star_plus_trans.
      { apply H4. }
      2: { reflexivity. }
      apply H5. }
    intro r; rewrite Hrs'; apply Hr''.
  Qed.

  Lemma wt_program_prog :
    wt_program prog.
  Proof.
    intros x fd Hin.
    unfold match_prog, match_program, match_program_gen in TRANSF.
    destruct fd.
    2: { constructor. }
    destruct TRANSF as (H0 & H1 & H2).
    eapply list_forall2_in_left in H0; eauto.
    destruct H0 as ([y gd] & Hy & H3 & H4).
    simpl in *; subst; inv H4.
    simpl in H3; monadInv H3; monadInv EQ.
    apply type_function_correct in EQ0.
    econstructor; eauto.
  Qed.

  Lemma rs_in_singleton (rs : Regmap.t val) args v r :
    rs ## args = [v] ->
    In r args ->
    rs # r = v.
  Proof.
    intros Hargs Hin.
    destruct args; inv Hin.
    - inv Hargs; auto.
    - inv Hargs.
      apply map_eq_nil in H2; subst; inv H.
  Qed.

  Lemma rs_in_l_2 (rs : Regmap.t val) args v1 v2 r :
    rs ## args = [v1; v2] ->
    In r args ->
    rs # r = v1 \/ rs # r = v2.
  Proof.
    intros Hargs Hin.
    destruct args; inv Hin.
    - inv Hargs; auto.
    - inv Hargs.
      right; eapply rs_in_singleton; eauto.
  Qed.

  Lemma wt_stackframes_sig_proper s sig1 sig2 :
    sig_res sig1 = sig_res sig2 ->
    wt_stackframes s sig1 ->
    wt_stackframes s sig2.
  Proof.
    intros Hres Hwt.
    inv Hwt.
    - constructor; rewrite <- Hres; assumption.
    - econstructor; eauto.
      unfold proj_sig_res; rewrite <- Hres; assumption.
  Qed.

  (* Lemma eval_addressing_in_args_vundef sp addr rs a args r : *)
  (*   eval_addressing ge sp addr rs ## args = Some a -> *)
  (*   In r args -> *)
  (*   rs # r = Vundef -> *)
  (*   a = Vundef. *)
  (* Proof. *)
  (*   intros Heval Hin Heq. *)
  (*   eapply eval_addressing_vundef; eauto. *)
  (*   apply in_map_iff. *)
  (*   eexists; split; eauto. *)
  (* Qed. *)

  Lemma rm_inv_ext_r rs0 rs1 rs2 c rm :
    (forall r, rs1 # r = rs2 # r) ->
    rm_inv c rm rs0 rs1 ->
    rm_inv c rm rs0 rs2.
  Proof.
    unfold rm_inv.
    intros Heq Hinv r1 Hused.
    apply Hinv in Hused.
    destruct (rm # r1).
    destruct Hused as (H0 & H1 & H2 & H3 & H4).
    repeat split; auto; rewrite <- Heq; auto.
  Qed.

  (* Lemma find_funct_proper rs rs' r f : *)
  (*   rs # r = rs' # r -> *)
  (*   Genv.find_funct tge rs # r = Some f -> *)
  (*   Genv.find_funct tge rs' # r = Some f. *)
  (* Proof. *)
  (*   unfold Genv.find_funct. *)
  (*   intros Heq Hfind. *)
  (*   rewrite <- Heq. *)
  (*   destruct (rs # r); congruence. *)
  (* Qed. *)

  (* Lemma find_funct_proper rs rs' r f : *)
  (*   (forall r : positive, rs # r = rs' # r) -> *)
  (*   Genv.find_funct tge rs # r = Some f -> *)
  (*   Genv.find_funct tge rs' # r = Some f. *)
  (* Proof. *)
  (*   unfold Genv.find_funct. *)
  (*   intros Heq Hfind. *)
  (*   rewrite <- Heq. *)
  (*   destruct (rs # r); congruence. *)
  (* Qed. *)

  Lemma find_function_proper rs rs' ros f :
    (forall r, ros = inl r -> rs # r = rs' # r) ->
    find_function tge ros rs = Some f ->
    find_function tge ros rs' = Some f.
  Proof.
    unfold find_function.
    intros Heq Hfind.
    destruct ros.
    - rewrite <- Heq; auto.
      (* eapply find_funct_proper; eauto. *)
    - destruct (Genv.find_symbol _ _); congruence.
  Qed.

  (* Lemma find_function_proper rs rs' ros f : *)
  (*   (forall r : positive, rs # r = rs' # r) -> *)
  (*   find_function tge ros rs = Some f -> *)
  (*   find_function tge ros rs' = Some f. *)
  (* Proof. *)
  (*   unfold find_function. *)
  (*   intros Heq Hfind. *)
  (*   destruct ros. *)
  (*   - eapply find_funct_proper; eauto. *)
  (*   - destruct (Genv.find_symbol _ _); congruence. *)
  (* Qed. *)

  (* TODO: put lemmas that are used a lot in a hint database to clean
     up this proof. *)
  Theorem step_simulation s1 t s2 :
    step ge s1 t s2 ->
    forall ts1,
      (* wt_state s1 -> *)
      match_states s1 ts1 ->
      (* exists ts2, plus step tge ts1 t ts2 /\ wt_state s2 /\ match_states s2 ts2. *)
      exists ts2, plus step tge ts1 t ts2 /\ match_states s2 ts2.
  Proof.
    intros Hstep ts1 Hmatch.
    (* assert (Hwt: wt_state s1). *)
    (* { eapply match_states_wt_state; eauto. } *)
    (* assert (Hwt2: wt_state s2). *)
    (* { eapply subject_reduction; eauto. *)
    (*   apply wt_program_prog. } *)

    (* inv Hmatch. *)
    inv Hstep.

    - (* exec_Inop *)
      inv Hmatch.
      inv FUN; simpl in *.
      eexists; split.
      + econstructor.
        * apply exec_Inop; simpl.
          specialize (H0 pc (Inop pc') H).
          inv H0; eauto.
        * apply star_refl.
        * reflexivity.
      + econstructor; eauto.
        econstructor; eauto.

    - (* exec_Iop *)
      inv Hmatch.
      inv FUN; simpl in *.
      set (f := {| fn_sig := sig
                ; fn_params := params
                ; fn_stacksize := stacksize
                ; fn_code := c
                ; fn_entrypoint := entrypoint |}).
      pose proof H1 as Hcode.
      specialize (H1 pc (Iop op args res pc') H); inv H1.
      assert (Hargs: Forall (reg_used_in_code c) args).
      { apply Forall_forall; intros x Hx;
          eexists; eexists; split; eauto; constructor; auto. }
      eexists; split.
      + econstructor.
        * eapply exec_Iop; eauto.
          eapply match_regs_1_2_eval_operation.
          { eauto. }
          2: { eauto. }
          2: { eauto. }
          apply Forall_forall; intros r Hin.
          eexists; eexists; split; eauto.
          constructor; auto.
        * eapply star_step.
          { eapply exec_Iop; eauto.
            eapply match_regs_1_3_eval_operation.
            { eauto. }
            { eapply res2_not_in_args3 with (l := fun_regs_list f); eauto.
              - eapply reg_used_in_code_in_fun_regs_list.
                eexists; eexists; split; eauto; solve [constructor].
              - apply Forall_forall.
                intros r Hin.
                eapply match_regs_exists_r1' with (args1:=args); eauto. }
            2: { eauto. }
            2: { auto. }
            auto. }
          { eapply star_step.
            - eapply exec_Iop; eauto.
              eapply regular_eval_operation; eauto.
              + eapply res2_not_in_args1 with (l := fun_regs_list f); eauto.
                * eapply reg_used_in_code_in_fun_regs_list.
                  eexists; eexists; split; eauto; solve [constructor].
                * apply Forall_forall; intros r Hin.
                  eapply reg_used_in_code_in_fun_regs_list.
                  rewrite Forall_forall in Hargs; intuition.
              + eapply res3_not_in_args1 with (l := fun_regs_list f); eauto.
                * eapply reg_used_in_code_in_fun_regs_list.
                  eexists; eexists; split; eauto; solve [constructor].
                * apply Forall_forall; intros r Hin.
                  eapply reg_used_in_code_in_fun_regs_list.
                  rewrite Forall_forall in Hargs; intuition.
            - apply star_refl.
            - reflexivity. }
          reflexivity.
        * reflexivity.
      + econstructor; eauto.
        { eapply wt_exec_Iop; eauto.
          eapply wt_instr_at; eauto. }
        * constructor; eauto.
        * intros r Hused.
          destruct (rm # r) eqn:Hr.
          destruct (DecidableTypeEx.Positive_as_DT.eq_dec r res); subst.
          { rewrite H8 in Hr; inv Hr.
            repeat split.
            - rewrite 2!PMap.gss; reflexivity.
            - rewrite PMap.gss, PMap.gso.
              2: { symmetry; eapply rm_wf_neq_1_2; eauto.
                   - eapply reg_used_in_code_in_fun_regs_list.
                     eexists; eexists; split; eauto; solve [constructor]. }
              rewrite PMap.gso.
              2: { eapply rm_wf_neq_2_3; eauto.
                   eapply reg_used_in_code_in_fun_regs_list.
                   eexists; eexists; split; eauto; solve [constructor]. }
              rewrite PMap.gss; reflexivity.
            - rewrite PMap.gss, PMap.gso.
              2: { symmetry; eapply rm_wf_neq_1_3; eauto.
                   eapply reg_used_in_code_in_fun_regs_list.
                   eexists; eexists; split; eauto; solve [constructor]. }
              rewrite PMap.gss; reflexivity.
            - specialize (RM _ Hused); rewrite H8 in RM; intuition.
            - specialize (RM _ Hused); rewrite H8 in RM; intuition. }
          { assert (Hresused: reg_used_in_code c res).
            { eexists; eexists; split; eauto; apply reg_used_iop_res. }
            repeat split.
            - rewrite 3!PMap.gso; auto.
              2: { intro HC; subst.
                   specialize (RM _ Hresused).
                   rewrite H8 in RM; intuition. }
              rewrite PMap.gso.
              2: { intro HC; subst.
                   specialize (RM _ Hresused).
                   rewrite H8 in RM; intuition. }
              specialize (RM r Hused).
              rewrite Hr in RM; intuition.
            - rewrite 2!PMap.gso; auto.
              2: { intro HC; subst.
                   specialize (RM _ Hused).
                   rewrite Hr in RM; intuition. }
              rewrite PMap.gso.
              2: { eapply rm_wf_neq_2_3' with (r1 := res); eauto.
                   - eapply reg_used_in_code_in_fun_regs_list.
                     eexists; eexists; split; eauto; solve [constructor].
                   - apply reg_used_in_code_in_fun_regs_list; auto. }
              rewrite PMap.gso.
              2: { eapply rm_wf_neq_2_2 with (r1 := res); eauto.
                   - eapply reg_used_in_code_in_fun_regs_list.
                     eexists; eexists; split; eauto; solve [constructor].
                   - apply reg_used_in_code_in_fun_regs_list; auto. }
              specialize (RM _ Hused); rewrite Hr in RM; intuition.
            - rewrite 2!PMap.gso; auto.
              2: { intro HC; subst.
                   specialize (RM _ Hused).
                   rewrite Hr in RM; intuition. }
              rewrite PMap.gso.
              2: { eapply rm_wf_neq_3_3 with (r1 := res); eauto.
                   - eapply reg_used_in_code_in_fun_regs_list.
                     eexists; eexists; split; eauto; solve [constructor].
                   - apply reg_used_in_code_in_fun_regs_list; auto. }
              rewrite PMap.gso.
              2: { symmetry.
                   eapply rm_wf_neq_2_3' with (r1 := r); eauto;
                     apply reg_used_in_code_in_fun_regs_list; auto. }
              specialize (RM _ Hused); rewrite Hr in RM; intuition.
            - specialize (RM _ Hused); rewrite Hr in RM; intuition.
            - specialize (RM _ Hused); rewrite Hr in RM; intuition. }

    - (* exec_Iload *)
      inv Hmatch.
      inv FUN; simpl in *.
      set (f := {| fn_sig := sig
                ; fn_params := params
                ; fn_stacksize := stacksize
                ; fn_code := c
                ; fn_entrypoint := entrypoint |}).
      pose proof H2 as Hcode.
      specialize (H2 pc (Iload chunk addr args dst pc') H); inv H2.
      assert (Hargs: Forall (reg_used_in_code c) args).
      { apply Forall_forall; intros x Hx;
          eexists; eexists; split; eauto; constructor; auto. }
      eexists; split.
      + econstructor.
        * eapply exec_Iload; eauto.
          eapply match_regs_1_2_eval_addressing.
          { eauto. }
          2: { eauto. }
          2: { eauto. }
          apply Forall_forall; intros r Hin.
          eexists; eexists; split; eauto.
          constructor; auto.
        * eapply star_step.
          { eapply exec_Iload; eauto.
            eapply match_regs_1_3_eval_addressing.
            { eauto. }
            { eapply res2_not_in_args3 with (l := fun_regs_list f); eauto.
              - eapply reg_used_in_code_in_fun_regs_list.
                eexists; eexists; split; eauto; solve [constructor].
              - apply Forall_forall.
                intros r Hin.
                eapply match_regs_exists_r1'; eauto. }
            2: { eauto. }
            2: { auto. }
            apply Forall_forall; intros r Hin.
            eexists; eexists; split; eauto.
            constructor; auto. }
          { eapply star_step.
            - eapply exec_Iload; eauto.
              eapply regular_eval_addressing; eauto.
              + eapply res2_not_in_args1 with (l := fun_regs_list f); eauto.
                * apply reg_used_in_code_in_fun_regs_list;
                    eexists; eexists; split; eauto; solve [constructor].
                * apply Forall_forall; intros r Hin.
                  apply reg_used_in_code_in_fun_regs_list.
                  rewrite Forall_forall in Hargs; intuition.
              + eapply res3_not_in_args1 with (l := fun_regs_list f); eauto.
                * apply reg_used_in_code_in_fun_regs_list;
                    eexists; eexists; split; eauto; solve [constructor].
                * apply Forall_forall; intros r Hin.
                  apply reg_used_in_code_in_fun_regs_list.
                  rewrite Forall_forall in Hargs; intuition.
            - apply star_refl.
            - reflexivity. }
          reflexivity.
        * reflexivity.
      + econstructor; eauto.
        { eapply wt_exec_Iload; eauto.
          eapply wt_instr_at; eauto. }
        * constructor; eauto.
        * intros r Hused.
          destruct (rm # r) eqn:Hr.
          destruct (DecidableTypeEx.Positive_as_DT.eq_dec r dst); subst.
          { rewrite H10 in Hr; inv Hr.
            repeat split.
            - rewrite 2!PMap.gss; reflexivity.
            - rewrite PMap.gss, PMap.gso.
              2: { symmetry; eapply rm_wf_neq_1_2; eauto.
                   - eapply reg_used_in_code_in_fun_regs_list.
                     eexists; eexists; split; eauto; solve [constructor]. }
              rewrite PMap.gso.
              2: { eapply rm_wf_neq_2_3; eauto.
                   - eapply reg_used_in_code_in_fun_regs_list.
                     eexists; eexists; split; eauto; solve [constructor]. }
              rewrite PMap.gss; reflexivity.
            - rewrite PMap.gss, PMap.gso.
              2: { symmetry; eapply rm_wf_neq_1_3; eauto.
                   - eapply reg_used_in_code_in_fun_regs_list.
                     eexists; eexists; split; eauto; solve [constructor]. }
              rewrite PMap.gss; reflexivity.
            - specialize (RM _ Hused); rewrite H10 in RM; intuition.
            - specialize (RM _ Hused); rewrite H10 in RM; intuition. }
          { assert (Hdstused: reg_used_in_code c dst).
            { eexists; eexists; split; eauto; apply reg_used_iload_res. }
            repeat split.
            - rewrite 3!PMap.gso; auto.
              2: { intro HC; subst.
                   specialize (RM _ Hdstused).
                   rewrite H10 in RM; intuition. }
              rewrite PMap.gso.
              2: { intro HC; subst.
                   specialize (RM _ Hdstused).
                   rewrite H10 in RM; intuition. }
              specialize (RM r Hused).
              rewrite Hr in RM; intuition.
            - rewrite 2!PMap.gso; auto.
              2: { intro HC; subst.
                   specialize (RM _ Hused).
                   rewrite Hr in RM; intuition. }
              rewrite PMap.gso.
              2: { eapply rm_wf_neq_2_3' with (r1 := dst); eauto.
                   - eapply reg_used_in_code_in_fun_regs_list.
                     eexists; eexists; split; eauto; solve [constructor].
                   - apply reg_used_in_code_in_fun_regs_list; auto. }
              rewrite PMap.gso.
              2: { eapply rm_wf_neq_2_2 with (r1 := dst); eauto.
                   - eapply reg_used_in_code_in_fun_regs_list.
                     eexists; eexists; split; eauto; solve [constructor].
                   - apply reg_used_in_code_in_fun_regs_list; auto. }
              specialize (RM _ Hused); rewrite Hr in RM; intuition.
            - rewrite 2!PMap.gso; auto.
              2: { intro HC; subst.
                   specialize (RM _ Hused).
                   rewrite Hr in RM; intuition. }
              rewrite PMap.gso.
              2: { eapply rm_wf_neq_3_3 with (r1 := dst); eauto.
                   - eapply reg_used_in_code_in_fun_regs_list.
                     eexists; eexists; split; eauto; solve [constructor].
                   - apply reg_used_in_code_in_fun_regs_list; auto. }
              rewrite PMap.gso.
              2: { symmetry.
                   eapply rm_wf_neq_2_3' with (r1 := r); eauto.
                   - apply reg_used_in_code_in_fun_regs_list; auto.
                   - apply reg_used_in_code_in_fun_regs_list; auto. }
              specialize (RM _ Hused); rewrite Hr in RM; intuition.
            - specialize (RM _ Hused); rewrite Hr in RM; intuition.
            - specialize (RM _ Hused); rewrite Hr in RM; intuition. }

    - (* exec_Istore *)
      inv Hmatch.
      inv FUN; simpl in *.
      set (f := {| fn_sig := sig
                 ; fn_params := params
                 ; fn_stacksize := stacksize
                 ; fn_code := c
                 ; fn_entrypoint := entrypoint |}).
      pose proof H2 as Hcode.
      specialize (H2 pc (Istore chunk addr args src pc') H); inv H2.
      eapply maj_vote_regR_star_step with (m:=m) in H10; eauto.
      2: { apply Forall_forall; intros r1 Hin.
           assert (Hused: reg_used_in_code c r1).
           { eexists; eexists; split; eauto; constructor; assumption. }
           assert (Heq: rs' # r1 = rs # r1).
           { specialize (RM r1 Hused).
             destruct (rm # r1) eqn:Hr1.
             intuition. }
           rewrite Heq; clear Hused Heq.
           split.
           { apply WT_RS. }
           split.
           - eapply rm_inv_get_2; eauto.
             eexists; eexists; split; eauto; constructor; auto.
           - eapply rm_inv_get_3; eauto.
             eexists; eexists; split; eauto; constructor; auto. }
      destruct H10 as (rs'' & H10 & Hrs'').
      eexists; split.
      + eapply star_plus_trans.
        { apply H10. }
        2: { reflexivity. }
        econstructor.
        2: { apply star_refl. }
        2: { rewrite Events.E0_right; reflexivity. }
        eapply exec_Istore; simpl; eauto.
        * erewrite <- rs_map_ext; eauto.
          eapply rm_inv_eval_addressing; eauto.
          apply Forall_forall; intros r Hr; eexists; eexists; split; eauto.
          constructor; auto.
        * rewrite <- Hrs''.
          eapply rm_inv_storev; eauto.
          eexists; eexists; split; eauto; solve [constructor].
      + econstructor; eauto.
        * econstructor; eauto.
        * eapply rm_inv_ext_r; eauto.

    - (* exec_Icall *)
      inv Hmatch.
      pose proof FUN as Hmatch_function.
      inv FUN; simpl in *.
      set (f := {| fn_sig := sig
                ; fn_params := params
                ; fn_stacksize := stacksize
                ; fn_code := c
                ; fn_entrypoint := entrypoint |}).
      pose proof H as Hcode.
      specialize (H1 pc (Icall (funsig fd) ros args res pc') Hcode); inv H1.
      smoveR_inv.
      eapply maj_vote_regR_star_step with (m:=m) in H9; eauto.
      2: { apply Forall_forall; intros r1 Hin.
           assert (Hused: reg_used_in_code c r1).
           { eexists; eexists; split; eauto.
             apply in_app_or in Hin; destruct Hin.
             - destruct ros; simpl in *; inv H6; try contradiction.
               constructor.
             - constructor; auto. }
           assert (Heq: rs' # r1 = rs # r1).
           { specialize (RM r1 Hused).
             destruct (rm # r1) eqn:Hr1.
             intuition. }
           rewrite Heq; clear Heq.
           split.
           { apply WT_RS. }
           split.
           { eapply rm_inv_get_2; eauto. }
           { eapply rm_inv_get_3; eauto. } }
      destruct H9 as (rs'' & H9 & Hrs'').
      assert (Htf: exists tf, transf_fundef fd = OK tf /\
                           find_function tge ros rs = Some tf).
      { unfold find_function in *.
        destruct ros.
        - apply functions_translated in H0.
          destruct H0 as (cu & tf & Hfind & Htrans & Hlink).
          eexists; split; eauto.
        - destruct (Genv.find_symbol ge i) eqn:Hsym; try congruence.
          apply function_ptr_translated in H0.
          destruct H0 as (cu & tf & Hfind & Htrans & Hlink).
          eexists; split; eauto.
          rewrite symbols_preserved, Hsym; auto. }
      destruct Htf as (tf & Htransf_fundef & Hfind_tf).
      eexists; split.
      + eapply star_plus_trans.
        { apply H9. }
        2: { reflexivity. }
        econstructor.
        2: { apply star_refl. }
        2: { rewrite Events.E0_right; reflexivity. }
        eapply exec_Icall; simpl.
        { eauto. }
        { erewrite find_function_proper.
          { eauto. }
          { intros r ?; subst.
            etransitivity.
            2: { rewrite <- Hrs''; reflexivity. }
            eapply rm_inv_get; eauto.
            eexists; eexists; split; eauto; constructor. }
          eauto. }
        { apply sig_function_translated; auto. }
      + erewrite rs_args_rs'_args; eauto.
        2: { apply Forall_forall; intros r' Hr';
             eexists; eexists; split; eauto; constructor; auto. }
        erewrite rs_map_ext; eauto.
        constructor; auto.
        { econstructor; eauto.
          inv WT_FN.
          simpl in *.
          apply wt_instrs in Hcode.
          inv Hcode; auto. }
        { destruct ros.
          - apply Genv.find_funct_inversion in H0.
            destruct H0 as [id H0].
            eapply wt_program_prog; eauto.
          - simpl in H0.
            destruct (Genv.find_symbol ge i); try congruence.
            apply Genv.find_funct_ptr_inversion in H0.
            destruct H0 as [id H0].
            eapply wt_program_prog; eauto. }
        { constructor; auto.
          econstructor; eauto.
          eapply rm_inv_ext_r; eauto. }
        { apply transf_function_match_fundef; auto. }

    - (* exec_Itailcall *)
      inv Hmatch.
      pose proof FUN as Hmatch_function.
      inv FUN; simpl in *.
      set (f := {| fn_sig := sig
                ; fn_params := params
                ; fn_stacksize := stacksize
                ; fn_code := c
                ; fn_entrypoint := entrypoint |}).
      pose proof H as Hcode.
      specialize (H1 pc (Itailcall (funsig fd) ros args) Hcode); inv H1.
      (* inv H6. *)
      eapply maj_vote_regR_star_step with (m:=m) in H6; eauto.
      2: { apply Forall_forall; intros r1 Hin.
           assert (Hused: reg_used_in_code c r1).
           { eexists; eexists; split; eauto.
             apply in_app_or in Hin; destruct Hin.
             - destruct ros; simpl in *; inv H1; try contradiction.
               constructor.
             - constructor; auto. }
           assert (Heq: rs' # r1 = rs # r1).
           { specialize (RM r1 Hused).
             destruct (rm # r1) eqn:Hr1.
             intuition. }
           rewrite Heq; clear Heq.
           split.
           { apply WT_RS. }
           split.
           { eapply rm_inv_get_2; eauto. }
           { eapply rm_inv_get_3; eauto. } }
      destruct H6 as (rs'' & H6 & Hrs'').
      assert (Htf: exists tf, transf_fundef fd = OK tf /\
                           find_function tge ros rs = Some tf).
      { unfold find_function in *.
        destruct ros.
        - apply functions_translated in H0.
          destruct H0 as (cu & tf & Hfind & Htrans & Hlink).
          eexists; split; eauto.
        - destruct (Genv.find_symbol ge i) eqn:Hsym; try congruence.
          apply function_ptr_translated in H0.
          destruct H0 as (cu & tf & Hfind & Htrans & Hlink).
          eexists; split; eauto.
          rewrite symbols_preserved, Hsym; auto. }
      destruct Htf as (tf & Htransf_fundef & Hfind_tf).
      eexists; split.
      + eapply star_plus_trans.
        { apply H6. }
        2: { reflexivity. }
        econstructor.
        2: { apply star_refl. }
        2: { rewrite Events.E0_right; reflexivity. }
        eapply exec_Itailcall; simpl.
        { eauto. }
        { erewrite find_function_proper.
          { eauto. }
          { intros r ?; subst.
            etransitivity.
            2: { rewrite <- Hrs''; reflexivity. }
            eapply rm_inv_get; eauto.
            eexists; eexists; split; eauto; constructor. }
          eauto. }
        { apply sig_function_translated; auto. }
        { eauto. }
      + erewrite rs_args_rs'_args; eauto.
        2: { apply Forall_forall; intros r' Hr';
             eexists; eexists; split; eauto; constructor; auto. }
        erewrite rs_map_ext; eauto.
        constructor; auto.
        { inv WT_FN. simpl in *.
          specialize (wt_instrs pc _ Hcode).
          inv wt_instrs.
          simpl in *.
          eapply wt_stackframes_sig_proper.
          { rewrite <- H10; reflexivity. }
          auto. }
        { destruct ros.
          - apply Genv.find_funct_inversion in H0.
            destruct H0 as [id H0].
            eapply wt_program_prog; eauto.
          - simpl in H0.
            destruct (Genv.find_symbol ge i); try congruence.
            apply Genv.find_funct_ptr_inversion in H0.
            destruct H0 as [id H0].
            eapply wt_program_prog; eauto. }
        { apply transf_function_match_fundef; auto. }

    - (* exec_Ibuiltin *)      
      inv Hmatch.
      pose proof FUN as Hmatch_function.
      inv FUN; simpl in *.
      set (f := {| fn_sig := sig
                ; fn_params := params
                ; fn_stacksize := stacksize
                ; fn_code := c
                ; fn_entrypoint := entrypoint |}).
      pose proof H as Hcode.
      specialize (H2 pc (Ibuiltin ef args res pc') Hcode); inv H2.
      smoveR_inv.
      eapply maj_vote_regR_star_step with (m:=m) in H7; eauto.
      2: { apply Forall_forall; intros r1 Hin.
           assert (Hused: reg_used_in_code c r1).
           { eexists; eexists; split; eauto; constructor; auto. }
             (* reg_used_in_instr *)
             (* apply in_app_or in Hin; destruct Hin. *)
             (* - destruct ros; simpl in *; inv H6; try contradiction. *)
             (*   constructor. *)
             (* - constructor; auto. } *)
           assert (Heq: rs' # r1 = rs # r1).
           { specialize (RM r1 Hused).
             destruct (rm # r1) eqn:Hr1.
             intuition. }
           rewrite Heq; clear Heq.
           split.
           { apply WT_RS. }
           split.
           { eapply rm_inv_get_2; eauto. }
           { eapply rm_inv_get_3; eauto. } }
      destruct H7 as (rs'' & H7 & Hrs'').
      (* assert (Htf: exists tf, transf_fundef fd = OK tf /\ *)
      (*                      find_function tge ros rs = Some tf). *)
      (* { unfold find_function in *. *)
      (*   destruct ros. *)
      (*   - apply functions_translated in H0. *)
      (*     destruct H0 as (cu & tf & Hfind & Htrans & Hlink). *)
      (*     eexists; split; eauto. *)
      (*   - destruct (Genv.find_symbol ge i) eqn:Hsym; try congruence. *)
      (*     apply function_ptr_translated in H0. *)
      (*     destruct H0 as (cu & tf & Hfind & Htrans & Hlink). *)
      (*     eexists; split; eauto. *)
      (*     rewrite symbols_preserved, Hsym; auto. } *)
      eexists; split.
      + eapply star_plus_trans.
        { apply H7. }
        2: { reflexivity. }
        econstructor.
        2: { apply star_refl. }
        2: { rewrite Events.E0_right; reflexivity. }
        eapply exec_Ibuiltin; simpl.
        { eauto. }
        { eapply eval_builtin_args_preserved.
          2: { (* TODO: eval_builtin_args proper wrt. rs that agree on
                  all args. Then goal immediate by H0. *)
            (* H0 : eval_builtin_args ge (fun r : positive => rs # r) sp m args vargs *)
            admit. }
          intros id; apply symbols_preserved. }
        { eapply external_call_symbols_preserved; eauto.
          apply senv_preserved. }
      +
        (* TODO: copying res to shadow regs. *)

        (* TODO: regmap_setres is equal on both sides. *)
        (* assert (Heq: regmap_setres res vres rs = regmap_setres res vres rs''). *)
        (* { admit. } *)
        (* rewrite Heq. *)
        (* admit. *)

        admit.

        (* { erewrite find_function_proper. *)
        (*   { eauto. } *)
        (*   { intros r ?; subst. *)
        (*       etransitivity. *)
        (*       2: { rewrite <- Hrs''; reflexivity. } *)
        (*       eapply rm_inv_get; eauto. *)
        (*       eexists; eexists; split; eauto; constructor. } *)
        (*     eauto. } *)
        (*   { apply sig_function_translated; auto. } *)
        (* + erewrite rs_args_rs'_args; eauto. *)
        (*   2: { apply Forall_forall; intros r' Hr'; *)
        (*        eexists; eexists; split; eauto; constructor; auto. } *)
        (*   erewrite rs_map_ext; eauto. *)
        (*   constructor; auto. *)
        (*   { econstructor; eauto. *)
        (*     inv WT_FN. *)
        (*     simpl in *. *)
        (*     apply wt_instrs in Hcode. *)
        (*     inv Hcode; auto. } *)
        (*   { destruct ros. *)
        (*     - apply Genv.find_funct_inversion in H0. *)
        (*       destruct H0 as [id H0]. *)
        (*       eapply wt_program_prog; eauto. *)
        (*     - simpl in H0. *)
        (*       destruct (Genv.find_symbol ge i); try congruence. *)
        (*       apply Genv.find_funct_ptr_inversion in H0. *)
        (*       destruct H0 as [id H0]. *)
        (*       eapply wt_program_prog; eauto. } *)
        (*   { constructor; auto. *)
        (*     econstructor; eauto. *)
        (*     eapply rm_inv_ext_r; eauto. } *)
        (*   { apply transf_function_match_fundef; auto. } } *)

    - (* exec_Icond *)
      admit.
    - (* exec_Ijumptable *)
      admit.
    - (* exec_Ireturn *)
      admit.
    - (* exec_function_internal *)
      admit.
    - (* exec_function_external *)
      admit.
    - (* exec_return *)
      admit.
  Admitted.

  Lemma transf_initial_states st1 :
    initial_state prog st1 ->
    exists st2, initial_state tprog st2 /\ match_states st1 st2.
  Proof.
    intros. inversion H.
    exploit function_ptr_translated; eauto. intros (cu & tf & A & B & C).
    subst.
    exists (Callstate nil tf nil m0); split.
    { econstructor; eauto.
      - eapply (Genv.init_mem_match TRANSF); eauto.
      - replace (prog_main tprog) with (prog_main prog).
        rewrite symbols_preserved. eauto.
        symmetry; eapply match_program_main; eauto.
      - rewrite <- H3. eapply sig_function_translated; eauto. }
    generalize (transf_function_match_fundef _ _ B); intro Hmatch_fundef.
    destruct f.
    simpl in *.
    - unfold bind in B.
      destruct (transf_function f) eqn:Hf; inv B.
      unfold transf_function in Hf.
      unfold bind in Hf.
      destruct (type_function f) eqn:Htype; try congruence.
      unfold transf_fun' in Hf.
      gen_case Htransf; inv Hf.
      pose proof Htransf as Htransf_fun.
      unfold transf_fun in Htransf.
      unfold RTLgen.bind in Htransf.
      simpl in *.
      gen_case Hrm.
      gen_case Hcopytransf.
      gen_case Hcopy.
      gen_case Htransf.
      gen_case Htransf'.
      rename t into rm.
      apply match_call_states; auto.
      { constructor; simpl; rewrite H3; reflexivity. }
      { econstructor; apply type_function_correct; eauto. }
      { constructor. }
    - inv B; constructor; try solve[constructor].
      + constructor; rewrite H3; reflexivity.
  Qed.

  Lemma transf_final_states st1 st2 r :
    match_states st1 st2 ->
    final_state st1 r ->
    final_state st2 r.
  Proof.
    intros Hmatch Hfin; inv Hmatch; inv Hfin; inv STACKS; constructor.
  Qed.

  Theorem transf_program_correct :
    forward_simulation (semantics prog) (semantics tprog).
  Proof.
    intros.
    apply forward_simulation_plus with
      (match_states := fun s1 s2 => match_states s1 s2).
    - apply senv_preserved.
    - simpl; intros. exploit transf_initial_states; eauto.
    (* intros [st2 [A B]]. *)
    (* exists st2; intuition. eapply sound_initial; eauto. *)
    - simpl; intros s1 s2 r Hmatch Hfin.
      eapply transf_final_states; eauto; intuition.
    - simpl; intros s1 t s1' Hstep s2 Hmatch.
      eapply step_simulation; eauto; intuition.
  Qed.

End PRESERVATION.
