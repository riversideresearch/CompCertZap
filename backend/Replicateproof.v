(** * Forward simulation proof for TMR pass. *)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Sorting.Permutation.
Require Import
  Decidable(not_or)
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

Local Hint Resolve
  in_eq	(* In x (x :: l) *)
  in_cons	(* In x l -> In x (x :: l) *)
: core.

Definition match_prog (prog tprog: program) :=
  match_program (fun cu f tf => transf_fundef f = OK tf) eq prog tprog.

Lemma transf_program_match:
  forall prog tprog, transf_program prog = OK tprog -> match_prog prog tprog.
Proof.
  intros. eapply match_transform_partial_program_contextual; eauto.
Qed.

(** * Simulation match relations.

    Well-typedness conditions are baked in so that we can easily
    assert that the code and register states are well-typed wrt. the
    regenv used in translation (rather than some arbitrary regenv). *)

(** Replication map invariant relating the register states of the
    original and translated executions. *)

Definition match_regsets
  (params : list reg) (c : code) (rm : replmap) (rs rs' : regset) : Prop :=
  forall r1 r2 r3 : reg,
    rm # r1 = (r2, r3) ->
    reg_used params c r1 ->
    rs # r1 = rs' # r1 /\
      rs # r1 = rs' # r2 /\
      rs # r1 = rs' # r3.

(** Match relation on stacks. It isn't quite sufficient to lift a
    simple 'match_stackframe' relation to lists, because the
    well-typedness of the stack requires a relation between caller and
    callee frames: the return type of the callee's signature must
    match the type of the register used by the caller to store the
    result of the call.  *)
Inductive match_stackframes : list stackframe -> list stackframe -> signature -> Prop :=
| match_stackframes_nil : forall sig,
    sig.(sig_res) = Xint ->
    match_stackframes [] [] sig
| match_stackframes_cons :
  forall stk tstk sig re rm res1 f tf sp pc rs trs res2 res3 n
    (* Well-typed *)
    (WT_FN : wt_function f re)
    (WT_RS : wt_regset re rs)
    (WT_RES : re res1 = proj_sig_res sig)
    (* Match *)
    (FUN : match_function re rm f tf)
    (REGS : match_regsets f.(fn_params) f.(fn_code) rm rs trs)
    (RM_WF : rm_wf rm (fun_regs_list f)),
    reg_used_in_code f.(fn_code) res1 ->
    rm # res1 = (res2, res3) ->
    smoveR tf.(fn_code) (re res1) res1 res2 res3 n pc ->
    match_stackframes stk tstk (fn_sig f) ->
    match_stackframes
      (Stackframe res1 f sp pc rs :: stk)
      (Stackframe res1 tf sp n trs :: tstk) sig.

(** Match program states. *)
Inductive match_states : state -> state -> Prop :=
| match_regular_states :
  forall stk tstk f tf sp pc rs rs' m re rm
    (* Well-typed *)
    (WT_FN: wt_function f re)
    (WT_RS: wt_regset re rs)
    (* Match *)
    (STACKS: match_stackframes stk tstk (fn_sig f))
    (FUN : match_function re rm f tf)
    (REGS : match_regsets f.(fn_params) f.(fn_code) rm rs rs'),
    match_states (State stk f sp pc rs m) (State tstk tf sp pc rs' m)
| match_call_states :
  forall stk tstk f tf args m
    (* Well-typed *)
    (WT_ARGS: Val.has_type_list args (proj_sig_args (funsig f)))
    (* Match *)
    (STACKS: match_stackframes stk tstk (funsig f))
    (FUN : match_fundef f tf),
    match_states (Callstate stk f args m) (Callstate tstk tf args m)
| match_return_states :
  forall sig stk tstk v m
    (* Well-typed *)
    (WT_RES : Val.has_type v (proj_sig_res sig))
    (* Match *)
    (STACKS: match_stackframes stk tstk sig),
    match_states (Returnstate stk v m) (Returnstate tstk v m).

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

  Lemma rs_args1_rs'_args2 params c rm args1 args2 args3 rs rs' :
    match_regsets params c rm rs rs' ->
    Forall (reg_used_in_code c) args1 ->
    rm_l rm args1 args2 args3 ->
    rs ## args1 = rs' ## args2.
  Proof.
    revert args2 args3.
    induction args1; intros args2 args3 Hrm Hall Hmatch.
    - inv Hmatch; auto.
    - inv Hmatch; inv Hall.
      simpl; f_equal; eauto.
      specialize (Hrm a r2 r3 H1 (or_intror H2)); intuition.
  Qed.

  Lemma rs_args1_rs'_args3 params c rm args1 args2 args3 rs rs' :
    match_regsets params c rm rs rs' ->
    Forall (reg_used_in_code c) args1 ->
    rm_l rm args1 args2 args3 ->
    rs ## args1 = rs' ## args3.
  Proof.
    revert args2 args3.
    induction args1; intros args2 args3 Hrm Hall Hmatch.
    - inv Hmatch; auto.
    - inv Hmatch; inv Hall.
      simpl; f_equal; eauto.
      specialize (Hrm a r2 r3 H1 (or_intror H2)); intuition.
  Qed.

  Lemma match_regsets_get params c rm r rs rs' :
    match_regsets params c rm rs rs' ->
    reg_used params c r ->
    rs # r = rs' # r.
  Proof.
    intros Hinv [Hin | Hused].
    - destruct (rm # r) eqn:Hr.
      specialize (Hinv _ _ _ Hr (or_introl Hin)); intuition.
    - destruct (rm # r) eqn:Hr.
      specialize (Hinv _ _ _ Hr (or_intror Hused)); intuition.
  Qed.

  Lemma match_regsets_get_2 params c rm r1 r2 r3 rs rs' :
    match_regsets params c rm rs rs' ->
    reg_used params c r1 ->
    rm # r1 = (r2, r3) ->
    rs # r1 = rs' # r2.
  Proof.
    intros Hinv [Hin | Hused] Hr.
    - specialize (Hinv _ _ _ Hr (or_introl Hin)); intuition.
    - specialize (Hinv _ _ _ Hr (or_intror Hused)); intuition.
  Qed.

  Lemma match_regsets_get_3 params c rm r1 r2 r3 rs rs' :
    match_regsets params c rm rs rs' ->
    reg_used params c r1 ->
    rm # r1 = (r2, r3) ->
    rs # r1 = rs' # r3.
  Proof.
    intros Hinv [Hin | Hused] Hr.
    - specialize (Hinv _ _ _ Hr (or_introl Hin)); intuition.
    - specialize (Hinv _ _ _ Hr (or_intror Hused)); intuition.
  Qed.

  Lemma match_regsets_get_3' params c rm r1 r2 r3 rs rs' :
    match_regsets params c rm rs rs' ->
    reg_used_in_code c r1 ->
    rm # r1 = (r2, r3) ->
    rs' # r2 = rs' # r3.
  Proof.
    intros Hinv Hused Hr.
    specialize (Hinv _ _ _ Hr (or_intror Hused)).
    destruct Hinv as (H0 & H1 & H2).
    rewrite <- H1, <- H2; reflexivity.
  Qed.

  Lemma rs_args_rs'_args params c rm args rs rs' :
    match_regsets params c rm rs rs' ->
    Forall (reg_used_in_code c) args ->
    rs ## args = rs' ## args.
  Proof.
    induction args; intros Hinv Hall.
    - reflexivity.
    - inv Hall; simpl; f_equal; auto.
      destruct (rm # a) eqn:Ha.
      specialize (Hinv _ _ _ Ha (or_intror H1)); intuition.
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

  Lemma match_regsets_eval_addressing params c rm sp a rs rs' args v :
    match_regsets params c rm rs rs' ->
    Forall (reg_used_in_code c) args ->
    eval_addressing ge sp a rs ## args = Some v ->
    eval_addressing tge sp a rs' ## args = Some v.
  Proof.
    intros Hrm Hall Heval.
    erewrite <- rs_args_rs'_args; eauto.
    erewrite eval_addressing_preserved; eauto.
    apply symbols_preserved.
  Qed.

  Lemma match_regsets_storev params c rm a rs rs' v m chunk src :
    match_regsets params c rm rs rs' ->
    reg_used_in_code c src ->
    Memory.Mem.storev chunk m a rs # src = Some v ->
    Memory.Mem.storev chunk m a rs' # src = Some v.
  Proof.
    intros Hinv Hused Hstore; erewrite <- match_regsets_get; eauto; right; auto.
  Qed.

  Lemma match_regs_1_2_eval_operation params c sp op rm args1 args2 args3 rs rs' m v :
    match_regsets params c rm rs rs' ->
    Forall (reg_used_in_code c) args1 ->
    rm_l rm args1 args2 args3 ->
    eval_operation ge sp op rs ## args1 m = Some v ->
    eval_operation tge sp op rs' ## args2 m = Some v.
  Proof.
    intros Hrm Hall Hmatch Hop.
    erewrite <- rs_args1_rs'_args2; eauto.
    erewrite eval_operation_preserved; eauto.
    apply symbols_preserved.
  Qed.

  Lemma match_regs_1_2_eval_addressing params c rm sp a rs rs' args1 args2 args3 v :
    match_regsets params c rm rs rs' ->
    Forall (reg_used_in_code c) args1 ->
    rm_l rm args1 args2 args3 ->
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

  Lemma match_regs_1_3_eval_operation params c sp op rm args1 args2 args3 res2 rs rs' m v :
    match_regsets params c rm rs rs' ->
    ~ In res2 args3 ->
    Forall (reg_used_in_code c) args1 ->
    rm_l rm args1 args2 args3 ->
    eval_operation ge sp op rs ## args1 m = Some v ->
    eval_operation tge sp op (rs' # res2 <- v) ## args3 m = Some v.
  Proof.
    intros Hrm Hnotin Hall Hmatch Hop.
    rewrite not_in_regs_set; auto.
    erewrite <- rs_args1_rs'_args3; eauto; auto.
    erewrite eval_operation_preserved; eauto.
    apply symbols_preserved.
  Qed.

  Lemma match_regs_1_3_eval_addressing params c sp a rm args1 args2 args3 res2 rs rs' v x :
    match_regsets params c rm rs rs' ->
    ~ In res2 args3 ->
    Forall (reg_used_in_code c) args1 ->
    rm_l rm args1 args2 args3 ->
    eval_addressing ge sp a rs ## args1 = Some x ->
    eval_addressing tge sp a (rs' # res2 <- v) ## args3 = Some x.
  Proof.
    intros Hrm Hnotin Hall Hmatch Hop.
    rewrite not_in_regs_set; auto.
    erewrite <- rs_args1_rs'_args3; eauto.
    erewrite eval_addressing_preserved; eauto.
    apply symbols_preserved.
  Qed.

  Lemma regular_eval_operation params c sp op rm args res2 res3 rs rs' m v :
    match_regsets params c rm rs rs' ->
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

  Lemma regular_eval_addressing params c sp a rm args res2 res3 rs rs' v x :
    match_regsets params c rm rs rs' ->
    ~ In res2 args ->
    ~ In res3 args ->
    Forall (reg_used_in_code c) args ->
    eval_addressing ge sp a rs ## args = Some x ->
    eval_addressing tge sp a ((rs' # res2 <- v) # res3 <- v) ## args = Some x.
  Proof.
    intros Hrm Hnotin2 Hnotin3 Hall Hop.
    rewrite 2!not_in_regs_set; auto.
    eapply match_regsets_eval_addressing; eauto.
  Qed.

  Lemma res2_not_in_args1 rm l args1 res1 res2 res3 :
    In res1 l ->
    Forall (fun r => In r l) args1 ->
    rm_wf rm l ->
    rm # res1 = (res2, res3) ->
    ~ In res2 args1.
  Proof.
    rewrite Forall_forall. intros Hres1 Hargs1 Hwf Hget Hres2%Hargs1.
    destruct (peq res1 res2) as [->|NE].
    { eapply rm_wf_ne_12_get; eauto. }
    generalize (rm_wf_nodup_2 Hwf _ _ NE Hres1 Hres2). rewrite Hget. simpl.
    intros Hnodup. inv Hnodup. inv H2. apply H3. simpl. auto.
  Qed.

  Lemma res3_not_in_args1 rm l args1 res1 res2 res3 :
    In res1 l ->
    Forall (fun r => In r l) args1 ->
    rm_wf rm l ->
    rm # res1 = (res2, res3) ->
    ~ In res3 args1.
  Proof.
    rewrite Forall_forall. intros Hres1 Hargs1 Hwf Hget Hres3%Hargs1.
    destruct (peq res1 res3) as [->|NE].
    { eapply rm_wf_ne_13_get; eauto. }
    generalize (rm_wf_nodup_2 Hwf _ _ NE Hres1 Hres3). rewrite Hget. simpl.
    intros Hnodup. inv Hnodup. inv H2. inv H4. apply H2. simpl. auto.
  Qed.

  Lemma res2_not_in_args3 rm l args3 res1 res2 res3 :
    In res1 l ->
    rm_wf rm l ->
    Forall (fun r3 => exists r1 r2, In r1 l /\ rm # r1 = (r2, r3)) args3 ->
    rm # res1 = (res2, res3) ->
    ~ In res2 args3.
  Proof.
    rewrite Forall_forall. intros Hres1 Hwf Hargs3 Hget Hres2%Hargs3.
    destruct Hres2 as (r1 & r2 & Hin & Hget').
    destruct (peq res1 res3) as [->|?].
    { eapply rm_wf_ne_13_get in Hget; eauto. }
    { eapply rm_wf_ne_2'3_get in Hget; eauto. }
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

  Lemma reg_used_in_code_in_elements_code_regs c r :
    reg_used_in_code c r ->
    In r (PSet.elements (code_regs c)).
  Proof.
    intro Hused.
    apply in_elements, reg_used_in_code_pset_in_code_regs; auto.
  Qed.

  Lemma reg_used_in_code_in_all_regs_list params c r :
    reg_used_in_code c r ->
    In r (all_regs_list params c).
  Proof.
    intro Hused.
    apply in_elements, PSet.union_3, in_elements.
    apply reg_used_in_code_in_elements_code_regs; assumption.
  Qed.

  Lemma param_in_all_regs_list c params r :
    In r params ->
    In r (all_regs_list params c).
  Proof.
    intro Hused.
    apply in_elements, PSet.union_2, in_pset_of_list; auto.
  Qed.

  Lemma uregs_in_all_regs_list params c uregs r :
    uregs_ok c params uregs ->
    In r uregs ->
    In r (all_regs_list params c).
  Proof.
    intros. apply reg_used_in_code_in_all_regs_list.
    eapply uregs_ok_code; eauto.
  Qed.

  Lemma prologue_copies_permute params uregs :
    Permutation (prologue_copies params uregs) (params ++ uregs).
  Proof.
    unfold prologue_copies. rewrite rev_append_rev.
    rewrite Permutation_app_comm.
    apply Permutation_app; now rewrite <-Permutation_rev.
  Qed.

  Lemma uregs_ok_rm_wf_mono params uregs c rm :
    uregs_ok c params uregs ->
    rm_wf rm (all_regs_list params c) ->
    rm_wf rm (params ++ uregs).
  Proof.
    intros. eapply rm_wf_mono; [|eassumption].
    intros r. rewrite in_app. intros [].
    - now apply param_in_all_regs_list.
    - eapply uregs_in_all_regs_list; eauto.
  Qed.
  Local Hint Resolve uregs_ok_rm_wf_mono : uregs_ok.

  Lemma uregs_ok_rm_wf_mono' rm c params uregs :
    uregs_ok c params uregs ->
    rm_wf rm (all_regs_list params c) ->
    rm_wf rm (prologue_copies params uregs).
  Proof.
    rewrite prologue_copies_permute.
    apply uregs_ok_rm_wf_mono.
  Qed.
  Local Hint Resolve uregs_ok_rm_wf_mono' : uregs_ok.

  Lemma match_regs_in_args3_exists_in_args1 rm  args1 args2 args3 r3 :
    rm_l rm args1 args2 args3 ->
    In r3 args3 ->
    exists (r1 r2 : reg), In r1 args1 /\ rm # r1 = (r2, r3).
  Proof.
    induction 1; intro Hin.
    { destruct Hin. }
    destruct Hin as [?|Hin]; subst.
    - eexists; eexists; split; eauto; left; reflexivity.
    - apply IHrm_l in Hin.
      destruct Hin as (r1' & r2' & Hin&  Hr'); eexists r1', r2'.
      split; auto; right; assumption.
  Qed.

  Lemma match_regs_exists_r1 rm c args1 args2 args3 r :
    Forall (reg_used_in_code c) args1 ->
    rm_l rm args1 args2 args3 ->
    In r args3 ->
    exists (r1 r2 : reg),
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
    rm_l rm args1 args2 args3 ->
    In r3 args3 ->
    exists (r1 r2 : reg),
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

  Lemma maj_voteR_step
    (r1 r2 r3 : reg) ty pc succ tstk sig params stacksize c entrypoint sp rs m :
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
    intros Hact Hr2 Hr3 Hmaj; inv Hmaj.
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
        destruct (peq r r1); subst.
        2: { rewrite PMap.gso; auto. }
        destruct (rs # r1) eqn:Hr1; simpl; try solve [inv Hact];
          (* This is necessary for riscv but not x86_64. Why? *)
          try solve [destruct Archi.ptr64 eqn:Harchi; simpl in *; try congruence;
                     destruct (eq_block _ _); simpl; try congruence;
                     destruct (Ptrofs.eq_dec _ _); simpl; try congruence;
                     rewrite PMap.gss; reflexivity].
        * rewrite PMap.gss; reflexivity.
        * destruct (Int.eq_dec i i); simpl; try congruence.
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
        destruct (peq r r1); subst.
        2: { rewrite PMap.gso; auto. }
        destruct (rs # r1) eqn:Hr1; simpl; try solve [inv Hact].
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
        destruct (peq r r1); subst.
        2: { rewrite PMap.gso; auto. }
        destruct (rs # r1) eqn:Hr1; simpl; try solve [inv Hact].
        * rewrite PMap.gss; reflexivity.
        * destruct (Int64.eq_dec i i); simpl; try congruence.
          rewrite PMap.gss; reflexivity.
        * destruct Archi.ptr64 eqn:Harchi; simpl.
          2: { simpl in Hact; congruence. }
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
        destruct (peq r r1); subst.
        2: { rewrite PMap.gso; auto. }
        destruct (rs # r1) eqn:Hr1; simpl; try solve [inv Hact].
        * rewrite PMap.gss; reflexivity.
        * destruct (Float32.eq_dec f f); simpl; try congruence.
          rewrite PMap.gss; reflexivity. }
  Qed.

  Lemma maj_vote_regR_star_step
    c re (rm : replmap)
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

  Lemma smove_step
    ty src dst mov tstk sig params stacksize c entrypoint sp rs m pc succ :
    Val.has_type (rs # src) ty ->
    smove ty src dst = Some mov ->
    c ! pc = Some (mov succ) ->
    step tge
      (State tstk
             {| fn_sig := sig
             ; fn_params := params
             ; fn_stacksize := stacksize
             ; fn_code := c
             ; fn_entrypoint := entrypoint |}
             sp pc rs m) E0
    (State tstk
           {| fn_sig := sig
           ; fn_params := params
           ; fn_stacksize := stacksize
           ; fn_code := c
           ; fn_entrypoint := entrypoint |}
           sp succ (rs # dst <- (rs # src)) m).
  Proof.
    intros Hty Hmove Hpc.
    unfold smove in Hmove.
    assert (Heq: rs # dst <- (rs # src) = regmap_setres (BR dst) (rs # src) rs).
    { reflexivity. }
    rewrite Heq; clear Heq.
    destruct ty; inv Hmove.
    - eapply exec_Ibuiltin; eauto.
      + repeat constructor.
      + constructor; simpl.
        unfold Val.has_type in Hty.
        destruct (rs # src); try contradiction; auto.
        rewrite Hty; reflexivity.
    - eapply exec_Ibuiltin; eauto.
      + repeat constructor.
      + constructor.
        unfold Val.has_type in Hty.
        destruct (rs # src); try contradiction; auto.
    - eapply exec_Ibuiltin; eauto.
      + repeat constructor.
      + constructor; simpl.
        destruct (rs # src); auto; simpl in Hty; try contradiction;
          try rewrite Hty; reflexivity.
    - eapply exec_Ibuiltin; eauto.
      + repeat constructor.
      + constructor.
        unfold Val.has_type in Hty.
        destruct (rs # src); try contradiction; auto.
  Qed.

  Lemma smoveR_step tstk sig params stacksize c entrypoint ty r1 r2 r3 sp rs m pc succ :
    Val.has_type (rs # r1) ty ->
    smoveR c ty r1 r2 r3 pc succ ->
    star step tge
      (State tstk
             {| fn_sig := sig
             ; fn_params := params
             ; fn_stacksize := stacksize
             ; fn_code := c
             ; fn_entrypoint := entrypoint |}
             sp pc rs m) E0
    (State tstk
           {| fn_sig := sig
           ; fn_params := params
           ; fn_stacksize := stacksize
           ; fn_code := c
           ; fn_entrypoint := entrypoint |}
           sp succ (rs # r2 <- (rs # r1) # r3 <- (rs # r1)) m).
  Proof.
    intros Hty Hmove; inv Hmove.
    eapply star_step.
    { eapply smove_step.
      - apply Hty.
      - apply H.
      - eauto. }
    2: { reflexivity. }
    eapply star_step.
    { eapply smove_step; eauto.
      destruct (peq r1 r2); subst.
      - rewrite PMap.gss; auto.
      - rewrite PMap.gso; auto. }
    2: { reflexivity. }
    assert (Heq: (rs # r2 <- (rs # r1)) # r3 <- ((rs # r2 <- (rs # r1)) # r1) =
                   ((rs # r2 <- (rs # r1)) # r3 <- (rs # r1))).
    { f_equal.
      destruct (peq r1 r2); subst.
      - rewrite PMap.gss; reflexivity.
      - rewrite PMap.gso; auto. }
    rewrite Heq.
    apply star_refl.
  Qed.

  (** Restatement of  [match_regsets] *)
  Section rsm.
    Local Set Implicit Arguments.
    Local Unset Strict Implicit.
    Local Set Maximal Implicit Insertion.
    Context (rm : replmap).

    Record rsm (D : reg -> Prop) (rs rs' : regset) : Prop := {
      rsm_eq_1 r1 : D r1 -> rs # r1 = rs' # r1;
      rsm_eq_2 r1 : D r1 -> rs # r1 = rs' # (fst (rm # r1));
      rsm_eq_3 r1 : D r1 -> rs # r1 = rs' # (snd (rm # r1));
    }.

    Section eq.
      Context (D : reg -> Prop) (rs rs' : regset).
      Context (Heq : rsm D rs rs').
      Context (r1 r2 r3 : reg) (Hin : D r1) (Hget : rm # r1 = (r2, r3)).

      Lemma rsm_eq_2_regs : rs # r1 = rs' # r2.
      Proof. generalize (rsm_eq_2 Heq Hin). now rewrite Hget. Qed.
      Lemma rsm_eq_3_regs : rs # r1 = rs' # r3.
      Proof. generalize (rsm_eq_3 Heq Hin). now rewrite Hget. Qed.
    End eq.

    Lemma rsm_mono D1 D2 rs rs' :
      (forall r, D2 r -> D1 r) ->
      rsm D1 rs rs' ->
      rsm D2 rs rs'.
    Proof.
      intros D ?. split.
      { intros r ?%D. eapply rsm_eq_1; eauto. }
      { intros r ?%D. eapply rsm_eq_2; eauto. }
      { intros r ?%D. eapply rsm_eq_3; eauto. }
    Qed.
  End rsm.

  Create HintDb rsm discriminated.
  Local Hint Resolve
    rsm_eq_1 rsm_eq_2 rsm_eq_3
    rsm_eq_2_regs rsm_eq_3_regs
  : rsm.

  Lemma rsm_match_regsets params c rm rs rs' :
    rsm rm (reg_used params c) rs rs' ->
    match_regsets params c rm rs rs'.
  Proof.
    intros Hinv r1 r2 r3 Hget Hin.
    repeat split; eauto with rsm.
  Qed.

  (** Pointwise equality *)
  Definition rse (rs rs' : regset) : Prop :=
    forall r : reg, rs # r = rs' # r.
  #[global] Hint Opaque rse : typeclass_instances.
  #[global] Instance rse_preorder : PreOrder rse.
  Proof.
    split.
    - intros rs r. reflexivity.
    - intros rs1 rs2 rs3 ?? r. now etransitivity.
  Qed.
  Lemma rse_rsm {rm dom rs} rs'' {rs'} :
    rsm rm dom rs rs'' ->
    rse rs'' rs' ->
    rsm rm dom rs rs'.
  Proof.
    intros M E. split; intros r Hin.
    { etransitivity. apply (rsm_eq_1 M Hin). apply (E _). }
    { etransitivity. apply (rsm_eq_2 M Hin). apply (E _). }
    { etransitivity. apply (rsm_eq_3 M Hin). apply (E _). }
  Qed.

  (** Pointwise equality on a domain *)
  Definition rsd (D : reg -> Prop) (rs rs' : regset) :=
    forall r, D r -> rs # r = rs' # r.
  Lemma rse_rsd {rs rs'} D : rse rs rs' -> rsd D rs rs'.
  Proof. intros E ??. apply E. Qed.

  Section rsd.
    Local Set Implicit Arguments.
    Local Unset Strict Implicit.
    Local Set Maximal Implicit Insertion.

    Lemma rsd_mono D1 D2 rs rs' :
      (forall r, D2 r -> D1 r) ->
      rsd D1 rs rs' ->
      rsd D2 rs rs'.
    Proof.
      intros Incl D r Hin%Incl. now apply D.
    Qed.
  End rsd.
  #[global] Instance rsd_preorder D : PreOrder (rsd D).
  Proof.
    split.
    - intros rs r ?. reflexivity.
    - intros rs1 rs2 rs3 D1 D2 r Hr. transitivity (rs2 # r); auto.
  Qed.

  (**
  Registers that don't conflict with the shadow registers for [dom].
  *)

  Definition non_shadow (rm : replmap) (dom : list reg) (r : reg) : Prop :=
    Forall (fun r1 : reg => r <> fst (rm # r1) /\ r <> snd (rm # r1)) dom.

  Lemma rm_wf_in_non_shadow rm dom r :
    rm_wf rm dom -> In r dom -> non_shadow rm dom r.
  Proof.
    intros. apply Forall_forall. intros.
    split; eauto with rm_wf symmetry.
  Qed.

  Lemma rm_wf_cons_non_shadow rm dom r1 :
    rm_wf rm (r1 :: dom) -> non_shadow rm dom r1.
  Proof.
    intros. eapply Forall_inv_tail.
    apply rm_wf_in_non_shadow; eauto.
  Qed.
  Local Hint Resolve rm_wf_cons_non_shadow : rm_wf.

  Lemma non_shadow_mono rm dom1 dom2 :
    incl dom2 dom1 ->
    forall r,
    non_shadow rm dom1 r ->
    non_shadow rm dom2 r.
  Proof.
    intros Hdom r. unfold non_shadow.
    now apply incl_Forall.
  Qed.

  (**
  Updating shadow registers.
  *)

  Definition update_regset (rm : replmap) :=
    fix update_regset (rs : regset) (regs : list reg) : regset :=
    match regs with
    | [] => rs
    | r1 :: regs =>
        let (r2, r3) := rm # r1 in
        let rs := update_regset rs regs in
        let v := rs # r1 in
        (rs # r2 <- v) # r3 <- v
    end.

  Lemma update_regset_permute regs1 regs2 rm rs :
    Permutation regs1 regs2 ->
    NoDup regs1 ->
    rm_wf rm regs1 ->
    rse (update_regset rm rs regs1) (update_regset rm rs regs2).
  Proof.
    revert regs1 regs2. apply (Permutation_ind_bis (fun regs1 regs2 =>
      NoDup regs1 ->
      rm_wf rm regs1 ->
      rse (update_regset rm rs regs1) (update_regset rm rs regs2)
    )).
    { repeat intro. reflexivity. }
    { intros r1 l k P IH HD Hwf r. simpl.
      destruct (rm # r1) as [r2 r3] eqn:Hget.
      inv HD.
      destruct (peq r r3); subst.
      { rewrite !Regmap.gss, IH; eauto with rm_wf. }
      rewrite !(Regmap.gso (j:=r3)); auto.
      destruct (peq r r2); subst.
      { rewrite !Regmap.gss, IH; eauto with rm_wf. }
      rewrite !(Regmap.gso (j:=r2)); auto.
      rewrite IH; eauto with rm_wf. }
    { intros r1 r1' l k P IH HD Hwf r. simpl.
      destruct (rm # r1) as [r2 r3] eqn:Hget.
      destruct (rm # r1') as [r2' r3'] eqn:Hget'.
      rewrite !NoDup_cons_iff in HD. destruct HD as (HD & ? & ?).
      apply not_or in HD; fold (In r1' l) in HD. destruct HD as [NE ?].
      destruct (peq r r3'); subst.
      { rewrite Regmap.gss, 4!Regmap.gso, Regmap.gss, IH;
        eauto with rm_wf symmetry. }
      rewrite (Regmap.gso (j:=r3')); [|easy].
      destruct (peq r r3); subst.
      { rewrite Regmap.gss, Regmap.gso, Regmap.gss,
        2!Regmap.gso, IH; eauto with rm_wf symmetry. }
      rewrite (Regmap.gso (i:=r) (j:=r3)); [|easy].
      destruct (peq r r2'); subst.
      { rewrite Regmap.gss, 4!Regmap.gso, Regmap.gss, IH;
        eauto with rm_wf symmetry. }
      rewrite (Regmap.gso (j:=r2')); [|easy].
      destruct (peq r r2); subst.
      { rewrite Regmap.gss, Regmap.gso, Regmap.gss,
        2!Regmap.gso, IH; eauto with rm_wf symmetry. }
      rewrite !Regmap.gso, IH; eauto with rm_wf. }
    { intros l1 l2 l3 P1 IH1 p2 IH2 HD Hwf r.
      rewrite (IH1 HD Hwf). rewrite P1 in HD, Hwf.
      now rewrite (IH2 HD Hwf). }
  Qed.

  Lemma update_regset_not_in (rm : replmap) rs regs :
    rsd (non_shadow rm regs) (update_regset rm rs regs) rs.
  Proof.
    induction regs as [|r1 regs IH]; intros r Hregs; auto.
    generalize (Forall_inv Hregs). intros [??].
    apply Forall_inv_tail in Hregs.
    simpl. destruct (rm # r1) as [r2 r3]. simpl in *.
    rewrite !Regmap.gso; auto.
  Qed.

  Lemma copy_allR_star_step
    c re (rm : replmap)
    args pc succ tstk sig params stacksize entrypoint sp rs m :
    Forall (fun r : reg => Val.has_type (rs # r) (re r)) args ->
    rm_wf rm args ->
    copy_allR re rm c args pc succ ->
    star step tge
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
             sp succ (update_regset rm rs args) m).
  Proof.
    revert rs pc succ.
    induction args; intros rs pc succ Hargs Hwf Hcopy; inv Hcopy.
    { apply star_refl. }
    inv Hargs.
    apply IHargs with (rs := rs) in H2; auto.
    2: { eauto with rm_wf. }
    clear IHargs. eapply star_trans.
    { apply H2. }
    2: { reflexivity. }
    clear H2. simpl.
    rewrite H1.
    eapply smoveR_step; eauto.
    rewrite update_regset_not_in; eauto with rm_wf.
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

  Lemma match_stackframes_sig_proper stk tstk sig1 sig2 :
    sig_res sig1 = sig_res sig2 ->
    match_stackframes stk tstk sig1 ->
    match_stackframes stk tstk sig2.
  Proof.
    intros Hres Hwt.
    induction Hwt.
    { constructor; rewrite <- Hres; auto. }
    econstructor; eauto.
    unfold proj_sig_res. unfold proj_xtype.
    rewrite <- Hres.
    rewrite WT_RES.
    reflexivity.
  Qed.

  Lemma match_regsets_ext_r rs0 rs1 rs2 params c rm :
    (forall r, rs1 # r = rs2 # r) ->
    match_regsets params c rm rs0 rs1 ->
    match_regsets params c rm rs0 rs2.
  Proof.
    unfold match_regsets.
    intros Heq Hinv r1 r2 r3 Hr1 Hused.
    eapply Hinv in Hused; eauto.
    destruct Hused as (H0 & H1 & H2).
    repeat split; auto; rewrite <- Heq; auto.
  Qed.

  Lemma find_function_proper rs rs' ros f :
    (forall r, ros = inl r -> rs # r = rs' # r) ->
    find_function tge ros rs = Some f ->
    find_function tge ros rs' = Some f.
  Proof.
    unfold find_function.
    intros Heq Hfind.
    destruct ros.
    - rewrite <- Heq; auto.
    - destruct (Genv.find_symbol _ _); congruence.
  Qed.

  Lemma eval_builtin_arg_proper rs rs' sp m barg varg :
    (forall arg, in_builtin_arg arg barg -> rs # arg = rs' # arg) ->
    eval_builtin_arg ge (fun r : positive => rs # r) sp m barg varg ->
    eval_builtin_arg ge (fun r : positive => rs' # r) sp m barg varg.
  Proof.
    revert varg; induction barg; intros varg Heq Heval;
      try solve [inv Heval; constructor; auto]; inv Heval;
      try (rewrite Heq; auto; constructor);
      constructor; try apply IHbarg1; try apply IHbarg2; auto;
      intros arg Hin; apply Heq; solve [constructor; auto].
  Qed.

  Lemma eval_builtin_args_proper rs rs' sp m bargs vargs :
    Forall (fun barg => forall arg,
                in_builtin_arg arg barg -> rs # arg = rs' # arg) bargs ->
    eval_builtin_args ge (fun r : positive => rs # r) sp m bargs vargs ->
    eval_builtin_args ge (fun r : positive => rs' # r) sp m bargs vargs.
  Proof.
    revert vargs; induction bargs;
      intros vargs Hall Heval; inv Heval; constructor.
    - inv Hall; eapply eval_builtin_arg_proper; eauto.
    - eapply list_forall2_imply; eauto.
      intros arg v Harg Hv Heval.
      inv Hall; rewrite Forall_forall in H4.
      eapply eval_builtin_arg_proper.
      2: { eauto. }
      intros p Hin; eapply H4; eauto.
  Qed.

  Lemma regmap_setres_id res (vres : val) rs :
    ~ is_BR res ->
    regmap_setres res vres rs = rs.
  Proof.
    intro Hres; destruct res; simpl in *; auto.
    exfalso; apply Hres; constructor.
  Qed.

  Lemma lessdef_list_refl (l : list val) :
    Val.lessdef_list l l.
  Proof. induction l; constructor; auto. Qed.

  Lemma match_regsets_update params c rm rs rs' rs'' res1 res2 res3 vres :
    rm_wf rm (all_regs_list params c) ->
    rm_inv (reg_used params c) rm ->
    rm # res1 = (res2, res3) ->
    (forall r, rs' # r = rs'' # r) ->
    reg_used_in_code c res1 ->
    match_regsets params c rm rs rs' ->
    match_regsets params c rm (rs # res1 <- vres)
      ((rs'' # res1 <- vres) # res2 <- ((rs'' # res1 <- vres) # res1)) # res3 <-
      ((rs'' # res1 <- vres) # res1).
  Proof.
    intros Hwf Hrm Hres1 Hrs'' Hres1_used' Hregs r1 r2 r3 Hr1 Hr1_used.
    assert (Hres1_used : reg_used params c res1) by now right.
    clear Hres1_used'.
    assert (Heq: rs # r1 = rs'' # r1).
    { rewrite <- Hrs''; eapply match_regsets_get; eauto. }
    repeat split.
    { destruct (peq res1 r1); subst.
      - rewrite 2!Regmap.gss.
        rewrite Hres1 in Hr1; inv Hr1.
        rewrite 2!Regmap.gso; eauto with rm_wf.
        rewrite PMap.gss; reflexivity.
      - rewrite 4!Regmap.gso; eauto with rm_wf symmetry. }
    { destruct (peq res1 r1); subst.
      - rewrite 2!PMap.gss.
        rewrite Hres1 in Hr1; inv Hr1.
        rewrite PMap.gso; eauto with rm_wf.
        rewrite PMap.gss; reflexivity.
      - rewrite 4!PMap.gso; eauto with rm_wf.
        rewrite <- Hrs''.
        eapply match_regsets_get_2; eauto. }
    { destruct (peq res1 r1); subst.
      - rewrite 2!PMap.gss.
        rewrite Hres1 in Hr1; inv Hr1.
        rewrite PMap.gss; reflexivity.
      - rewrite 4!PMap.gso; eauto with rm_wf.
        rewrite <- Hrs''.
        eapply match_regsets_get_3; eauto. }
  Qed.

  (**
  A variant of [init_regs] that also initializes shadow registers.
  *)

  Definition init_regs' (rm : replmap) :=
    fix init_regs' (vl : list val) (rl : list reg) {struct rl} : regset :=
    match rl, vl with
    | r1 :: rs, v1 :: vs =>
        let (r2, r3) := rm # r1 in
        (((init_regs' vs rs) # r1 <- v1) # r2 <- v1) # r3 <- v1
    | _, _ => Regmap.init Vundef
    end.

  Lemma not_in_update_regset rm rs r regs v :
    rm_wf rm regs ->
    non_shadow rm regs r ->
    ~ In r regs ->
    (update_regset rm (rs # r <- v) regs) # r = v.
  Proof.
    induction regs as [|r1 regs IH]; simpl; intros Hwf Hne Hnotin.
    { now rewrite Regmap.gss. }
    generalize (Forall_inv Hne). intros [??]. apply Forall_inv_tail in Hne.
    destruct (rm # r1) as [r2 r3] eqn:Hget.
    destruct (peq r r1); subst.
    { exfalso. auto. }
    rewrite 2!Regmap.gso; auto.
    apply IH; eauto with rm_wf.
  Qed.

  Lemma not_in_update_regset' rm rs s r (regs : list reg) v :
    ~ In s regs ->
    s <> r ->
    (update_regset rm (rs # s <- v) regs) # r =
    (update_regset rm rs regs) # r.
  Proof.
    revert r.
    induction regs as [|r1 regs IH]; intros r; simpl; intros Hnotin Hne.
    { now rewrite Regmap.gso. }
    destruct (rm # r1) as [r2 r3] eqn:Hget.
    apply not_or in Hnotin. destruct Hnotin.
    destruct (peq r r3); subst.
    { rewrite !Regmap.gss; auto. }
    rewrite Regmap.gso; [|easy].
    destruct (peq r r2); subst.
    { rewrite Regmap.gss, Regmap.gso, Regmap.gss; auto. }
    rewrite !Regmap.gso; auto.
  Qed.

  Lemma update_regset_init rm regs v (r : reg) :
    (update_regset rm (Regmap.init v) regs) # r = v.
  Proof.
    revert r. induction regs as [|r1 regs IH]; intros r; simpl; auto.
    destruct (rm # r1) as [r2 r3] eqn:Hget.
    destruct (peq r r3); subst.
    { now rewrite Regmap.gss, IH. }
    rewrite Regmap.gso; auto.
    destruct (peq r r2); subst.
    { now rewrite Regmap.gss, IH. }
    rewrite Regmap.gso; auto.
  Qed.

  Lemma init_regs'_update_regset args params uregs rm :
    rm_wf rm (params ++ uregs) ->
    NoDup (params ++ uregs) ->
    length params = length args ->
    rse (init_regs' rm args params)
        (update_regset rm (init_regs args params) (params ++ uregs)).
  Proof.
    intros Hwf Hnodup Hlen.
    revert args Hlen. induction params as [|r1 params IH]; intros args Hlen r; simpl.
    { now rewrite update_regset_init. }
    destruct args; [easy|].
    destruct (rm # r1) as [r2 r3] eqn:Hget.
    inv Hnodup.
    rewrite not_in_update_regset; eauto with rm_wf.
    destruct (peq r r3); subst.
    { now rewrite !Regmap.gss. }
    rewrite !(Regmap.gso (j:=r3)); auto.
    destruct (peq r r2); subst.
    { now rewrite !Regmap.gss. }
    rewrite !(Regmap.gso (j:=r2)); auto.
    destruct (peq r r1); subst.
    { rewrite Regmap.gss, not_in_update_regset; eauto with rm_wf. }
    rewrite Regmap.gso; [|easy].
    rewrite not_in_update_regset'; auto.
    apply IH; eauto with rm_wf.
  Qed.

  Lemma init_regs'_no_args rm params r :
    (init_regs' rm nil params) # r = Vundef.
  Proof. induction params; auto. Qed.

  Lemma init_regs_init_regs' uregs rm args params c :
    rm_inv (reg_used params c) rm ->
    rm_wf rm (all_regs_list params c) ->
    length args = length params ->
    rsd (reg_used params c)
      (init_regs args params) (init_regs' rm args (params ++ uregs)).
  Proof.
    enough (
      init_regs_init_regs'_generic : forall uregs U rm args params,
      rm_inv U rm ->
      length args = length params ->
      rsd (fun r => U r /\ non_shadow rm params r)
        (init_regs args params)
        (init_regs' rm args (params ++ uregs))
    ).
    { intros Hinv Hwf Hlen r Hused.
      erewrite init_regs_init_regs'_generic; eauto. split; auto.
      apply Forall_forall. intros r1 Hr1.
      apply (param_in_all_regs_list c) in Hr1.
      apply reg_used_in_all_regs_list in Hused.
      destruct (peq r r1); subst.
      - eauto with rm_wf.
      - split; eauto with rm_wf symmetry. }
    clear. intros *.
    intros Hinv. revert args.
    induction params as [|r1 params IH]; intros args Hlen r [Hused Hdom].
    { destruct args; [|easy]. now rewrite init_regs'_no_args. }
    destruct args; [easy|]. simpl.
    destruct (Forall_inv Hdom). apply Forall_inv_tail in Hdom.
    destruct (rm # r1) as [r2 r3] eqn:Hget. simpl in *.
    destruct (peq r r1) as [->|?].
    { rewrite Regmap.gss, 2!Regmap.gso, Regmap.gss.
      all: eauto with rm_inv. }
    rewrite Regmap.gso; [|easy].
    rewrite 3!Regmap.gso, IH; eauto.
  Qed.

  Lemma init_regs'_r2 params regs c rm r1 args :
    Forall (fun r => In r (all_regs_list params c)) regs ->
    rm_wf rm (all_regs_list params c) ->
    reg_used params c r1 ->
    (init_regs' rm args regs) # (fst (rm # r1)) = (init_regs' rm args regs) # r1.
  Proof.
    intros Hregs Hwf Hused.
    revert args Hregs. induction regs as [|a regs IH]; [easy|].
    intros [] Hregs; [now auto|]. inv Hregs.
    destruct (rm # r1) as [r2 r3] eqn:Hr1. simpl.
    destruct (rm # a) as [a2 a3] eqn:Ha.
    destruct (peq r1 a); subst.
    { rewrite Hr1 in Ha. inv Ha.
      rewrite Regmap.gso, Regmap.gss; eauto with rm_wf.
      rewrite 2!Regmap.gso, Regmap.gss; eauto with rm_wf. }
    assert (In r1 (all_regs_list params c)).
    { apply reg_used_in_all_regs_list; auto. }
    rewrite !Regmap.gso; eauto with rm_wf symmetry.
  Qed.

  Lemma init_regs'_r3 params regs c rm r1 args :
    Forall (fun r => In r (all_regs_list params c)) regs ->
    rm_wf rm (all_regs_list params c) ->
    reg_used params c r1 ->
    (init_regs' rm args regs) # (snd (rm # r1)) = (init_regs' rm args regs) # r1.
  Proof.
    intros Hregs Hwf Hused.
    revert args Hregs. induction regs as [|a regs IH]; [easy|].
    intros [] Hregs; [now auto|]. inv Hregs.
    destruct (rm # r1) as [r2 r3] eqn:Hr1. simpl.
    destruct (rm # a) as [a2 a3] eqn:Ha.
    destruct (peq r1 a); subst.
    { rewrite Hr1 in Ha. inv Ha.
      rewrite Regmap.gss, 2!Regmap.gso; eauto with rm_wf.
      now rewrite Regmap.gss. }
    assert (In r1 (all_regs_list params c)).
    { apply reg_used_in_all_regs_list; auto. }
    rewrite !Regmap.gso; eauto with rm_wf symmetry.
  Qed.

  Lemma rm_inv_init_regs args params uregs c rm :
    rm_inv (reg_used params c) rm ->
    rm_wf rm (all_regs_list params c) ->
    NoDup params ->
    length params = length args ->
    uregs_ok c params uregs ->
    match_regsets params c rm
      (init_regs args params)
      (update_regset rm (init_regs args params)
        (prologue_copies params uregs)).
  Proof.
    intros Hinv Hwf HDp Hlen Huregs.
    apply rsm_match_regsets.
    apply (rse_rsm (init_regs' rm args params)).
    { assert (Forall (fun r => In r (all_regs_list params c)) params).
      { apply Forall_forall. intros r Hr.
        apply param_in_all_regs_list; auto. }
      split; intros.
      all: erewrite (init_regs_init_regs' nil), app_nil_r; eauto.
      - erewrite init_regs'_r2; eauto.
      - erewrite init_regs'_r3; eauto. }
    etransitivity; [apply init_regs'_update_regset; eauto with uregs_ok|].
    apply update_regset_permute; eauto with uregs_ok.
    now rewrite prologue_copies_permute.
  Qed.

  Lemma copy_allR_params_used_in_code re rm c params pc succ :
    copy_allR re rm c params pc succ ->
    Forall (reg_used_in_code c) params.
  Proof.
    induction 1.
    { constructor. }
    constructor; auto.
    inv H1.
    unfold smove in *.
    destruct (re r1) eqn:Hr1; inv H2; inv H3;
      eexists; eexists; split; eauto; constructor; simpl; auto.
  Qed.

  Lemma wt_regset_init_regs re params args :
    list_norepet params ->
    Val.has_type_list args (map re params) ->
    wt_regset re (init_regs args params).
  Proof.
    revert args; induction params; simpl; intros args Hnodup Hty.
    { constructor. }
    inv Hnodup.
    destruct args; inv Hty.
    intro r.
    destruct (peq r a); subst.
    { rewrite PMap.gss; auto. }
    rewrite PMap.gso; auto.
    apply IHparams; auto.
  Qed.

  Lemma list_norepet_nodup {A : Type} (l : list A) :
    list_norepet l <-> NoDup l.
  Proof. split; induction l; intro H; inv H; constructor; auto. Qed.

  Lemma has_type_list_length args tys :
    Val.has_type_list args tys ->
    length args = length tys.
  Proof.
    revert tys; induction args; intros tys Hty; destruct tys; auto; inv Hty.
    simpl; erewrite IHargs; eauto.
  Qed.

  Ltac reg_used1 :=
    eapply reg_used_in_code_in_all_regs_list;
    eexists; eexists; split; eauto; solve [constructor].

  Ltac reg_used2 :=
    match goal with
    | [Hargs : Forall (reg_used_in_code _) _ |- _] =>
        apply Forall_forall; intros ? ?;
        eapply reg_used_in_code_in_all_regs_list;
        rewrite Forall_forall in Hargs; intuition
    end.

  Theorem step_simulation s1 t s2 :
    step ge s1 t s2 ->
    forall ts1,
      match_states s1 ts1 ->
      exists ts2, plus step tge ts1 t ts2 /\ match_states s2 ts2.
  Proof.
    intros Hstep ts1 Hmatch.
    inv Hstep.

    - (* exec_Inop *)
      inv Hmatch; inv FUN; simpl in *.
      eexists; split.
      + econstructor.
        * apply exec_Inop; simpl.
          specialize (CODE pc (Inop pc') H).
          inv CODE; eauto.
        * apply star_refl.
        * reflexivity.
      + repeat (econstructor; eauto).

    - (* exec_Iop *)
      inv Hmatch; inv FUN; simpl in *.
      set (f := {| fn_sig := sig
                ; fn_params := params
                ; fn_stacksize := stacksize
                ; fn_code := c
                ; fn_entrypoint := entrypoint |}).
      pose proof CODE as Hcode.
      specialize (CODE pc (Iop op args res pc') H); inv CODE.
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
            { eapply res2_not_in_args3 with (l := fun_regs_list f);
                eauto; try reg_used1.
              apply Forall_forall.
              intros r Hin.
              eapply match_regs_exists_r1' with (args1:=args); eauto. }
            2: { eauto. }
            2: { auto. }
            auto. }
          { eapply star_step.
            - eapply exec_Iop; eauto.
              eapply regular_eval_operation; eauto.
              + eapply res2_not_in_args1 with (l := fun_regs_list f);
                  eauto; try reg_used1; reg_used2.
              + eapply res3_not_in_args1 with (l := fun_regs_list f);
                  eauto; try reg_used1; reg_used2.
            - apply star_refl.
            - reflexivity. }
          reflexivity.
        * reflexivity.
      + econstructor; eauto.
        { eapply wt_exec_Iop; eauto.
          eapply wt_instr_at; eauto. }
        * econstructor; eauto.
        * intros r1 r2 r3 Hr1 Hused.
          destruct (peq r1 res); subst.
          { rewrite RM_RES in Hr1; inv Hr1.
            repeat split.
            - rewrite 2!PMap.gss; reflexivity.
            - rewrite PMap.gss, PMap.gso; eauto with rm_wf.
              rewrite PMap.gso; eauto with rm_wf.
              rewrite PMap.gss; reflexivity.
            - rewrite PMap.gss, PMap.gso; eauto with rm_wf.
              rewrite PMap.gss; reflexivity. }
          { assert (Hresused: reg_used_in_code c res).
            { eexists; eexists; split; eauto; apply reg_used_Iop_res. }
            repeat split.
            - rewrite 3!PMap.gso; eauto with rm_inv.
              rewrite PMap.gso; eauto with rm_inv.
              specialize (REGS _ _ _ Hr1 Hused); intuition.
            - rewrite 2!PMap.gso; eauto with rm_inv symmetry.
              rewrite PMap.gso; eauto with rm_wf.
              rewrite PMap.gso; eauto with rm_wf.
              specialize (REGS _ _ _ Hr1 Hused); intuition.
            - rewrite 2!PMap.gso; eauto with rm_inv symmetry.
              rewrite PMap.gso; eauto with rm_wf.
              rewrite PMap.gso; eauto with rm_wf.
              specialize (REGS _ _ _ Hr1 Hused); intuition. }

    - (* exec_Iload *)
      inv Hmatch; inv FUN; simpl in *.
      set (f := {| fn_sig := sig
                ; fn_params := params
                ; fn_stacksize := stacksize
                ; fn_code := c
                ; fn_entrypoint := entrypoint |}).
      pose proof CODE as Hcode.
      specialize (CODE pc (Iload chunk addr args dst pc') H); inv CODE.
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
            { eapply res2_not_in_args3 with (l := fun_regs_list f);
                eauto; try reg_used1.
              apply Forall_forall.
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
              + eapply res2_not_in_args1 with (l := fun_regs_list f);
                  eauto; try reg_used1; reg_used2.
              + eapply res3_not_in_args1 with (l := fun_regs_list f);
                  eauto; try reg_used1; reg_used2.
            - apply star_refl.
            - reflexivity. }
          reflexivity.
        * reflexivity.
      + econstructor; eauto.
        { eapply wt_exec_Iload; eauto.
          eapply wt_instr_at; eauto. }
        * econstructor; eauto.
        * intros r1 r2 r3 Hr1 Hused.
          destruct (peq r1 dst); subst.
          { rewrite RM_RES in Hr1; inv Hr1.
            repeat split.
            - rewrite 2!PMap.gss; reflexivity.
            - rewrite PMap.gss, PMap.gso; eauto with rm_wf.
              rewrite PMap.gso; eauto with rm_wf.
              rewrite PMap.gss; reflexivity.
            - rewrite PMap.gss, PMap.gso; eauto with rm_wf.
              rewrite PMap.gss; reflexivity. }
          { assert (Hdstused: reg_used_in_code c dst).
            { eexists; eexists; split; eauto; apply reg_used_Iload_res. }
            repeat split.
            - rewrite 3!PMap.gso; eauto with rm_inv.
              rewrite PMap.gso; eauto with rm_inv.
              specialize (REGS _ _ _ Hr1 Hused); intuition.
            - rewrite 2!PMap.gso; eauto with rm_inv symmetry.
              rewrite PMap.gso; eauto with rm_wf.
              rewrite PMap.gso; eauto with rm_wf.
              specialize (REGS _ _ _ Hr1 Hused); intuition.
            - rewrite 2!PMap.gso; eauto with rm_inv symmetry.
              rewrite PMap.gso; eauto with rm_wf.
              rewrite PMap.gso; eauto with rm_wf.
              specialize (REGS _ _ _ Hr1 Hused); intuition. }

    - (* exec_Istore *)
      inv Hmatch; inv FUN; simpl in *.
      set (f := {| fn_sig := sig
                 ; fn_params := params
                 ; fn_stacksize := stacksize
                 ; fn_code := c
                 ; fn_entrypoint := entrypoint |}).
      pose proof CODE as Hcode.
      specialize (CODE pc (Istore chunk addr args src pc') H); inv CODE.
      eapply maj_vote_regR_star_step with (m:=m) in VOTE_REGS; eauto.
      2: { apply Forall_forall; intros r1 Hin.
           assert (Hused: reg_used_in_code c r1).
           { eexists; eexists; split; eauto; constructor; assumption. }
           assert (Heq: rs' # r1 = rs # r1).
           { destruct (rm # r1) eqn:Hr1.
             specialize (REGS _ _ _ Hr1 (or_intror Hused)); intuition. }
           rewrite Heq; clear Hused Heq.
           split.
           { apply WT_RS. }
           split.
           - eapply match_regsets_get_2; eauto.
             right; eexists; eexists; split; eauto; constructor; auto.
           - eapply match_regsets_get_3'; eauto.
             eexists; eexists; split; eauto; constructor; auto. }
      destruct VOTE_REGS as (rs'' & Hvote & Hrs'').
      eexists; split.
      + eapply star_plus_trans.
        { apply Hvote. }
        2: { reflexivity. }
        econstructor.
        2: { apply star_refl. }
        2: { rewrite Events.E0_right; reflexivity. }
        eapply exec_Istore; simpl; eauto.
        * erewrite <- rs_map_ext; eauto.
          eapply match_regsets_eval_addressing; eauto.
          apply Forall_forall; intros r Hr; eexists; eexists; split; eauto.
          constructor; auto.
        * rewrite <- Hrs''.
          eapply match_regsets_storev; eauto.
          eexists; eexists; split; eauto; solve [constructor].
      + econstructor; eauto.
        * econstructor; eauto.
        * eapply match_regsets_ext_r; eauto.

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
      specialize (CODE pc (Icall (funsig fd) ros args res pc') Hcode); inv CODE.
      smoveR_inv.
      eapply maj_vote_regR_star_step with (m:=m) in VOTE_ARGS; eauto.
      2: { apply Forall_forall; intros r1 Hin.
           assert (Hused: reg_used_in_code c r1).
           { eexists; eexists; split; eauto.
             apply in_app_or in Hin; destruct Hin as [Hin|Hin].
             - destruct ros; simpl in *; inv Hin; try contradiction.
               constructor.
             - constructor; auto. }
           assert (Heq: rs' # r1 = rs # r1).
           { destruct (rm # r1) eqn:Hr1.
             specialize (REGS _ _ _ Hr1 (or_intror Hused)); intuition. }
           rewrite Heq; clear Heq.
           split.
           { apply WT_RS. }
           split.
           { eapply match_regsets_get_2; eauto; right; auto. }
           { eapply match_regsets_get_3'; eauto. } }
      destruct VOTE_ARGS as (rs'' & Hvote & Hrs'').
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
        { apply Hvote. }
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
            eapply match_regsets_get; eauto.
            right; eexists; eexists; split; eauto; constructor. }
          eauto. }
        { apply sig_function_translated; auto. }
      + erewrite rs_args_rs'_args; eauto.
        2: { apply Forall_forall; intros r' Hr';
             eexists; eexists; split; eauto; constructor; auto. }
        erewrite rs_map_ext; eauto.
        constructor; auto.
        { inv WT_FN; simpl in *.
          apply wt_instrs in Hcode; inv Hcode.
          rewrite <- H11.
          erewrite <- rs_map_ext; eauto.
          erewrite <- rs_args_rs'_args; eauto.
          2: { apply Forall_forall; intros x Hx.
               eexists; eexists; split; eauto; constructor; auto. }
          apply wt_regset_list; auto. }
        { econstructor; eauto.
          - inv WT_FN.
            simpl in *.
            apply wt_instrs in Hcode.
            inv Hcode; auto.
          - eapply match_regsets_ext_r; eauto.
          - eexists; eexists; split; eauto; solve [constructor; auto].
          - econstructor; eauto. }
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
      specialize (CODE pc (Itailcall (funsig fd) ros args) Hcode); inv CODE.
      eapply maj_vote_regR_star_step with (m:=m) in VOTE_ARGS; eauto.
      2: { apply Forall_forall; intros r1 Hin.
           assert (Hused: reg_used_in_code c r1).
           { eexists; eexists; split; eauto.
             apply in_app_or in Hin; destruct Hin as [Hin|Hin].
             - destruct ros; simpl in *; inv Hin; try contradiction.
               constructor.
             - constructor; auto. }
           assert (Heq: rs' # r1 = rs # r1).
           { destruct (rm # r1) eqn:Hr1.
             specialize (REGS _ _ _ Hr1 (or_intror Hused)); intuition. }
           rewrite Heq; clear Heq.
           split.
           { apply WT_RS. }
           split.
           { eapply match_regsets_get_2; eauto; right; auto. }
           { eapply match_regsets_get_3'; eauto. } }
      destruct VOTE_ARGS as (rs'' & Hvote & Hrs'').
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
        { apply Hvote. }
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
            eapply match_regsets_get; eauto.
            right; eexists; eexists; split; eauto; constructor. }
          eauto. }
        { apply sig_function_translated; auto. }
        { eauto. }
      + erewrite rs_args_rs'_args; eauto.
        2: { apply Forall_forall; intros r' Hr';
             eexists; eexists; split; eauto; constructor; auto. }
        erewrite rs_map_ext; eauto.
        constructor; auto.
        { inv WT_FN; simpl in *.
          apply wt_instrs in Hcode; inv Hcode.
          rewrite <- H6.
          erewrite <- rs_map_ext; eauto.
          erewrite <- rs_args_rs'_args; eauto.
          2: { apply Forall_forall; intros x Hx.
               eexists; eexists; split; eauto; constructor; auto. }
          apply wt_regset_list; auto. }
        { eapply match_stackframes_sig_proper.
          2: { eauto. }
          inv WT_FN.
          simpl in *.
          apply wt_instrs in Hcode.
          inv Hcode; auto. }
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
      specialize (CODE pc (Ibuiltin ef args res pc') Hcode); inv CODE.
      { (* No result register *)
        eapply maj_vote_regR_star_step with (m:=m) in VOTE_ARGS; eauto.
        2: { apply Forall_forall; intros r1 Hin.
             assert (Hused: reg_used_in_code c r1).
             { eexists; eexists; split; eauto; constructor; auto. }
             assert (Heq: rs' # r1 = rs # r1).
             { destruct (rm # r1) eqn:Hr1.
               specialize (REGS _ _ _ Hr1 (or_intror Hused)); intuition. }
             rewrite Heq; clear Heq.
             split.
             { apply WT_RS. }
             split.
             { eapply match_regsets_get_2; eauto; right; auto. }
             { eapply match_regsets_get_3'; eauto. } }
        destruct VOTE_ARGS as (rs'' & Hvote & Hrs'').
        eexists; split.
        + eapply star_plus_trans.
          { apply Hvote. }
          2: { reflexivity. }
          econstructor.
          3: { rewrite Events.E0_right; reflexivity. }
          { eapply exec_Ibuiltin; simpl.
            { eauto. }
            { eapply eval_builtin_args_preserved.
              - intros id; apply symbols_preserved.
              - eapply eval_builtin_args_proper; eauto.
                apply Forall_forall.
                intros arg Harg r Hr.
                rewrite <- Hrs''.
                eapply match_regsets_get; eauto.
                right; eexists; eexists; split; eauto.
                constructor.
                apply in_regs_of_builtin_args_exists_in_builtin_arg.
                apply Exists_exists.
                eexists; split; eauto. }
            { eapply external_call_symbols_preserved; eauto.
              apply senv_preserved. } }
          rewrite regmap_setres_id; auto.
          apply star_refl.
        + rewrite regmap_setres_id; auto.
          econstructor; eauto.
          eapply match_regsets_ext_r; eauto. }
      { (* With result register *)
        eapply maj_vote_regR_star_step with (m:=m) in VOTE_ARGS; eauto.
        2: { apply Forall_forall; intros r1 Hin.
             assert (Hused: reg_used_in_code c r1).
             { eexists; eexists; split; eauto; constructor; auto. }
             assert (Heq: rs' # r1 = rs # r1).
             { destruct (rm # r1) eqn:Hr1.
               specialize (REGS _ _ _ Hr1 (or_intror Hused)); intuition. }
             rewrite Heq; clear Heq.
             split.
             { apply WT_RS. }
             split.
             { eapply match_regsets_get_2; eauto; right; auto. }
             { eapply match_regsets_get_3'; eauto. } }
        destruct VOTE_ARGS as (rs'' & Hvote & Hrs'').
        assert (Hty: Val.has_type vres (re res1)).
        { inv WT_FN.
          simpl in *.
          specialize (wt_instrs _ _ Hcode).
          inv wt_instrs.
          simpl in *.
          rewrite H7.
          eapply external_call_well_typed; eauto. }
        eexists; split.
        + eapply star_plus_trans.
          { apply Hvote. }
          2: { reflexivity. }
          econstructor.
          3: { rewrite Events.E0_right; reflexivity. }
          { eapply exec_Ibuiltin; simpl.
            { eauto. }
            { eapply eval_builtin_args_preserved.
              - intros id; apply symbols_preserved.
              - eapply eval_builtin_args_proper; eauto.
                apply Forall_forall.
                intros arg Harg r Hr.
                rewrite <- Hrs''.
                eapply match_regsets_get; eauto.
                right; eexists; eexists; split; eauto.
                constructor.
                apply in_regs_of_builtin_args_exists_in_builtin_arg.
                apply Exists_exists.
                eexists; split; eauto. }
            { eapply external_call_symbols_preserved; eauto.
              apply senv_preserved. } }
          eapply smoveR_step in MOVE; eauto.
          simpl.
          rewrite PMap.gss; auto.
        + simpl.
          econstructor; eauto.
          intro r.
          destruct (peq res1 r); subst.
          * rewrite PMap.gss; auto.
          * rewrite PMap.gso; auto.
          * eapply match_regsets_update; eauto.
            eexists; eexists; split; eauto; solve [constructor; auto]. }

    - (* exec_Icond *)
      inv Hmatch.
      pose proof FUN as Hmatch_function.
      inv FUN; simpl in *.
      set (f := {| fn_sig := sig
                ; fn_params := params
                ; fn_stacksize := stacksize
                ; fn_code := c
                ; fn_entrypoint := entrypoint |}).
      pose proof H as Hcode.
      specialize (CODE pc (Icond cond args ifso ifnot) Hcode); inv CODE.
      eapply maj_vote_regR_star_step with (m:=m) in VOTE_ARGS; eauto.
      2: { apply Forall_forall; intros r1 Hin.
           assert (Hused: reg_used_in_code c r1).
           { eexists; eexists; split; eauto; constructor; auto. }
           assert (Heq: rs' # r1 = rs # r1).
           { destruct (rm # r1) eqn:Hr1.
             specialize (REGS _ _ _ Hr1 (or_intror Hused)); intuition. }
           rewrite Heq; clear Heq.
           split.
           { apply WT_RS. }
           split.
           { eapply match_regsets_get_2; eauto; right; auto. }
           { eapply match_regsets_get_3'; eauto. } }
      destruct VOTE_ARGS as (rs'' & Hvote & Hrs'').
      eexists; split.
      + eapply star_plus_trans.
        { apply Hvote. }
        2: { reflexivity. }
        econstructor.
        3: { rewrite Events.E0_right; reflexivity. }
        { eapply exec_Icond with (b := b)
                                 (pc' := if b then ifso else ifnot);
            simpl; auto.
          { eauto. }
          { eapply eval_condition_lessdef; eauto.
            - erewrite rs_args_rs'_args; eauto.
              + erewrite rs_map_ext; eauto.
                apply lessdef_list_refl.
              + apply Forall_forall; intros x Hx.
                eexists; eexists; split; eauto; constructor; auto.
            - apply Memory.Mem.extends_refl. } }
        apply star_refl.
      + econstructor; eauto.
        eapply match_regsets_ext_r; eauto.

    - (* exec_Ijumptable *)
      inv Hmatch.
      pose proof FUN as Hmatch_function.
      inv FUN; simpl in *.
      set (f := {| fn_sig := sig
                ; fn_params := params
                ; fn_stacksize := stacksize
                ; fn_code := c
                ; fn_entrypoint := entrypoint |}).
      pose proof H as Hcode.
      specialize (CODE pc (Ijumptable arg tbl) Hcode); inv CODE.
      assert (Hused: reg_used_in_code c arg).
      { eexists; eexists; split; eauto; constructor. }
      eapply maj_voteR_step with (rs := rs') in VOTE.
      2: { erewrite <- match_regsets_get; eauto; right; auto. }
      2: { erewrite <- match_regsets_get; eauto.
           - eapply match_regsets_get_2; eauto; right; auto.
           - right; auto. }
      2: { eapply match_regsets_get_3'; eauto. }
      destruct VOTE as (rs'' & Hvote & Hrs'').
      eexists; split.
      + eapply plus_trans.
        { apply Hvote. }
        2: { reflexivity. }
        econstructor.
        3: { rewrite Events.E0_right; reflexivity. }
        { eapply exec_Ijumptable; eauto.
          rewrite <- Hrs''.
          erewrite <- match_regsets_get; eauto; right; auto. }
        apply star_refl.
      + econstructor; eauto.
        eapply match_regsets_ext_r; eauto.

    - (* exec_Ireturn *)
      inv Hmatch.
      pose proof FUN as Hmatch_function.
      inv FUN; simpl in *.
      set (f := {| fn_sig := sig
                ; fn_params := params
                ; fn_stacksize := stacksize
                ; fn_code := c
                ; fn_entrypoint := entrypoint |}).
      pose proof H as Hcode.
      specialize (CODE pc (Ireturn or) Hcode); inv CODE.
      + (* Without return value *)
        eexists; split.
        * econstructor.
          { apply exec_Ireturn; eauto. }
          { apply star_refl. }
          reflexivity.
        * econstructor; eauto.
          inv WT_FN; simpl in *.
          apply wt_instrs in Hcode; inv Hcode; auto.
      + (* With return value *)
        assert (Hused: reg_used_in_code c arg1).
        { eexists; eexists; split; eauto; constructor. }
        eapply maj_voteR_step with (rs := rs') in VOTE.
        2: { erewrite <- match_regsets_get; eauto; right; auto. }
        2: { erewrite <- match_regsets_get; eauto.
             - eapply match_regsets_get_2; eauto; right; auto.
             - right; auto. }
        2: { eapply match_regsets_get_3'; eauto. }
        destruct VOTE as (rs'' & Hvote & Hrs'').
        eexists; split.
        * eapply plus_trans.
          { apply Hvote. }
          2: { reflexivity. }
          econstructor.
          3: { rewrite Events.E0_right; reflexivity. }
          { eapply exec_Ireturn; eauto. }
        apply star_refl.
        * simpl; rewrite <- Hrs''.
          erewrite match_regsets_get; eauto.
          { econstructor; eauto.
            inv WT_FN; simpl in *.
            apply wt_instrs in Hcode; inv Hcode.
            simpl in H3; rewrite <- H3.
            erewrite <- match_regsets_get; eauto; right; auto. }
          right; auto.

    - (* exec_function_internal *)
      inv Hmatch; inv FUN; inv FUN0; simpl in *.
      eexists; split.
      + econstructor.
        * apply exec_function_internal; eauto.
        * simpl.
          eapply copy_allR_star_step.
          3: eassumption.
          { apply Forall_forall.
            intros x Hx.
            inv WT; subst; simpl in *.
            rewrite <- wt_params in WT_ARGS.
            apply wt_regset_init_regs; auto. }
          { eauto with uregs_ok. }
        * reflexivity.
      + econstructor; eauto.
        * apply wt_init_regs.
          inv WT; simpl in *.
          rewrite wt_params; auto.
        * econstructor; eauto.
        * apply rm_inv_init_regs; auto.
          { inv WT; simpl in *; apply list_norepet_nodup; auto. }
          { inv WT; simpl in *. clear -wt_params WT_ARGS.
            apply has_type_list_length in WT_ARGS.
            rewrite <- wt_params in WT_ARGS.
            now rewrite list_length_map in WT_ARGS. }

    - (* exec_function_external *)
      inv Hmatch; inv FUN; simpl in *.
      eexists; split.
      + econstructor.
        * apply exec_function_external.
          eapply external_call_symbols_preserved; eauto.
          apply senv_preserved.
        * apply star_refl.
        * rewrite E0_right; reflexivity.
      + econstructor; eauto.
        eapply external_call_well_typed; eauto.

    - (* exec_return *)
      inv Hmatch; inv STACKS.
      destruct tf; simpl in *.
      eexists; split.
      + econstructor.
        * apply exec_return.
        * eapply smoveR_step with (rs := trs # res <- vres) in H9.
          2: { rewrite PMap.gss; rewrite WT_RES0; auto. }
          eapply H9.
        * reflexivity.
      + econstructor; eauto.
        * intro r.
          destruct (peq r res); subst.
          { rewrite PMap.gss; rewrite WT_RES0; auto. }
          rewrite PMap.gso; auto.
        * eapply match_regsets_update; eauto.
          inv FUN; auto.
  Qed.

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
        rewrite symbols_preserved; eauto.
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
      apply match_call_states; auto.
      { simpl; rewrite H3; apply I. }
      { econstructor; simpl; rewrite H3; reflexivity. }
    - inv B; constructor; try solve[constructor].
      + simpl in *; rewrite H3; apply I.
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
    - simpl; intros s1 s2 r Hmatch Hfin.
      eapply transf_final_states; eauto; intuition.
    - simpl; intros s1 t s1' Hstep s2 Hmatch.
      eapply step_simulation; eauto; intuition.
  Qed.
End PRESERVATION.
