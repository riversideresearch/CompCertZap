(** * Forward simulation proof for DMR pass. *)

(* TODO: factor out things in common with TMR (and do same for spec). *)

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
  DMRspec
  RTLgen
  RTLtyping
  Smallstep
  Values
.
Require Import RTL.
Require Import DMR.
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

(** * Simulation match relations.

    Well-typedness conditions are baked in so that we can easily
    assert that the code and register states are well-typed wrt. the
    regenv used in translation (rather than some arbitrary regenv). *)

(** Replication map invariant relating the register states of the
    original and translated executions. *)
Definition match_regsets
  (params : list reg) (c : code) (rm : PMap.t reg) (rs rs' : regset) : Prop :=
  forall r,
    reg_used params c r ->
    rs # r = rs' # r /\
      rs # r = rs' # (rm # r).

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
  forall stk tstk sig re rm res f tf sp pc rs trs n
    (* Well-typed *)
    (WT_FN : wt_function f re)
    (WT_RS : wt_regset re rs)
    (WT_RES : re res = proj_sig_res sig)
    (* Match *)
    (FUN : match_function re rm f tf)
    (REGS : match_regsets f.(fn_params) f.(fn_code) rm rs trs)
    (RM_WF : rm_wf rm (fun_regs_list f)),
    reg_used_in_code f.(fn_code) res ->
    smoveR tf.(fn_code) (re res) res (rm # res) n pc ->
    match_stackframes stk tstk (fn_sig f) ->
    match_stackframes
      (Stackframe res f sp pc rs :: stk)
      (Stackframe res tf sp n trs :: tstk) sig.

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

  Ltac in_list :=
    match goal with
    | [ |- In ?x (?x :: _) ] => left; reflexivity
    | [ |- In ?x (?y :: ?ys) ] => right; in_list
    end.

  Ltac not_in_list :=
    match goal with
    | [ H: ~ In ?x (?y :: ?ys) |- _ ] => exfalso; apply H; in_list
    end.

  Ltac nodup_false :=
    match goal with
    | [ H : NoDup (?x :: ?xs) |- _ ] => inv H; try not_in_list; nodup_false
    end.      

  Ltac not_nodup :=
    match goal with
    | [ |- ~ NoDup (?x :: ?xs) ] => intro HC; nodup_false
    end.

  Lemma rm_wf_neq_1_2 (rm : PMap.t reg) l (r : reg) :
    rm_wf rm l ->
    In r l ->
    r <> rm # r.
  Proof.
    intros Hwf Hn ?; subst.
    apply Hwf in Hn; auto; intuition.
  Qed.

  Lemma rm_wf_neq_2_2 (rm : PMap.t reg) l (r r' : reg) :
    rm_wf rm l ->
    r <> r' ->
    In r l ->
    In r' l ->
    rm # r' <> rm # r.
  Proof.
    intros Hwf Hneq Hn Hn' ?; subst.
    specialize (Hwf r Hn).
    destruct Hwf as [Hr Hwf].
    specialize (Hwf r' Hn' Hneq).
    rewrite H in Hwf.
    nodup_false.
  Qed.

  Lemma rm_wf_neq_2_1' (rm : PMap.t reg) l (r r' : reg) :
    rm_wf rm l ->
    In r l ->
    In r' l ->
    rm # r' <> r.
  Proof.
    intros Hwf Hn Hn' ?; subst.
    destruct (DecidableTypeEx.Positive_as_DT.eq_dec (rm # r') r'); subst.
    - eapply rm_wf_neq_1_2; eauto.
    - apply Hwf in Hn.
      destruct Hn as [Hneq Hn].
      apply Hn in Hn'; auto.
      nodup_false.
  Qed.

  Lemma rm_wf_neq_2_2' (rm : PMap.t reg) l (r r' : reg) :
    rm_wf rm l ->
    In r l ->
    In r' l ->
    r <> r' ->
    rm # r' <> rm # r.
  Proof.
    intros Hwf Hn Hn' Hneq HC.
    apply Hwf in Hn.
    destruct Hn as [Hneq' Hn].
    apply Hn in Hn'; auto.
    rewrite HC in Hn'.
    nodup_false.
  Qed.

  Lemma rs_args1_rs'_args2 params c rm args1 args2 rs rs' :
    match_regsets params c rm rs rs' ->
    Forall (reg_used_in_code c) args1 ->
    rm_l rm args1 args2 ->
    rs ## args1 = rs' ## args2.
  Proof.
    revert args2.
    induction args1; intros args2 Hrm Hall Hmatch.
    - inv Hmatch; auto.
    - inv Hmatch; inv Hall.
      simpl; f_equal; eauto.
      unfold match_regsets in Hrm.
      specialize (Hrm a (or_intror H1)); intuition.
  Qed.

  Lemma match_regsets_get params c rm r rs rs' :
    match_regsets params c rm rs rs' ->
    reg_used params c r ->
    rs # r = rs' # r.
  Proof.
    intros Hinv [Hin | Hused].
    - specialize (Hinv _ (or_introl Hin)); intuition.
    - specialize (Hinv _ (or_intror Hused)); intuition.
  Qed.

  Lemma match_regsets_get_2 params c rm r rs rs' :
    match_regsets params c rm rs rs' ->
    reg_used params c r ->
    rs # r = rs' # (rm # r).
  Proof.
    intros Hinv [Hin | Hused].
    - specialize (Hinv _ (or_introl Hin)); intuition.
    - specialize (Hinv _ (or_intror Hused)); intuition.
  Qed.

  Lemma rs_args_rs'_args params c rm args rs rs' :
    match_regsets params c rm rs rs' ->
    Forall (reg_used_in_code c) args ->
    rs ## args = rs' ## args.
  Proof.
    induction args; intros Hinv Hall.
    - reflexivity.
    - inv Hall; simpl; f_equal; auto.
      specialize (Hinv _ (or_intror H1)); intuition.
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

  Lemma match_regs_1_2_eval_operation params c sp op rm args1 args2 rs rs' m v :
    match_regsets params c rm rs rs' ->
    Forall (reg_used_in_code c) args1 ->
    rm_l rm args1 args2 ->
    eval_operation ge sp op rs ## args1 m = Some v ->
    eval_operation tge sp op rs' ## args2 m = Some v.
  Proof.
    intros Hrm Hall Hmatch Hop.
    erewrite <- rs_args1_rs'_args2; eauto.
    erewrite eval_operation_preserved; eauto.
    apply symbols_preserved.
  Qed.

  Lemma match_regs_1_2_eval_addressing params c rm sp a rs rs' args1 args2 v :
    match_regsets params c rm rs rs' ->
    Forall (reg_used_in_code c) args1 ->
    rm_l rm args1 args2 ->
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

  Lemma regular_eval_operation params c sp op rm args res2 rs rs' m v :
    match_regsets params c rm rs rs' ->
    ~ In res2 args ->
    Forall (reg_used_in_code c) args ->
    eval_operation ge sp op rs ## args m = Some v ->
    eval_operation tge sp op (rs' # res2 <- v) ## args m = Some v.
  Proof.
    intros Hrm Hnotin2 Hall Hop.
    rewrite not_in_regs_set; auto.
    erewrite <- rs_args_rs'_args; eauto.
    erewrite eval_operation_preserved; eauto.
    apply symbols_preserved.
  Qed.

  Lemma regular_eval_addressing params c sp a rm args res2 rs rs' v x :
    match_regsets params c rm rs rs' ->
    ~ In res2 args ->
    Forall (reg_used_in_code c) args ->
    eval_addressing ge sp a rs ## args = Some x ->
    eval_addressing tge sp a (rs' # res2 <- v) ## args = Some x.
  Proof.
    intros Hrm Hnotin2 Hall Hop.
    rewrite not_in_regs_set; auto.
    eapply match_regsets_eval_addressing; eauto.
  Qed.

  Lemma res2_not_in_args1 rm l args1 res1 :
    In res1 l ->
    Forall (fun r => In r l) args1 ->
    rm_wf rm l ->
    ~ In (rm # res1) args1.
  Proof.
    intros Hres1 Hargs1 Hwf H.
    rewrite Forall_forall in Hargs1.
    apply Hargs1 in H.
    apply Hwf in Hres1.
    destruct Hres1 as [Hneq Hres1].
    apply Hres1 in H; auto.
    nodup_false.
  Qed.

  Lemma pset_in_res_fold_right pc op args res pc' l :
    In (pc, Iop op args res pc') l ->
    Regset.In res
      (fold_right (fun (y : positive * instruction) (x : Regset.t) =>
                     Regset.union x (instr_regs (snd y))) Regset.empty
         l).
  Proof.
    revert pc op args res pc'.
    induction l; simpl; intros pc op args res pc' Hin; try contradiction.
    destruct a as [p i]; simpl.
    destruct Hin as [H | Hin].
    - inv H; apply Regset.union_3, Regset.union_3, Regset.singleton_2; reflexivity.
    - apply Regset.union_2; eapply IHl; eauto.
  Qed.

  Lemma reg_used_in_code_in_elements_code_regs c r :
    reg_used_in_code c r ->
    In r (Regset.elements (code_regs c)).
  Proof.
    intro Hused.
    apply in_elements, reg_used_in_code_pset_in_code_regs; auto.
  Qed.

  Lemma reg_used_in_code_in_all_regs_list params c r :
    reg_used_in_code c r ->
    In r (all_regs_list params c).
  Proof.
    intro Hused.
    apply in_elements, Regset.union_3, in_elements.
    apply reg_used_in_code_in_elements_code_regs; assumption.
  Qed.

  Lemma param_in_all_regs_list params c r :
    In r params ->
    In r (all_regs_list params c).
  Proof.
    intro Hused.
    apply in_elements, Regset.union_2, in_pset_of_list; auto.
  Qed.

  Lemma checkR_step
    r1 r2 ty pc succ tstk sig params stacksize c entrypoint sp rs m :
    checkR c ty r1 r2 pc succ ->
    step tge
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
             sp succ rs m).
  Proof.
    intro H; inv H.
    replace rs with (regmap_setres BR_none Vundef rs) by auto.
    unfold DMR.check_of_typ in H1.
    destruct ty; simpl in H0; try contradiction; clear H0; inv H1;
      eapply exec_Ibuiltin with (vargs := [rs # r1; rs # r2]);
      simpl; eauto; repeat constructor.
  Qed.

  Lemma check_regsR_star_step
    c re (rm : PMap.t reg)
    args pc n tstk sig params stacksize entrypoint sp rs m :
    check_regsR c re rm args pc n ->
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
             sp n rs m).
  Proof.
    revert pc n.
    induction args; intros pc n Hchk; inv Hchk.
    { apply star_refl. }
    eapply star_step; eauto.
    - eapply checkR_step; eauto.
    - reflexivity.
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

  Lemma smoveR_step tstk sig params stacksize c entrypoint ty r1 r2 sp rs m pc succ :
    Val.has_type (rs # r1) ty ->
    smoveR c ty r1 r2 pc succ ->
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
           sp succ (rs # r2 <- (rs # r1)) m).
  Proof.
    intros Hty Hmov; inv Hmov.
    eapply smove_step; eauto.
  Qed.

  (* Lemma smoveR_step tstk sig params stacksize c entrypoint ty r1 r2 sp rs m pc succ : *)
  (*   Val.has_type (rs # r1) ty -> *)
  (*   smoveR c ty r1 r2 pc succ -> *)
  (*   star step tge *)
  (*     (State tstk *)
  (*            {| fn_sig := sig *)
  (*            ; fn_params := params *)
  (*            ; fn_stacksize := stacksize *)
  (*            ; fn_code := c *)
  (*            ; fn_entrypoint := entrypoint |} *)
  (*            sp pc rs m) E0 *)
  (*   (State tstk *)
  (*          {| fn_sig := sig *)
  (*          ; fn_params := params *)
  (*          ; fn_stacksize := stacksize *)
  (*          ; fn_code := c *)
  (*          ; fn_entrypoint := entrypoint |} *)
  (*          sp succ (rs # r2 <- (rs # r1)) m). *)
  (* Proof. *)
  (*   intros Hty Hmove; inv Hmove. *)
  (*   eapply star_step. *)
  (*   { eapply smove_step. *)
  (*     - apply Hty. *)
  (*     - apply H. *)
  (*     - eauto. } *)
  (*   2: { reflexivity. } *)
  (*   eapply star_step. *)
  (*   { eapply smove_step; auto. *)
      
  (*     destruct (DecidableTypeEx.Positive_as_DT.eq_dec r1 r2); subst. *)
  (*     - rewrite PMap.gss; auto. *)
  (*     - rewrite PMap.gso; auto. } *)
  (*   2: { reflexivity. } *)
  (*   assert (Heq: (rs # r2 <- (rs # r1)) # r3 <- ((rs # r2 <- (rs # r1)) # r1) = *)
  (*                  ((rs # r2 <- (rs # r1)) # r3 <- (rs # r1))). *)
  (*   { f_equal. *)
  (*     destruct (DecidableTypeEx.Positive_as_DT.eq_dec r1 r2); subst. *)
  (*     - rewrite PMap.gss; reflexivity. *)
  (*     - rewrite PMap.gso; auto. } *)
  (*   rewrite Heq. *)
  (*   apply star_refl. *)
  (* Qed. *)

  (* Fixpoint shadow_regs (rm : PMap.t reg) (args : list reg) : list reg := *)
  (*   match args with *)
  (*   | [] => [] *)
  (*   | r1 :: args' => *)
  (*       rm # r1 :: shadow_regs rm args' *)
  (*   end. *)

  (* (* TODO: get rid of this entirely if possible and replace with *)
  (*    simpler proof strategy for establishing match_regsets upon *)
  (*    function entry. *) *)
  (* Fixpoint update_regset *)
  (*   (rm : PMap.t reg) (rs : regset) (args : list reg) *)
  (*   : regset := *)
  (*   match args with *)
  (*   | [] => rs *)
  (*   | r1 :: args' => *)
  (*       let rs' := update_regset rm rs args' in *)
  (*       rs' # (rm # r1) <- (rs' # r1) *)
  (*   end. *)

  Fixpoint update_regset
    (rm : PMap.t reg) (rs : regset) (args : list reg)
    : regset :=
    match args with
    | [] => rs
    | arg :: args' =>
        update_regset rm (rs # (rm # arg) <- (rs # arg)) args'
    end.

  (* Inductive updated_regset *)
  (*   (rm : PMap.t reg) (rs : regset) : list reg -> regset -> Prop := *)
  (* | updated_regset_nil : updated_regset rm rs [] rs *)
  (* | updated_regset_cons : *)
  (*   forall r1 rest rs' rs'', *)
  (*     updated_regset rm rs rest rs' -> *)
  (*     rs'' = rs' # (rm # r1) <- (rs # r1) -> *)
  (*     updated_regset rm rs (r1 :: rest) rs''. *)

  Lemma rm_wf_cons rm a args :
    rm_wf rm (a :: args) ->
    rm_wf rm args.
  Proof.
    unfold rm_wf.
    intros Hwf r1 Hin.
    specialize (Hwf r1 (in_cons _ _ _ Hin)).
    destruct Hwf as (Hnodup & Hwf).
    split; auto.
    intros r1' Hin' Hneq.
    apply Hwf; auto; right; auto.
  Qed.

  Lemma update_regset_not_in
    (rm : PMap.t reg) (rs : regset) (r : reg) (args : list reg) :
    Forall (fun r1 => r <> rm # r1) args ->
    (update_regset rm rs args) # r = rs # r.
  Proof.
    revert r rs; induction args; simpl; intros r rs Hall; auto.
    inv Hall.
    rewrite IHargs; auto.
    rewrite PMap.gso; auto.
  Qed.

  Lemma copy_allR_star_step
    c re (rm : PMap.t reg)
    args pc succ tstk sig params stacksize entrypoint sp rs m :
    Forall (fun r => Val.has_type (rs # r) (re r)) args ->
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
    eapply star_step.
    { eapply smoveR_step; eauto. }
    2: { reflexivity. }
    simpl.
    apply IHargs; auto.
    - apply Forall_forall; intros x Hin.
      rewrite Forall_forall in H3.
      specialize (H3 _ Hin).
      generalize (rm_wf_neq_2_1' rm (a :: args) x a).
      intro H; apply H in Hwf.
      2: { right; auto. }
      2: { left; reflexivity. }
      destruct (DecidableTypeEx.Positive_as_DT.eq_dec (rm # a) x); subst.
      { contradiction. }
      { rewrite PMap.gso; auto. }
    - eapply rm_wf_cons; eauto.
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
    intros Heq Hinv r1 Hused.
    eapply Hinv in Hused; eauto.
    destruct Hused as [H0 H1].
    split; auto; rewrite <- Heq; auto.
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

  Lemma match_regsets_update params c rm rs rs' rs'' res vres :
    rm_wf rm (all_regs_list params c) ->
    rm_inv params c rm ->
    (forall r, rs' # r = rs'' # r) ->
    reg_used_in_code c res ->
    match_regsets params c rm rs rs' ->
    match_regsets params c rm (rs # res <- vres)
      (rs'' # res <- vres) # (rm # res) <- ((rs'' # res <- vres) # res).
  Proof.
    intros Hwf Hrm Hrs'' Hres1_used Hregs r1 Hr1_used.
    assert (Heq: rs # r1 = rs'' # r1).
    { rewrite <- Hrs''; eapply match_regsets_get; eauto. }
    unfold reg_used in Hr1_used.
    split.
    { destruct (DecidableTypeEx.Positive_as_DT.eq_dec res r1); subst.
      - rewrite 2!PMap.gss.
        rewrite PMap.gso.
        2: { eapply rm_wf_neq_1_2; eauto.
             apply reg_used_in_all_regs_list; auto. }
        rewrite PMap.gss; reflexivity.
      - rewrite 3!PMap.gso; auto; intro; subst;
          specialize (Hrm _ (or_intror Hres1_used)); intuition. }
    { destruct (DecidableTypeEx.Positive_as_DT.eq_dec res r1); subst.
      - rewrite 3!PMap.gss; reflexivity.
      - rewrite 3!PMap.gso; auto.
        + rewrite <- Hrs''.
          eapply match_regsets_get_2; eauto.
        + eapply rm_wf_neq_2_1'; eauto;
            apply reg_used_in_all_regs_list; auto; right; auto.
        + eapply rm_wf_neq_2_2'; eauto;
            apply reg_used_in_all_regs_list; auto; right; auto. }
  Qed.

(*   Fixpoint init_regs' *)
(*     (rm : PMap.t (reg * reg)) (vl: list val) (rl: list reg) {struct rl} *)
(*     : regset := *)
(*     match rl, vl with *)
(*     | r1 :: rs, v1 :: vs => *)
(*         let (r2, r3) := rm # r1 in *)
(*         (((init_regs' rm vs rs) # r1 <- v1) # r2 <- v1) # r3 <- v1 *)
(*     | _, _ => Regmap.init Vundef *)
(*     end. *)

(*   Lemma not_in_update_regset rm rs a params v : *)
(*     Forall (fun r => forall r1 r2 r3, In r1 params -> *)
(*                               rm # r1 = (r2, r3) -> *)
(*                               a <> r2 /\ a <> r3) params -> *)
(*     rm_wf rm params -> *)
(*     ~ In a params -> *)
(*     (update_regset rm rs # a <- v params) # a = v. *)
(*   Proof. *)
(*     induction params; simpl; intros Hneq Hwf Hnotin. *)
(*     { rewrite PMap.gss; reflexivity. } *)
(*     inv Hneq. *)
(*     destruct (rm # a0) eqn:Ha0. *)
(*     destruct (DecidableTypeEx.Positive_as_DT.eq_dec a0 a); subst. *)
(*     { intuition. } *)
(*     rewrite 2!PMap.gso; auto. *)
(*     - apply IHparams; auto. *)
(*       + eapply Forall_impl; eauto. *)
(*       + eapply rm_wf_cons; eauto. *)
(*     - apply H1 in Ha0; intuition. *)
(*     - apply H1 in Ha0; intuition. *)
(*   Qed. *)

(*   Lemma not_in_update_regset' rm rs a r params v : *)
(*     ~ In a params -> *)
(*     a <> r -> *)
(*     (update_regset rm (rs # a <- v) params) # r = (update_regset rm rs params) # r. *)
(*   Proof. *)
(*     revert a r. *)
(*     induction params; simpl; intros r0 r Hnotin Hneq; try contradiction. *)
(*     { rewrite PMap.gso; auto. } *)
(*     rename a into r1; rename r0 into a. *)
(*     destruct (rm # _) as [r2 r3] eqn:Hr1. *)
(*     destruct (DecidableTypeEx.Positive_as_DT.eq_dec r r3); subst. *)
(*     { rewrite 2!PMap.gss. *)
(*       apply IHparams; intuition. } *)
(*     rewrite PMap.gso; auto. *)
(*     destruct (DecidableTypeEx.Positive_as_DT.eq_dec r r2); subst. *)
(*     { rewrite PMap.gss. *)
(*       rewrite PMap.gso; auto. *)
(*       rewrite PMap.gss. *)
(*       apply IHparams; intuition. } *)
(*     rewrite 3!PMap.gso; auto. *)
(*   Qed. *)

  Lemma rm_wf_forall_neq rm params a :
    rm_wf rm (a :: params) ->
    Forall
      (fun _ : positive =>
         forall (r1 : positive),
           In r1 params ->
           a <> rm # r1)
      params.
  Proof.
    intros Hwf.
    apply Forall_forall; intros x Hx r1 Hin.
    symmetry.
    eapply rm_wf_neq_2_1'.
    { eauto. }
    { left; reflexivity. }
    { right; eauto. }
  Qed.

(*   Lemma update_regset_init_regs rm args params r : *)
(*     rm_wf rm params -> *)
(*     NoDup params -> *)
(*     (length params <= length args)%nat -> *)
(*     (update_regset rm (init_regs args params) params) # r = *)
(*       (init_regs' rm args params) # r. *)
(*   Proof. *)
(*     revert r args; induction params; intros r args Hwf Hnodup Hlen; simpl; auto. *)
(*     destruct (rm # a) as [b c] eqn:Ha. *)
(*     destruct args; simpl in *; try lia. *)
(*     inv Hnodup. *)
(*     pose proof (rm_wf_cons _ _ _ Hwf) as Hwf'. *)
(*     rewrite not_in_update_regset; auto. *)
(*     assert (Hb: b <> c). *)
(*     { intro; subst. *)
(*       destruct (Hwf a c c (in_eq _ _) Ha) as [Hnodup _]. *)
(*       inv Hnodup; inv H4; apply H5; left; reflexivity. } *)
(*     destruct (DecidableTypeEx.Positive_as_DT.eq_dec r b); subst. *)
(*     { rewrite PMap.gso; auto. *)
(*       rewrite PMap.gss. *)
(*       rewrite PMap.gso; auto. *)
(*       rewrite PMap.gss; reflexivity. } *)
(*     destruct (DecidableTypeEx.Positive_as_DT.eq_dec r c); subst. *)
(*     { rewrite 2!PMap.gss; reflexivity. } *)
(*     rewrite 4!PMap.gso; auto. *)
(*     destruct (DecidableTypeEx.Positive_as_DT.eq_dec r a); subst. *)
(*     { rewrite PMap.gss; apply not_in_update_regset; auto. *)
(*       eapply rm_wf_forall_neq; eauto. } *)
(*     rewrite PMap.gso; auto. *)
(*     rewrite not_in_update_regset'; auto. *)
(*     apply IHparams; auto; lia. *)
(*     eapply rm_wf_forall_neq; eauto. *)
(*   Qed. *)

(*   Lemma init_regs_init_regs' c rm args params a : *)
(*     Forall (fun r1 => forall r2 r3, *)
(*                 rm # r1 = (r2, r3) -> *)
(*                 a <> r2 /\ a <> r3) params -> *)
(*     rm_inv params c rm -> *)
(*     reg_used params c a -> *)
(*     (init_regs args params) # a = (init_regs' rm args params) # a. *)
(*   Proof. *)
(*     revert args a; induction params; intros args r Hall Hrm Hused; simpl; auto. *)
(*     destruct args; auto. *)
(*     inv Hall. *)
(*     destruct (rm # a) as [a2 a3] eqn:Ha. *)
(*     destruct (DecidableTypeEx.Positive_as_DT.eq_dec r a); subst. *)
(*     { rewrite PMap.gss. *)
(*       destruct (DecidableTypeEx.Positive_as_DT.eq_dec a a3); subst. *)
(*       { rewrite PMap.gss; reflexivity. } *)
(*       rewrite PMap.gso; auto. *)
(*       destruct (DecidableTypeEx.Positive_as_DT.eq_dec a a2); subst. *)
(*       { rewrite PMap.gss; reflexivity. } *)
(*       rewrite PMap.gso; auto. *)
(*       rewrite PMap.gss; reflexivity. } *)
(*     rewrite PMap.gso; auto. *)
(*     destruct (DecidableTypeEx.Positive_as_DT.eq_dec r a3); subst. *)
(*     { specialize (H1 a2 a3 eq_refl); intuition. } *)
(*     rewrite PMap.gso; auto. *)
(*     destruct (DecidableTypeEx.Positive_as_DT.eq_dec r a2); subst. *)
(*     { specialize (H1 a2 a3 eq_refl); intuition. } *)
(*     rewrite 2!PMap.gso; auto. *)
(*     apply IHparams; auto. *)
(*     eapply rm_inv_cons; eauto. *)
(*     destruct Hused as [Hin | Hused]. *)
(*     - inv Hin; try lia; left; auto. *)
(*     - right; auto. *)
(*   Qed. *)

  Definition in_dec (p : positive) (l : list positive)
    : { In p l } + { ~ In p l }.
  Proof.
    induction l; simpl.
    { right; intro; contradiction. }
    destruct IHl as [Hin | Hnotin].
    - left; right; assumption.
    - destruct (DecidableTypeEx.Positive_as_DT.eq_dec a p); subst.
      + left; left; reflexivity.
      + right; intros [?|H]; subst; congruence.
  Qed.

(*   Lemma init_regs'_r2 params c rm r1 r2 r3 args : *)
(*     rm_wf rm (all_regs_list params c) -> *)
(*     reg_used params c r1 -> *)
(*     rm # r1 = (r2, r3) -> *)
(*     (init_regs' rm args params) # r1 = (init_regs' rm args params) # r2. *)
(*   Proof. *)
(*     revert args r1 r2 r3; induction params; *)
(*       intros args r1 r2 r3 Hwf Hused Hr1; simpl; auto. *)
(*     destruct args; auto. *)
(*     destruct (rm # a) as [a2 a3] eqn:Ha. *)
(*     destruct (DecidableTypeEx.Positive_as_DT.eq_dec r1 a); subst. *)
(*     { rewrite Hr1 in Ha; inv Ha. *)
(*       rewrite 2!PMap.gso. *)
(*       2: { eapply rm_wf_neq_1_2; eauto. *)
(*            apply in_elements, Regset.union_2, in_pset_of_list; left; auto. } *)
(*       2: { eapply rm_wf_neq_1_3; eauto. *)
(*            apply in_elements, Regset.union_2, in_pset_of_list; left; auto. } *)
(*       rewrite PMap.gss. *)
(*       rewrite PMap.gso. *)
(*       2: { eapply rm_wf_neq_2_3; eauto. *)
(*            apply in_elements, Regset.union_2, in_pset_of_list; left; auto. } *)
(*       rewrite PMap.gss; reflexivity. } *)
(*     assert (Ha': In a (all_regs_list (a :: params) c)). *)
(*     { apply in_elements, Regset.union_2, in_pset_of_list; left; auto. } *)
(*     assert (Hr1': In r1 (all_regs_list (a :: params) c)). *)
(*     { apply reg_used_in_all_regs_list; auto. } *)
(*     rewrite !PMap.gso; auto. *)
(*     { eapply IHparams; eauto. *)
(*       - eapply rm_wf_antimonotone; eauto. *)
(*         intros r Hin. *)
(*         apply in_elements in Hin. *)
(*         apply in_elements. *)
(*         destruct (Regset.union_1 Hin) as [Hparams | Hc]. *)
(*         + apply Regset.union_2, in_pset_of_list; right. *)
(*           apply in_pset_of_list; auto. *)
(*         + apply Regset.union_3; auto. *)
(*       - destruct Hused as [[? | Hin] | Hused]; subst; try congruence. *)
(*         + left; auto. *)
(*         + right; auto. } *)
(*     - eapply rm_wf_neq_2_1'; eauto. *)
(*     - eapply rm_wf_neq_2_2'. *)
(*       4: { eauto. } *)
(*       4: { eauto. } *)
(*       eauto. auto. auto. auto. *)
(*     - eapply rm_wf_neq_2_3'. *)
(*       4: { eauto. } *)
(*       4: { eauto. } *)
(*       eauto. auto. auto. *)
(*     - symmetry; eapply rm_wf_neq_2_1'. *)
(*       4: { eauto. } *)
(*       4: { eauto. } *)
(*       eauto. auto. auto. *)
(*     - symmetry; eapply rm_wf_neq_3_1'. *)
(*       4: { eauto. } *)
(*       4: { eauto. } *)
(*       eauto. auto. auto. *)
(*   Qed. *)

(*   Lemma init_regs'_r3 params c rm r1 r2 r3 args : *)
(*     rm_wf rm (all_regs_list params c) -> *)
(*     reg_used params c r1 -> *)
(*     rm # r1 = (r2, r3) -> *)
(*     (init_regs' rm args params) # r1 = (init_regs' rm args params) # r3. *)
(*   Proof. *)
(*     revert args r1 r2 r3; induction params; *)
(*       intros args r1 r2 r3 Hwf Hused Hr1; simpl; auto. *)
(*     destruct args; auto. *)
(*     destruct (rm # a) as [a2 a3] eqn:Ha. *)
(*     destruct (DecidableTypeEx.Positive_as_DT.eq_dec r1 a); subst. *)
(*     { rewrite Hr1 in Ha; inv Ha. *)
(*       rewrite 2!PMap.gso. *)
(*       rewrite 2!PMap.gss; reflexivity. *)
(*       - eapply rm_wf_neq_1_2; eauto. *)
(*         apply in_elements, Regset.union_2, in_pset_of_list; left; auto. *)
(*       - eapply rm_wf_neq_1_3; eauto. *)
(*         apply in_elements, Regset.union_2, in_pset_of_list; left; auto. } *)
(*     assert (Ha': In a (all_regs_list (a :: params) c)). *)
(*     { apply in_elements, Regset.union_2, in_pset_of_list; left; auto. } *)
(*     assert (Hr1': In r1 (all_regs_list (a :: params) c)). *)
(*     { apply reg_used_in_all_regs_list; auto. } *)
(*     rewrite !PMap.gso; auto. *)
(*     { eapply IHparams; eauto. *)
(*       - eapply rm_wf_antimonotone; eauto. *)
(*         intros r Hin. *)
(*         apply in_elements in Hin. *)
(*         apply in_elements. *)
(*         destruct (Regset.union_1 Hin) as [Hparams | Hc]. *)
(*         + apply Regset.union_2, in_pset_of_list; right. *)
(*           apply in_pset_of_list; auto. *)
(*         + apply Regset.union_3; auto. *)
(*       - destruct Hused as [[? | Hin] | Hused]; subst; try congruence. *)
(*         + left; auto. *)
(*         + right; auto. } *)
(*     - eapply rm_wf_neq_3_1'; eauto. *)
(*     - symmetry; eapply rm_wf_neq_2_3'. *)
(*       4: { eauto. } *)
(*       4: { eauto. } *)
(*       eauto. auto. auto. *)
(*     - symmetry; eapply rm_wf_neq_3_3'. *)
(*       4: { eauto. } *)
(*       4: { eauto. } *)
(*       eauto. auto. auto. auto. *)
(*     - symmetry; eapply rm_wf_neq_2_1'. *)
(*       4: { eauto. } *)
(*       4: { eauto. } *)
(*       eauto. auto. auto. *)
(*     - symmetry; eapply rm_wf_neq_3_1'. *)
(*       4: { eauto. } *)
(*       4: { eauto. } *)
(*       eauto. auto. auto. *)
(*   Qed. *)

(*   Lemma rm_inv_init_regs c rm args params : *)
(*     rm_inv params c rm -> *)
(*     rm_wf rm (all_regs_list params c) -> *)
(*     NoDup params -> *)
(*     (length params <= length args)%nat -> *)
(*     match_regsets params c rm (init_regs args params) *)
(*       (update_regset rm (init_regs args params) params). *)
(*   Proof. *)
(*     intros Hrm Hwf Hnodup Hlen. *)
(*     intros r1 r2 r3 Hr1 Hused. *)
(*     repeat split. *)
(*     - rewrite update_regset_init_regs; auto. *)
(*       2: { eapply rm_wf_antimonotone; eauto. *)
(*            intros x Hx. *)
(*            apply in_elements, Regset.union_2, in_pset_of_list; auto. } *)
(*       eapply init_regs_init_regs'; eauto. *)
(*       apply Forall_forall. *)
(*       intros x1 Hin' x2 x3 Hx1. *)
(*       destruct (Hwf x1 x2 x3 (param_in_all_regs_list _ _ _ Hin') Hx1) *)
(*         as [Hnodup' H]. *)
(*       split; intro; subst. *)
(*       + destruct (Hwf x2 r2 r3 (reg_used_in_all_regs_list _ _ _ Hused) Hr1) *)
(*           as [Hnodup'' H']. *)
(*         destruct (DecidableTypeEx.Positive_as_DT.eq_dec x1 x2); subst. *)
(*         { inv Hnodup'; apply H2; left; reflexivity. } *)
(*         specialize (H' x1 x2 x3 (param_in_all_regs_list _ _ _ Hin') *)
(*                       (RelationClasses.neq_Symmetric _ _ n) Hx1). *)
(*         inv H'; apply H2; right; right; right; left; reflexivity. *)
(*       + destruct (Hwf x3 r2 r3 (reg_used_in_all_regs_list _ _ _ Hused) Hr1) *)
(*           as [Hnodup'' H']. *)
(*         destruct (DecidableTypeEx.Positive_as_DT.eq_dec x1 x3); subst. *)
(*         { inv Hnodup'; apply H2; right; left; reflexivity. } *)
(*         specialize (H' x1 x2 x3 (param_in_all_regs_list _ _ _ Hin') *)
(*                       (RelationClasses.neq_Symmetric _ _ n) Hx1). *)
(*         inv H'; apply H2; right; right; right; right; left; reflexivity. *)
(*     - rewrite update_regset_init_regs; auto. *)
(*       2: { eapply rm_wf_antimonotone; eauto. *)
(*            intros x Hx. *)
(*            apply in_elements, Regset.union_2, in_pset_of_list; auto. } *)
(*       erewrite <- init_regs'_r2; eauto. *)
(*       eapply init_regs_init_regs'; eauto. *)
(*       apply Forall_forall. *)
(*       intros x1 Hin' x2 x3 Hx1. *)
(*       destruct (Hwf x1 x2 x3 (param_in_all_regs_list _ _ _ Hin') Hx1) *)
(*         as [Hnodup' H]. *)
(*       split; intro; subst. *)
(*       + destruct (Hwf x2 r2 r3 (reg_used_in_all_regs_list _ _ _ Hused) Hr1) *)
(*           as [Hnodup'' H']. *)
(*         destruct (DecidableTypeEx.Positive_as_DT.eq_dec x1 x2); subst. *)
(*         { inv Hnodup'; apply H2; left; reflexivity. } *)
(*         specialize (H' x1 x2 x3 (param_in_all_regs_list _ _ _ Hin') *)
(*                       (RelationClasses.neq_Symmetric _ _ n) Hx1). *)
(*         inv H'; apply H2; right; right; right; left; reflexivity. *)
(*       + destruct (Hwf x3 r2 r3 (reg_used_in_all_regs_list _ _ _ Hused) Hr1) *)
(*           as [Hnodup'' H']. *)
(*         destruct (DecidableTypeEx.Positive_as_DT.eq_dec x1 x3); subst. *)
(*         { inv Hnodup'; apply H2; right; left; reflexivity. } *)
(*         specialize (H' x1 x2 x3 (param_in_all_regs_list _ _ _ Hin') *)
(*                       (RelationClasses.neq_Symmetric _ _ n) Hx1). *)
(*         inv H'; apply H2; right; right; right; right; left; reflexivity. *)
(*     - rewrite update_regset_init_regs; auto. *)
(*       2: { eapply rm_wf_antimonotone; eauto. *)
(*            intros x Hx. *)
(*            apply in_elements, Regset.union_2, in_pset_of_list; auto. } *)
(*       erewrite <- init_regs'_r3; eauto. *)
(*       eapply init_regs_init_regs'; eauto. *)
(*       apply Forall_forall. *)
(*       intros x1 Hin' x2 x3 Hx1. *)
(*       destruct (Hwf x1 x2 x3 (param_in_all_regs_list _ _ _ Hin') Hx1) *)
(*         as [Hnodup' H]. *)
(*       split; intro; subst. *)
(*       + destruct (Hwf x2 r2 r3 (reg_used_in_all_regs_list _ _ _ Hused) Hr1) *)
(*           as [Hnodup'' H']. *)
(*         destruct (DecidableTypeEx.Positive_as_DT.eq_dec x1 x2); subst. *)
(*         { inv Hnodup'; apply H2; left; reflexivity. } *)
(*         specialize (H' x1 x2 x3 (param_in_all_regs_list _ _ _ Hin') *)
(*                       (RelationClasses.neq_Symmetric _ _ n) Hx1). *)
(*         inv H'; apply H2; right; right; right; left; reflexivity. *)
(*       + destruct (Hwf x3 r2 r3 (reg_used_in_all_regs_list _ _ _ Hused) Hr1) *)
(*           as [Hnodup'' H']. *)
(*         destruct (DecidableTypeEx.Positive_as_DT.eq_dec x1 x3); subst. *)
(*         { inv Hnodup'; apply H2; right; left; reflexivity. } *)
(*         specialize (H' x1 x2 x3 (param_in_all_regs_list _ _ _ Hin') *)
(*                       (RelationClasses.neq_Symmetric _ _ n) Hx1). *)
(*         inv H'; apply H2; right; right; right; right; left; reflexivity. *)
(*   Qed. *)

  Lemma copy_allR_params_used_in_code re rm c params pc succ :
    copy_allR re rm c params pc succ ->
    Forall (reg_used_in_code c) params.
  Proof.
    induction 1.
    { constructor. }
    constructor; auto.
    inv H.
    unfold smove in *.
    unfold reg_used_in_code.
    destruct (re r) eqn:Hr; inv H1; eexists; eexists; split;
      eauto; constructor; left; reflexivity.
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
    destruct (DecidableTypeEx.Positive_as_DT.eq_dec r a); subst.
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

  Lemma match_regsets_extra params c rm rs rs' l :
    rm_wf rm (l ++ all_regs_list params c) ->
    match_regsets params c rm rs rs' ->
    match_regsets params c rm rs (update_regset rm rs' l).
  Proof.
    revert rs rs'.
    induction l; simpl; auto; intros rs rs' Hwf Hmatch.
    apply IHl.
    { eapply rm_wf_antimonotone; eauto.
      intros r Hin; right; auto. }
    intros r1 Hused.
    specialize (Hmatch r1 Hused).
    destruct Hmatch as [Hmatch1 Hmatch2].
    destruct (DecidableTypeEx.Positive_as_DT.eq_dec r1 a); subst.
    { rewrite PMap.gso, PMap.gss; auto.
      eapply rm_wf_neq_1_2; eauto; left; reflexivity. }
    { assert (Hr1: In r1 (l ++ all_regs_list params c)).
      { apply in_or_app; right.
        destruct Hused as [Hin | Hused].
        - apply param_in_all_regs_list; auto.
        - apply reg_used_in_code_in_all_regs_list; auto. }
      rewrite 2!PMap.gso; auto.
      - eapply rm_wf_neq_2_2; eauto.
        + left; reflexivity.
        + right; auto.
      - symmetry; eapply rm_wf_neq_2_1'; eauto.
        + right; auto.
        + left; reflexivity. }
  Qed.

  Lemma update_regset_app rm rs l1 l2 :
    update_regset rm rs (l1 ++ l2) = update_regset rm (update_regset rm rs l1) l2.
  Proof. revert rs; induction l1; intros rs; simpl; auto. Qed.

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
            eapply regular_eval_operation; eauto.
            eapply res2_not_in_args1 with (l := fun_regs_list f);
              eauto; try reg_used1; reg_used2. }
          { apply star_refl. }
          { reflexivity. }
        * reflexivity.
      + econstructor; eauto.
        { eapply wt_exec_Iop; eauto.
          eapply wt_instr_at; eauto. }
        * econstructor; eauto.
        * intros r Hused.
          destruct (DecidableTypeEx.Positive_as_DT.eq_dec r res); subst.
          { split.
            - rewrite 2!PMap.gss; reflexivity.
            - rewrite PMap.gss, PMap.gso.
              2: { symmetry; eapply rm_wf_neq_1_2; eauto; reg_used1. }
              rewrite PMap.gss; reflexivity. }
          { assert (Hresused: reg_used_in_code c res).
            { eexists; eexists; split; eauto; apply reg_used_Iop_res. }
            split.
            - rewrite 3!PMap.gso; auto.
              2: { intro HC; subst.
                   specialize (RM_INV _ (or_intror Hresused)).
                   destruct Hused; intuition. }
              specialize (REGS _ Hused); intuition.
            - rewrite 2!PMap.gso; auto.
              2: { intro HC; subst.
                   specialize (RM_INV _ Hused); intuition. }
              rewrite PMap.gso.
              2: { eapply rm_wf_neq_2_2 with (r := res); eauto; try reg_used1.
                   apply reg_used_in_all_regs_list; auto. }
              specialize (REGS _ Hused); intuition. }

    - (* exec_Iload *)
      inv Hmatch.
      pose proof FUN as Hmatch_function.
      inv FUN; simpl in *.
      set (f := {| fn_sig := sig
                ; fn_params := params
                ; fn_stacksize := stacksize
                ; fn_code := c
                ; fn_entrypoint := entrypoint |}).
      pose proof H as Hcode.
      specialize (CODE pc (Iload chunk addr args dst pc') H); inv CODE.
      assert (Hargs: Forall (reg_used_in_code c) args).
      { apply Forall_forall; intros x Hx;
          eexists; eexists; split; eauto; constructor; auto. }
      eapply check_regsR_star_step with (m:=m) in CHK_ARGS; eauto.
      assert (Hty: Val.has_type v (re dst)).
      { inv WT_FN.
        simpl in *.
        specialize (wt_instrs _ _ Hcode).
        inv wt_instrs.
        simpl in *.
        rewrite H8.
        destruct a; inv H1.
        eapply Memory.Mem.load_type; eauto. }
      eexists; split.
      + eapply star_plus_trans.
        { apply CHK_ARGS. }
        2: { reflexivity. }
        econstructor.
        3: { rewrite Events.E0_right; reflexivity. }
        { eapply exec_Iload; eauto.
          eapply match_regsets_eval_addressing; eauto. }
        apply star_one.
        eapply smoveR_step in MOVE; eauto.
        rewrite PMap.gss; auto.
      + simpl.
        econstructor; eauto.
        intro r.
        destruct (peq dst r); subst.
        * rewrite PMap.gss; auto.
        * rewrite PMap.gso; auto.
        * eapply match_regsets_update; eauto.
          eexists; eexists; split; eauto; solve [constructor; auto].

    - (* exec_Istore *)
      inv Hmatch; inv FUN; simpl in *.
      set (f := {| fn_sig := sig
                 ; fn_params := params
                 ; fn_stacksize := stacksize
                 ; fn_code := c
                 ; fn_entrypoint := entrypoint |}).
      pose proof CODE as Hcode.
      specialize (CODE pc (Istore chunk addr args src pc') H); inv CODE.
      eapply check_regsR_star_step with (m:=m) in CHK_REGS; eauto.
      eexists; split.
      + eapply star_plus_trans.
        { apply CHK_REGS. }
        2: { reflexivity. }
        econstructor.
        2: { apply star_refl. }
        2: { rewrite Events.E0_right; reflexivity. }
        eapply exec_Istore; simpl; eauto.
        * erewrite <- rs_map_ext; eauto.
          eapply match_regsets_eval_addressing; eauto.
          apply Forall_forall; intros r Hr; eexists; eexists; split; eauto.
          constructor; auto.
        * eapply match_regsets_storev; eauto.
          eexists; eexists; split; eauto; solve [constructor].
      + econstructor; eauto.
        * econstructor; eauto.

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
      eapply check_regsR_star_step with (m:=m) in CHK_ARGS; eauto.
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
        { apply CHK_ARGS. }
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
            2: { reflexivity. }
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
          rewrite <- H9.
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
      eapply check_regsR_star_step with (m:=m) in CHK_ARGS; eauto.
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
        { apply CHK_ARGS. }
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
            2: { reflexivity. }
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
        eapply check_regsR_star_step with (m:=m) in CHK_ARGS; eauto.
        eexists; split.
        + eapply star_plus_trans.
          { apply CHK_ARGS. }
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
          econstructor; eauto. }
      { (* With result register *)
        eapply check_regsR_star_step with (m:=m) in CHK_ARGS; eauto.
        assert (Hty: Val.has_type vres (re res0)).
        { inv WT_FN.
          simpl in *.
          specialize (wt_instrs _ _ Hcode).
          inv wt_instrs.
          simpl in *.
          rewrite H7.
          eapply external_call_well_typed; eauto. }
        eexists; split.
        + eapply star_plus_trans.
          { apply CHK_ARGS. }
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
                eapply match_regsets_get; eauto.
                right; eexists; eexists; split; eauto.
                constructor.
                apply in_regs_of_builtin_args_exists_in_builtin_arg.
                apply Exists_exists.
                eexists; split; eauto. }
            { eapply external_call_symbols_preserved; eauto.
              apply senv_preserved. } }
          apply star_one.
          eapply smoveR_step in MOVE; eauto.
          simpl; rewrite PMap.gss; auto.
        + simpl; econstructor; eauto.
          intro r.
          destruct (DecidableTypeEx.Positive_as_DT.eq_dec res0 r); subst.
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
      eapply check_regsR_star_step with (m:=m) in CHK_ARGS; eauto.
      eexists; split.
      + eapply star_plus_trans.
        { apply CHK_ARGS. }
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
      eapply checkR_step with (rs := rs') in CHK.
      eexists; split.
      + econstructor.
        { apply CHK. }
        2: { reflexivity. }
        apply star_one.
        eapply exec_Ijumptable; eauto.
          erewrite <- match_regsets_get; eauto; right; auto.
      + econstructor; eauto.

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
        assert (Hused: reg_used_in_code c arg).
        { eexists; eexists; split; eauto; constructor. }
        eapply checkR_step with (rs := rs') in CHK.
        eexists; split.
        * econstructor.
          { apply CHK. }
          2: { reflexivity. }
          apply star_one.
          eapply exec_Ireturn; eauto.
        * simpl; erewrite match_regsets_get; eauto.
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
          3: { eauto. }
          { apply Forall_forall.
            intros x Hx.
            inv WT; subst; simpl in *.
            rewrite <- wt_params in WT_ARGS.
            apply wt_regset_init_regs; auto. }
          { eapply rm_wf_antimonotone; eauto.
            intros r Hin.
            unfold all_regs_list.
            rewrite <- app_app' in Hin.
            apply in_app_or in Hin.
            destruct Hin as [Hin | Hin].
            - apply in_elements, Regset.union_2, in_pset_of_list; auto.
            - rewrite Forall_forall in COPY_REGS_OK; auto. }
        * reflexivity.
      + econstructor; eauto.
        * apply wt_init_regs.
          inv WT; simpl in *.
          rewrite wt_params; auto.
        * econstructor; eauto.
        * rewrite <- app_app'.
          rewrite update_regset_app.
          apply match_regsets_extra.
          { eapply rm_wf_antimonotone; eauto.
            rewrite Forall_forall in COPY_REGS_OK.
            intros r Hin.
            apply in_app_or in Hin; destruct Hin as [Hin|Hin]; auto. }
          (* apply rm_inv_init_regs; auto. *)
          (* { inv WT; simpl in *; apply list_norepet_nodup; auto. } *)
          (* { inv WT; simpl in *. *)
          (*   apply has_type_list_length in WT_ARGS. *)
          (*   rewrite <- wt_params in WT_ARGS. *)
          (*   rewrite list_length_map in WT_ARGS. *)
          (*   rewrite WT_ARGS; reflexivity. } *)
          admit.

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
        * eapply smoveR_step with (rs := trs # res <- vres) in H8.
          2: { rewrite PMap.gss; rewrite WT_RES0; auto. }
          apply star_one; eapply H8.
        * reflexivity.
      + econstructor; eauto.
        * intro r.
          destruct (DecidableTypeEx.Positive_as_DT.eq_dec r res); subst.
          { rewrite PMap.gss; rewrite WT_RES0; auto. }
          rewrite PMap.gso; auto.
        * eapply match_regsets_update; eauto.
          inv FUN; auto.
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
      rename t into rm.
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
    eapply forward_simulation_plus; simpl.
    - apply senv_preserved.
    - intros. exploit transf_initial_states; eauto.
    - intros s1 s2 r Hmatch Hfin.
      eapply transf_final_states; eauto; intuition.
    - intros s1 t s1' Hstep s2 Hmatch.
      eapply step_simulation; eauto; intuition.
  Qed.

End PRESERVATION.
