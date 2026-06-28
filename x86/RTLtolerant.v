Require Import
  AST
  Behaviors
  Builtins
  SharedFaultPolicy
  FaultPolicy
  CompCertZapUtils
  Builtins2
  Coqlib
  Events
  Globalenvs
  Linking
  Maps
  ProofLiveness
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

Definition match_rs (live : Regset.t)
  (col : reg -> color) (faulted : bool) (rs1 rs2 : regset) : Prop :=
  if faulted then
    exists c, is_basic c /\
           forall r, Regset.In r live -> col r <> c -> Val.lessdef (rs1 # r) (rs2 # r)
  else
    forall r, Val.lessdef (rs1 # r) (rs2 # r).

Definition match_rs_upto (res : reg) (live : Regset.t)
  (col : reg -> color) (faulted : bool) (rs1 rs2 : regset) : Prop :=
  if faulted then
    exists c, is_basic c /\
           forall r, r <> res ->
                Regset.In r live -> col r <> c -> Val.lessdef (rs1 # r) (rs2 # r)
  else
    forall r, r <> res -> Val.lessdef (rs1 # r) (rs2 # r).

Lemma match_rs_match_rs_upto live res col faulted rs1 rs2 :
  match_rs live col faulted rs1 rs2 ->
  match_rs_upto res live col faulted rs1 rs2.
Proof.
  unfold match_rs, match_rs_upto; intro RS.
  destruct faulted; auto.
  destruct RS as (c & Hc & RS).
  exists c; split; auto.
Qed.

Lemma match_rs_weaken s1 s2 col faulted rs1 rs2 :
  Regset.Subset s1 s2 ->
  match_rs s2 col faulted rs1 rs2 ->
  match_rs s1 col faulted rs1 rs2.
Proof.
  unfold match_rs; intros Hsub RS.
  destruct faulted.
  - destruct RS as (c & Hc & RS).
    exists c; split; [auto|].
    intros r Hr Hcol. apply RS; auto.
  - auto.
Qed.

(** Propagate match_rs from predecessor to successor with color change.
    For r in s1 (successor's live set), if:
    - s1 <= s2 (predecessor's live set)
    - For r in s_mid, col1 r = col2 r
    - s1 <= s_mid
    Then match_rs s2 col1 faulted rs1 rs2 implies match_rs s1 col2 faulted rs1 rs2. *)

Lemma match_rs_color_weaken s1 s2 s_mid col1 col2 faulted rs1 rs2 :
  Regset.Subset s1 s2 ->
  Regset.Subset s1 s_mid ->
  (forall r, Regset.In r s_mid -> col1 r = col2 r) ->
  match_rs s2 col1 faulted rs1 rs2 ->
  match_rs s1 col2 faulted rs1 rs2.
Proof.
  unfold match_rs; intros Hsub1 Hsub2 Hcol RS.
  destruct faulted.
  - destruct RS as (c & Hc & RS).
    exists c; split; [auto|].
    intros r Hr Hcol_ne.
    apply RS.
    + apply Hsub1; auto.
    + rewrite Hcol; auto.
  - auto.
Qed.


Section match_states.

  (** When a fault has occurred elsewhere and regsets [rs1] and [rs2]
      are unchanged, they still match. *)
  Lemma match_rs_upto_fault res live col (pc : node) (rs1 rs2 : regset) :
    match_rs_upto res live (col pc) false rs1 rs2 ->
    match_rs_upto res live (col pc) true rs1 rs2.
  Proof. intro H; exists Red; split; auto; constructor. Qed.

  Inductive match_stackframes (faulted : bool)
    : RTL.stackframe -> RTL.stackframe -> Prop :=
  | match_stackframes_Stackframe :
    forall col res f sp pc rs1 rs2 live
      (WC_FUN: wc_function col f)
      (RS_COMPAT: rs_compat rs1 rs2)
      (LIVE: ProofLiveness.analyze f = Some live)
      (RS: match_rs_upto res (ProofLiveness.transfer f pc (live !! pc)) (col pc) faulted rs1 rs2),
      match_stackframes faulted
        (Stackframe res f sp pc rs1)
        (Stackframe res f sp pc rs2).

  (** When a fault has occurred elsewhere and stackframes [sf1] and
      [sf2] are unchanged, they still match. *)
  Lemma match_stackframes_fault (sf1 sf2 : RTL.stackframe) :
    match_stackframes false sf1 sf2 ->
    match_stackframes true sf1 sf2.
  Proof.
    intro H; inv H.
    econstructor; eauto.
    apply match_rs_upto_fault; auto.
  Qed.

  (** When a fault hasn't occurred, equality should hold between all
      registers. When a fault has occurred, it should hold between all
      registers except those of the affected color.

      [RS_COMPAT] ensures data operations remain well-defined after a
      fault occurs (else they could cause the faulty semantics to get
      stuck). *)
  Inductive match_states : bool -> RTL.state -> fstate -> Prop :=
  | match_states_State :
    forall col stk1 stk2 f sp pc rs1 rs2 m1 m2 (b : bool) live
      (LIVE: ProofLiveness.analyze f = Some live)
      (STK: Forall2 (match_stackframes b) stk1 stk2)
      (WC_FUN: wc_function col f)
      (RS_COMPAT: rs_compat rs1 rs2)
      (RS: match_rs (ProofLiveness.transfer f pc (live !! pc)) (col pc) b rs1 rs2)
      (MEM: Memory.Mem.extends m1 m2),
      match_states b (State stk1 f sp pc rs1 m1)
                   {| fs_state := State stk2 f sp pc rs2 m2; fault := b |}
  | match_states_Callstate :
    forall stk1 stk2 fd args1 args2 m1 m2 b
      (STK: Forall2 (match_stackframes b) stk1 stk2)
      (WC_FD: wc_fundef fd)
      (LESSDEF: Forall2 Val.lessdef args1 args2)
      (MEM: Memory.Mem.extends m1 m2),
      match_states b (Callstate stk1 fd args1 m1)
                   {| fs_state := Callstate stk2 fd args2 m2; fault := b |}
  | match_state_Returnstate :
    forall stk1 stk2 v1 v2 m1 m2 b
      (STK: Forall2 (match_stackframes b) stk1 stk2)
      (LESSDEF: Val.lessdef v1 v2)
      (MEM: Memory.Mem.extends m1 m2),
      match_states b (Returnstate stk1 v1 m1)
                   {| fs_state := Returnstate stk2 v2 m2; fault := b |}.

End match_states.

Lemma find_funct_ptr_wc_fundef (p : RTL.program) b fd :
  wc_program p ->
  Genv.find_funct_ptr (Genv.globalenv p) b = Some fd ->
  wc_fundef fd.
Proof.
  intros Hwc Hfind.
  destruct fd; try constructor.
  apply Genv.find_funct_ptr_inversion in Hfind.
  destruct Hfind as [id Hin].
  apply Hwc in Hin; auto.
Qed.

Lemma init_match_states_refl p s :
  wc_program p ->
  RTL.initial_state p s ->
  match_states false s {| fs_state := s; fault := false |}.
Proof.
  intros Hwc Hinit; inv Hinit.
  econstructor; auto.
  - eapply find_funct_ptr_wc_fundef; eauto.
  - apply Memory.Mem.extends_refl.
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

  Ltac inv_wc :=
    match goal with
    | [ H : wc_function _ _ |- _ ] => inv H
    end;
    match goal with
    | [ Hwc : wc_code _ _ _, Hpc : (fn_code _) ! _ = Some _ |- _ ] =>
        let Hpc' := fresh "Hpc" in
        pose proof Hpc as Hpc';
        apply Hwc in Hpc'; inv Hpc'; try congruence
    end.

  (** Unify the two [live] variables from [match_states] and [wc_function].
      Call AFTER [inv_wc] when step_simulation needs [Hin_live] to refer
      to the same [live] used in the [wc_code] hypotheses. *)
  Ltac unify_live :=
    match goal with
    | [ H1 : ProofLiveness.analyze ?f = Some ?l1,
        H2 : ProofLiveness.analyze ?f = Some ?l2 |- _ ] =>
        match l1 with
        | l2 => idtac  (* already unified *)
        | _ => let Heq := fresh in
               assert (Heq : l1 = l2) by congruence;
               subst l2
        end
    end.

  (* Lemma wc_col_succ_exists f col pc i r succ : *)
  (*   (fn_code f) ! pc = Some i -> *)
  (*   res_of_instruction i = Some r -> *)
  (*   succ_of_instruction i = Some succ -> *)
  (*   wc_function col f -> *)
  (*   exists c, col succ r = Some c. *)
  (* Proof. *)
  (*   intros Hpc Hr Hsucc Hwc. *)
  (*   inv_wc; simpl in *; try congruence; inv Hr; inv Hsucc; *)
  (*     try solve [exists White; auto]; try solve [eexists; eauto]. *)
  (*   - inv H0; eexists; eauto. *)
  (*   - destruct bres; simpl in *; try congruence. *)
  (*     inv H6; exists White; auto. *)
  (* Qed. *)

  Lemma res_exists_succ i r :
    res_of_instruction i = Some r ->
    exists succ, succ_of_instruction i = Some succ.
  Proof.
    intro Hres; destruct i; simpl in *;
      try congruence; eexists; eauto.
  Qed.

  Lemma step_succ {VT: Builtins2.vote_type} {vsem: Builtins2.VoteSemantics VT}
    stk f sp pc rs m t stk' sp' pc' rs' m' i :
    RTL.step (Genv.globalenv prog) (State stk f sp pc rs m)
      t (State stk' f sp' pc' rs' m') ->
    f.(fn_code) ! pc = Some i ->
    In pc' (succs_of_instruction i).
  Proof.
    intros Hstep Hpc.
    inv Hstep; rewrite H6 in Hpc; inv Hpc; simpl; auto.
    - destruct b; auto.
    - eapply list_nth_z_in; eauto.
  Qed.

  Lemma maybe_zap_preserves_match_states b s1 stk f sp pc rs m s' s'' b' s1' t :
    match_states b s1 {| fs_state := State stk f sp pc rs m; fault := b |} ->
    maybe_zap f pc s' b s'' b' ->
    Step (@RTL.semantics Three VoteSemantics_Three prog) s1 t s1' ->
    match_states b s1' {| fs_state := s'; fault := b |} ->
    match_states b' s1' {| fs_state := s''; fault := b' |}.
  Proof.
    intros Hmatch Hzap Hstep Hmatch'.
    inv Hzap; auto.
    inv Hmatch'.
    econstructor; eauto.
    - apply forall2_match_stackframes_fault; auto.
    - intro x.
      destruct (peq x r); subst.
      + rewrite Regmap.gss.
        eapply val_compat_trans; eauto.
      + rewrite Regmap.gso; auto.
    - unfold match_rs in *.
      assert (Hc: is_basic (col pc' r)).
      { pose proof H0 as Hop.
        inv Hmatch.
        eapply step_succ in Hstep; eauto.
        clear WC_FUN0.
        inv_wc; simpl in *; try congruence; inv H2; inv Hstep; try contradiction.
        all: first [ assumption
                   | unfold builtin_can_fault in H1; congruence
                   | exfalso; inv H3; vm_compute in H1; discriminate ]. }
      exists (col pc' r); split; auto.
      intros x Hx.
      destruct (peq x r); subst; try congruence.
      rewrite Regmap.gso; auto.
  Qed.

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
    inv Hmatch; inv STK; inv LESSDEF; constructor.
  Qed.


  Ltac inv_rs :=
    match goal with
    | [ RS : exists c : color, is_basic c /\ _ |- _ ] =>
        destruct RS as (c & Hc & RS)
    | [ RS : match_rs _ _ true _ _ |- _ ] =>
        unfold match_rs in RS; destruct RS as (c & Hc & RS)
    end.

  (** Tactic to apply RS with automatic Regset.In resolution *)
  Ltac apply_RS :=
    match goal with
    | [ RS : forall r, Regset.In r _ -> _ -> Val.lessdef _ _ |- _ ] =>
        apply RS;
        [ first [ assumption
                | eauto using args_in_transfer_iop, args_in_transfer_iload,
                              args_in_transfer_istore, src_in_transfer_istore,
                              args_in_transfer_icall, ros_in_transfer_icall,
                              args_in_transfer_itailcall, ros_in_transfer_itailcall,
                              args_in_transfer_icond, arg_in_transfer_ijumptable,
                              args_in_transfer_ibuiltin, optarg_in_transfer_ireturn,
                              live_in_transfer_iop, live_in_transfer_iload,
                              live_in_transfer_istore, live_in_transfer_icall,
                              live_in_transfer_icond, live_in_transfer_ijumptable,
                              live_in_transfer_ibuiltin,
                              succ_in_transfer_iop, succ_in_transfer_iload,
                              succ_in_transfer_istore, succ_in_transfer_icall,
                              succ_in_transfer_icond, succ_in_transfer_ijumptable,
                              succ_in_transfer_ibuiltin,
                              transfer_succ_subset ]
        | ]
    end.


  Ltac inv_Forall :=
    repeat match goal with
      | [H : Forall _ (_ :: _) |- _] => inv H
      end.

  Ltac inv_stk :=
    match goal with
    | [ H : Forall2 (match_stackframes false)
              (Stackframe ?res ?f ?sp ?pc ?rs :: ?s) ?stk2 |- _ ] =>
        inv H
    end.

  Lemma known_builtin_sem_Three_Two b vargs m t v m' :
    @known_builtin_sem Three VoteSemantics_Three b (Genv.globalenv prog) vargs m t v m' ->
    exists v',
      @known_builtin_sem Two VoteSemantics_Two b (Genv.globalenv prog) vargs m t v' m'.
  Proof.
    intro H; inv H.
    destruct b; simpl in *.
    - exists v; constructor; auto.
    - exists v; constructor; auto.
    - destruct b; simpl in *;
        repeat (destruct vargs; try congruence);
        destruct v0; inv H0; eexists; eexists; simpl; simpl;
        simpl; try repeat eexists; try rewrite H1; reflexivity.
  Qed.

  Lemma known_builtin_sem_Three_Two' b vargs m t v m' :
    @known_builtin_sem Three VoteSemantics_Three b (Genv.globalenv prog) vargs m t v m' ->
    exists v',
      @known_builtin_sem Two VoteSemantics_Two b (Genv.globalenv prog) vargs m t v' m' /\
        Val.lessdef v v'.
  Proof.
    intro H; inv H.
    destruct b; simpl in *.
    - exists v; split; constructor; auto.
    - exists v; split; constructor; auto.
    - destruct b; simpl in *;
        repeat (destruct vargs; try congruence);
        destruct v0; inv H0; eexists; split; try solve[constructor; simpl; auto];
        try solve [constructor; simpl; destruct Archi.ptr64; auto];
        apply vote3_lessdef_vote.
  Qed.
    
  Lemma builtin_or_external_sem_Three_Two name sg vargs m t v m' :
    @builtin_or_external_sem Three VoteSemantics_Three
      name sg (Genv.globalenv prog) vargs m t v m' ->
    exists v', @builtin_or_external_sem Two VoteSemantics_Two
            name sg (Genv.globalenv prog) vargs m t v' m'.
  Proof.
    unfold builtin_or_external_sem.
    intro Hsem.
    destruct (Builtins.lookup_builtin_function _ _) eqn:Hlookup.
    - unfold Builtins.lookup_builtin_function in *.
      simpl in *.
      destruct (string_dec name _ && signature_eq sg _%asttyp);
        eapply known_builtin_sem_Three_Two; eauto.
    - eexists; eauto.
  Qed.

  Lemma builtin_or_external_sem_Three_Two' name sg vargs m t v m' :
    @builtin_or_external_sem Three VoteSemantics_Three
      name sg (Genv.globalenv prog) vargs m t v m' ->
    exists v', @builtin_or_external_sem Two VoteSemantics_Two
            name sg (Genv.globalenv prog) vargs m t v' m' /\ Val.lessdef v v'.
  Proof.
    unfold builtin_or_external_sem.
    intro Hsem.
    destruct (Builtins.lookup_builtin_function _ _) eqn:Hlookup.
    - unfold Builtins.lookup_builtin_function in *.
      simpl in *.
      destruct (string_dec name _ && signature_eq sg _%asttyp);
        eapply known_builtin_sem_Three_Two'; eauto.
    - eexists; eauto.
  Qed.

  Lemma external_call_Three_Two' ef vargs m t v m' :
    @external_call Three VoteSemantics_Three
      ef (Genv.globalenv prog) vargs m t v m' ->
    exists v', @external_call Two VoteSemantics_Two
            ef (Genv.globalenv prog) vargs m t v' m' /\ Val.lessdef v v'.
  Proof.
    intro Hef.
    destruct ef; simpl in *;
      try solve [eexists; eauto];
      eapply builtin_or_external_sem_Three_Two'; eauto.
  Qed.

  Inductive list_lessdef_mod_1 : list val -> list val -> Prop :=
  | list_lessdef_mod_1_nil : list_lessdef_mod_1 nil nil
  | list_lessdef_mod_1_cons_lessdef : forall x y l1 l2,
      Val.lessdef x y ->
      list_lessdef_mod_1 l1 l2 ->
      list_lessdef_mod_1 (x :: l1 ) (y :: l2)
  | list_lessdef_mod_1_cons : forall x y l1 l2,
      (* ~ Val.lessdef x y -> *)
      Forall2 Val.lessdef l1 l2 ->
      list_lessdef_mod_1 (x :: l1) (y :: l2).

  Lemma lessdef_vote3_vote ty x x0 x1 y y0 y1 :
    Val.lessdef x y ->
    Val.lessdef x0 y0 ->
    Val.lessdef (vote3 ty x x0 x1) (vote ty y y0 y1).
  Proof.
    intros H0 H1.
    unfold vote3, vote.
    inv H0; inv H1; simpl;
      destruct (Val.has_type_dec _ _); simpl; try constructor;
      destruct (Val.eq _ _); simpl; try constructor; subst;
      destruct (Val.eq _ _); subst; simpl; constructor.
  Qed.
  
  Lemma lessdef_vote3_vote' ty x x0 x1 y y0 y1 :
    Val.lessdef x y ->
    Val.lessdef x1 y1 ->
    Val.lessdef (vote3 ty x x0 x1) (vote ty y y0 y1).
  Proof.
    intros H0 H1.
    unfold vote3, vote.
    inv H0; inv H1; simpl;
      destruct (Val.has_type_dec _ _); simpl; try constructor;
      destruct (Val.eq _ _); simpl; try constructor; subst;
      destruct (Val.eq _ _); subst; simpl; try constructor;
      destruct (Val.eq _ _); subst; simpl; constructor.
  Qed.
  
  Lemma lessdef_vote3_vote'' ty x x0 x1 y y0 y1 :
    Val.lessdef x0 y0 ->
    Val.lessdef x1 y1 ->
    Val.lessdef (vote3 ty x x0 x1) (vote ty y y0 y1).
  Proof.
    intros H0 H1.
    unfold vote3, vote.
    inv H0; inv H1; simpl;
      destruct (Val.has_type_dec _ _); simpl; try constructor;
      destruct (Val.eq _ _); simpl; try constructor; subst;
      destruct (Val.eq _ _); subst; simpl; try constructor.
    destruct (Val.has_type_dec _ _); simpl; try constructor.
    - destruct (Val.eq _ _); subst; simpl; try constructor.
      destruct (Val.has_type_dec _ _); simpl; try congruence; constructor.
    - destruct (Val.has_type_dec _ _); simpl; try congruence; constructor.
  Qed.

  Lemma external_call_green_smove_E0
    {VT: Builtins2.vote_type} {vsem: Builtins2.VoteSemantics VT}
    ef vs m t v m' :
    is_green_smove_builtin ef ->
    external_call ef (Genv.globalenv prog) vs m t v m' ->
    t = E0.
  Proof.
    intros Hef Hcall.
    unfold external_call, builtin_or_external_sem,
      Builtins.lookup_builtin_function in Hcall.
    simpl in Hcall.
    inv Hef; simpl in *; destruct (signature_eq _ _);
      try congruence; inv Hcall; auto.
  Qed.

  Lemma external_call_green_smove_mem
    {VT: Builtins2.vote_type} {vsem: Builtins2.VoteSemantics VT}
    ef vs m t v m' :
    is_green_smove_builtin ef ->
    external_call ef (Genv.globalenv prog) vs m t v m' ->
    m = m'.
  Proof.
    intros Hef Hcall.
    unfold external_call, builtin_or_external_sem,
      Builtins.lookup_builtin_function in Hcall.
    simpl in Hcall.
    inv Hef; simpl in *; destruct (signature_eq _ _);
      try congruence; inv Hcall; auto.
  Qed.

  Lemma external_call_blue_smove_E0
    {VT: Builtins2.vote_type} {vsem: Builtins2.VoteSemantics VT}
    ef vs m t v m' :
    is_blue_smove_builtin ef ->
    external_call ef (Genv.globalenv prog) vs m t v m' ->
    t = E0.
  Proof.
    intros Hef Hcall.
    unfold external_call, builtin_or_external_sem,
      Builtins.lookup_builtin_function in Hcall.
    simpl in Hcall.
    inv Hef; simpl in *; destruct (signature_eq _ _);
      try congruence; inv Hcall; auto.
  Qed.

  Lemma external_call_blue_smove_mem
    {VT: Builtins2.vote_type} {vsem: Builtins2.VoteSemantics VT}
    ef vs m t v m' :
    is_blue_smove_builtin ef ->
    external_call ef (Genv.globalenv prog) vs m t v m' ->
    m = m'.
  Proof.
    intros Hef Hcall.
    unfold external_call, builtin_or_external_sem,
      Builtins.lookup_builtin_function in Hcall.
    simpl in Hcall.
    inv Hef; simpl in *; destruct (signature_eq _ _);
      try congruence; inv Hcall; auto.
  Qed.

  Lemma external_call_vote_E0 {VT: Builtins2.vote_type} {vsem: Builtins2.VoteSemantics VT}
    ef vs m t v m' :
    is_vote_builtin ef ->
    external_call ef (Genv.globalenv prog) vs m t v m' ->
    t = E0.
  Proof.
    intros Hef Hcall.
    unfold external_call, builtin_or_external_sem,
      Builtins.lookup_builtin_function in Hcall.
    simpl in Hcall.
    inv Hef; simpl in *; destruct (signature_eq _ _);
      try congruence; inv Hcall; auto.
  Qed.

  Lemma external_call_vote_mem {VT: Builtins2.vote_type} {vsem: Builtins2.VoteSemantics VT}
    ef vs m t v m' :
    is_vote_builtin ef ->
    external_call ef (Genv.globalenv prog) vs m t v m' ->
    m = m'.
  Proof.
    intros Hef Hcall.
    unfold external_call, builtin_or_external_sem,
      Builtins.lookup_builtin_function in Hcall.
    simpl in Hcall.
    inv Hef; simpl in *; destruct (signature_eq _ _);
      try congruence; inv Hcall; auto.
  Qed.

  (* Note: The four cases below are structurally identical modulo the type
     argument to [vote]. Deduplication via Ltac was attempted in Phase 4
     but abandoned due to hypothesis name instability across inversion chains. *)
  Lemma external_call_vote_lessdef ef vs1 vs2 m1 m2 t v m' :
    is_vote_builtin ef ->
    list_lessdef_mod_1 vs1 vs2 ->
    Memory.Mem.extends m1 m2 ->
    @external_call Three VoteSemantics_Three ef (Genv.globalenv prog) vs1 m1 t v m' ->
    exists v', @external_call Two VoteSemantics_Two ef (Genv.globalenv prog) vs2 m2 t v' m2 /\
            Val.lessdef v v'.
  Proof.
    intros Hbuiltin Heq Hmem Hext.
    inv Hbuiltin; simpl in *.
    - unfold builtin_or_external_sem in *.
      unfold Builtins.lookup_builtin_function in *; simpl in *.
      destruct (signature_eq _ _); simpl in *; try congruence.
      clear e.
      inv Hext.
      simpl in *.
      inv Heq; try congruence.
      + inv H1; try congruence.
        * inv H3; try congruence.
          { inv H4; try congruence.
            inv H.
            exists (vote Tint y y0 y1); split.
            - constructor; auto.
            - apply lessdef_vote3_vote; auto. }
          inv H1; try congruence.
          inv H.
          exists (vote Tint y y0 y1); split.
          { constructor; auto. }
          apply lessdef_vote3_vote; auto.
        * inv H2; try congruence.
          inv H3; try congruence.
          inv H.
          exists (vote Tint y y0 y1); split.
          { constructor; auto. }
          apply lessdef_vote3_vote'; auto.
      + inv H0; try congruence.
        inv H2; try congruence.
        inv H3; try congruence.
        inv H.
        exists (vote Tint y y0 y1); split.
        { constructor; auto. }
        apply lessdef_vote3_vote''; auto.
    - unfold builtin_or_external_sem in *.
      unfold Builtins.lookup_builtin_function in *; simpl in *.
      destruct (signature_eq _ _); simpl in *; try congruence.
      clear e.
      inv Hext.
      simpl in *.
      inv Heq; try congruence.
      + inv H1; try congruence.
        * inv H3; try congruence.
          { inv H4; try congruence.
            inv H.
            exists (vote Tlong y y0 y1); split.
            - constructor; auto.
            - apply lessdef_vote3_vote; auto. }
          inv H1; try congruence.
          inv H.
          exists (vote Tlong y y0 y1); split.
          { constructor; auto. }
          apply lessdef_vote3_vote; auto.
        * inv H2; try congruence.
          inv H3; try congruence.
          inv H.
          exists (vote Tlong y y0 y1); split.
          { constructor; auto. }
          apply lessdef_vote3_vote'; auto.
      + inv H0; try congruence.
        inv H2; try congruence.
        inv H3; try congruence.
        inv H.
        exists (vote Tlong y y0 y1); split.
        { constructor; auto. }
        apply lessdef_vote3_vote''; auto.
    - unfold builtin_or_external_sem in *.
      unfold Builtins.lookup_builtin_function in *; simpl in *.
      destruct (signature_eq _ _); simpl in *; try congruence.
      clear e.
      inv Hext.
      simpl in *.
      inv Heq; try congruence.
      + inv H1; try congruence.
        * inv H3; try congruence.
          { inv H4; try congruence.
            inv H.
            exists (vote Tsingle y y0 y1); split.
            - constructor; auto.
            - apply lessdef_vote3_vote; auto. }
          inv H1; try congruence.
          inv H.
          exists (vote Tsingle y y0 y1); split.
          { constructor; auto. }
          apply lessdef_vote3_vote; auto.
        * inv H2; try congruence.
          inv H3; try congruence.
          inv H.
          exists (vote Tsingle y y0 y1); split.
          { constructor; auto. }
          apply lessdef_vote3_vote'; auto.
      + inv H0; try congruence.
        inv H2; try congruence.
        inv H3; try congruence.
        inv H.
        exists (vote Tsingle y y0 y1); split.
        { constructor; auto. }
        apply lessdef_vote3_vote''; auto.
    - unfold builtin_or_external_sem in *.
      unfold Builtins.lookup_builtin_function in *; simpl in *.
      destruct (signature_eq _ _); simpl in *; try congruence.
      clear e.
      inv Hext.
      simpl in *.
      inv Heq; try congruence.
      + inv H1; try congruence.
        * inv H3; try congruence.
          { inv H4; try congruence.
            inv H.
            exists (vote Tfloat y y0 y1); split.
            - constructor; auto.
            - apply lessdef_vote3_vote; auto. }
          inv H1; try congruence.
          inv H.
          exists (vote Tfloat y y0 y1); split.
          { constructor; auto. }
          apply lessdef_vote3_vote; auto.
        * inv H2; try congruence.
          inv H3; try congruence.
          inv H.
          exists (vote Tfloat y y0 y1); split.
          { constructor; auto. }
          apply lessdef_vote3_vote'; auto.
      + inv H0; try congruence.
        inv H2; try congruence.
        inv H3; try congruence.
        inv H.
        exists (vote Tfloat y y0 y1); split.
        { constructor; auto. }
        apply lessdef_vote3_vote''; auto.
  Qed.

  Lemma forall_lessdef_list rs1 rs2 args :
    Forall (fun arg => Val.lessdef (rs1 # arg) (rs2 # arg)) args ->
    Val.lessdef_list rs1 ## args rs2 ## args.
  Proof. induction 1; constructor; auto. Qed.

  Lemma forall2_lessdef rs1 rs2 args :
    Forall (fun arg => Val.lessdef (rs1 # arg) (rs2 # arg)) args ->
    Forall2 Val.lessdef rs1 ## args rs2 ## args.
  Proof. induction 1; constructor; auto. Qed.

  Lemma forall2_lessdef_list args1 args2 :
    Forall2 Val.lessdef args1 args2 ->
    Val.lessdef_list args1 args2.
  Proof. induction 1; constructor; auto. Qed.

  Lemma has_argtype_list_lessdef args1 args2 l :
    Val.has_argtype_list args1 l ->
    Forall2 Val.lessdef args1 args2 ->
    Val.has_argtype_list args2 l.
  Proof.
    revert args2 l; induction args1;
      intros args2 l Htype Hlessdef; inv Htype; inv Hlessdef; constructor.
    - eapply Val.has_argtype_lessdef; eauto.
    - apply IHargs1; auto.
  Qed.

  Lemma find_function_lessdef ros rs1 rs2 fd :
    (forall r, ros = inl r -> Val.lessdef (rs1 # r) (rs2 # r)) ->
    find_function (Genv.globalenv prog) ros rs1 = Some fd ->
    find_function (Genv.globalenv prog) ros rs2 = Some fd.
  Proof.
    unfold find_function.
    intros Hlessdef Hfind.
    destruct ros.
    - unfold Genv.find_funct in *.
      specialize (Hlessdef _ eq_refl); inv Hlessdef; try congruence.
      rewrite <- H0 in Hfind; congruence.
    - unfold Genv.find_symbol in *.
      destruct ((Genv.genv_symb _)) ! _; congruence.
  Qed.

  Lemma safe_external_call_E0 {VT: Builtins2.vote_type} {vsem: Builtins2.VoteSemantics VT}
    ef vargs m t vres m' :
    builtin_can_replicate ef = true ->
    @external_call VT vsem ef (Genv.globalenv prog) vargs m t vres m' ->
    t = E0.
  Proof.
    intros Hcan Hcall.
    unfold builtin_can_replicate in Hcan.
    destruct ef; simpl in *; try discriminate.
    destruct (Builtins.lookup_builtin_function name sg) eqn:Hlookup; [|discriminate].
    unfold external_call, builtin_or_external_sem in *.
    rewrite Hlookup in *. inv Hcall. reflexivity.
  Qed.

  Lemma safe_external_call_mem {VT: Builtins2.vote_type} {vsem: Builtins2.VoteSemantics VT}
    ef vargs m t vres m' :
    builtin_can_replicate ef = true ->
    @external_call VT vsem ef (Genv.globalenv prog) vargs m t vres m' ->
    m' = m.
  Proof.
    intros Hcan Hcall.
    unfold builtin_can_replicate in Hcan.
    destruct ef; simpl in *; try discriminate.
    destruct (Builtins.lookup_builtin_function name sg) eqn:Hlookup; [|discriminate].
    unfold external_call, builtin_or_external_sem in *.
    rewrite Hlookup in *. inv Hcall. reflexivity.
  Qed.

  Lemma safe_external_call_total
    {VT: Builtins2.vote_type} {vsem: Builtins2.VoteSemantics VT}
    ef vargs1 vargs2 m1 m2 t vres1 m1' :
    builtin_can_replicate ef = true ->
    Forall2 val_compat vargs1 vargs2 ->
    Memory.Mem.extends m1 m2 ->
    @external_call VT vsem ef (Genv.globalenv prog) vargs1 m1 t vres1 m1' ->
    exists vres2,
      @external_call VT vsem ef (Genv.globalenv prog) vargs2 m2 E0 vres2 m2.
  Proof.
    intros Hcan Hcompat Hmem Hcall.
    unfold builtin_can_replicate in Hcan.
    destruct ef; simpl in *; try discriminate.
    destruct (Builtins.lookup_builtin_function name sg) eqn:Hlookup; [|discriminate].
    unfold external_call, builtin_or_external_sem in *.
    rewrite Hlookup in *. inv Hcall.
    destruct b as [sb|pb|rb].
    - destruct sb; simpl in *; try discriminate;
        repeat match goal with
               | [ H : Forall2 _ (_ :: _) _ |- _ ] => inv H
               | [ H : Forall2 _ nil _ |- _ ] => inv H
               end;
        repeat match goal with
               | [ H : match ?x with _ :: _ => _ | nil => _ end = Some _ |- _ ] =>
                   destruct x; [discriminate|]; simpl in H
               | [ H : Forall2 _ (_ :: _) _ |- _ ] => inv H
               | [ H : Forall2 _ nil _ |- _ ] => inv H
               end;
        try match goal with
            | [ H : match ?x with _ :: _ => _ | nil => _ end = Some _ |- _ ] =>
                destruct x; [|discriminate]
            end;
        repeat match goal with
               | [ H : Forall2 _ nil _ |- _ ] => inv H
               end;
        try (eexists; constructor; reflexivity).
    - destruct pb; simpl in *; try discriminate;
        repeat match goal with
               | [ H : Forall2 _ (_ :: _) _ |- _ ] => inv H
               | [ H : Forall2 _ nil _ |- _ ] => inv H
               end;
        repeat match goal with
               | [ H : match ?x with _ :: _ => _ | nil => _ end = Some _ |- _ ] =>
                   destruct x; [discriminate|]; simpl in H
               | [ H : Forall2 _ (_ :: _) _ |- _ ] => inv H
               | [ H : Forall2 _ nil _ |- _ ] => inv H
               end;
        try match goal with
            | [ H : match ?x with _ :: _ => _ | nil => _ end = Some _ |- _ ] =>
                destruct x; [|discriminate]
            end;
        repeat match goal with
               | [ H : Forall2 _ nil _ |- _ ] => inv H
               end;
        try (eexists; constructor; reflexivity).
    - simpl in Hcan. discriminate.
  Qed.

  Lemma safe_external_call_val_compat
    {VT: Builtins2.vote_type} {vsem: Builtins2.VoteSemantics VT}
    ef vargs1 vargs2 m vres1 :
    builtin_can_replicate ef = true ->
    Forall2 val_compat vargs1 vargs2 ->
    @external_call VT vsem ef (Genv.globalenv prog) vargs1 m E0 vres1 m ->
    exists vres2,
      @external_call VT vsem ef (Genv.globalenv prog) vargs2 m E0 vres2 m /\
      val_compat vres1 vres2.
  Proof.
    intros Hcan Hcompat Hcall.
    unfold builtin_can_replicate in Hcan.
    destruct ef; simpl in *; try discriminate.
    destruct (Builtins.lookup_builtin_function name sg) eqn:Hlookup; [|discriminate].
    unfold external_call, builtin_or_external_sem in Hcall.
    rewrite Hlookup in Hcall. destruct Hcall as [vargs' vres' m' Hbsem].
    assert (Hnoshift: match b with
      | BI_standard BI_i64_shl
      | BI_standard BI_i64_shr
      | BI_standard BI_i64_sar => False
      | _ => True
      end).
    { destruct b as [sb|pb|rb]; simpl in Hcan; try discriminate.
      - destruct sb; simpl in Hcan; try discriminate; auto.
    }

    eapply builtin_sem_val_compat in Hbsem; eauto.
    destruct Hbsem as (vres2 & Hsem2 & Hvc).
    exists vres2. split; auto.
    unfold external_call, builtin_or_external_sem.
    rewrite Hlookup. constructor; auto.
  Qed.

  Lemma eval_builtin_arg_val_compat sp m1 m2 rs1 rs2 a v1 :
    rs_compat rs1 rs2 ->
    Memory.Mem.extends m1 m2 ->
    eval_builtin_arg ge (fun r => rs1 # r) sp m1 a v1 ->
    exists v2, eval_builtin_arg ge (fun r => rs2 # r) sp m2 a v2 /\ val_compat v1 v2.
  Proof.
    intros Hrs Hmem Heval.
    induction Heval.
    - exists (rs2 # x). split; [constructor | apply Hrs].
    - eexists; split; [constructor | apply val_compat_refl].
    - eexists; split; [constructor | apply val_compat_refl].
    - eexists; split; [constructor | apply val_compat_refl].
    - eexists; split; [constructor | apply val_compat_refl].
    - eapply Memory.Mem.loadv_extends in H; eauto.
      destruct H as (v2 & Hload & Hld).
      eexists; split; [econstructor; eauto | apply val_lessdef_compat; auto].
    - eexists; split; [constructor | apply val_compat_refl].
    - eapply Memory.Mem.loadv_extends in H; eauto.
      destruct H as (v2 & Hload & Hld).
      eexists; split; [econstructor; eauto | apply val_lessdef_compat; auto].
    - eexists; split; [constructor | apply val_compat_refl].
    - destruct IHHeval1 as (v2hi & Hhi & Hchi).
      destruct IHHeval2 as (v2lo & Hlo & Hclo).
      eexists; split; [econstructor; eauto|].
      inv Hchi; inv Hclo; simpl; try constructor.
    - destruct IHHeval1 as (v2a & Ha & Hca).
      destruct IHHeval2 as (v2b & Hb & Hcb).
      eexists; split; [econstructor; eauto|].
      destruct Archi.ptr64; [unfold Val.addl | unfold Val.add];
        inv Hca; inv Hcb; simpl; try constructor;
        try (destruct Archi.ptr64; constructor).
  Qed.

  Lemma eval_builtin_args_val_compat sp m1 m2 rs1 rs2 al vl1 :
    rs_compat rs1 rs2 ->
    Memory.Mem.extends m1 m2 ->
    eval_builtin_args ge (fun r => rs1 # r) sp m1 al vl1 ->
    exists vl2, eval_builtin_args ge (fun r => rs2 # r) sp m2 al vl2 /\
      Forall2 val_compat vl1 vl2.
  Proof.
    intros Hrs Hmem Heval. induction Heval.
    - exists nil; split; [constructor | constructor].
    - edestruct eval_builtin_arg_val_compat as (v2 & Hv2 & Hvc); eauto.
      destruct IHHeval as (vl2 & Hvl2 & Hfl).
      exists (v2 :: vl2); split; [econstructor; eauto | constructor; auto].
  Qed.


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
    inv Hstep; inv Hmatch; try (inv_stk; destruct y).

    (* exec_Inop *)
    - eexists; econstructor.
      2: { apply maybe_zap_refl. }
      eapply exec_Inop; eauto.

    (* exec_Iop *)
    - destruct (is_protectedb_spec op).
      + (* op is protected *)
        eapply Op.eval_operation_lessdef with (vl2 := rs2 ## args) in H0; eauto.
        2: { apply forall_lessdef_list.
             apply Forall_forall; intros r Hin.
             destruct fault.
             - unfold match_rs in RS. inv_rs; inv_wc.
               apply_RS.
               rewrite Forall_forall in H6; apply H6 in Hin.
               intro HC; rewrite Hin in HC; inv HC; inv Hc.
             - apply RS. }
        destruct H0 as (v2 & Hop & Hv2).
        eexists; econstructor.
        2: { apply maybe_zap_refl. }
        eapply exec_Iop; eauto.
      + (* op is safe *)
        eapply rs_compat_eval_operation in H0; eauto.
        destruct H0 as [v' Hop].
        eapply Op.eval_operation_lessdef in Hop; eauto.
        2: { apply Val.lessdef_list_refl. }
        destruct Hop as (v2 & Hop & Hv2).
        eexists; econstructor.
        2: { apply maybe_zap_refl. }
        eapply exec_Iop; eauto.

    (* exec_Iload *)
    - eapply Op.eval_addressing_lessdef with (vl2 := rs2 ## args) in H0.
      2: { apply forall_lessdef_list.
           apply Forall_forall; intros r Hin.
           destruct fault.
           - unfold match_rs in RS. inv_rs; inv_wc.
             apply_RS.
             rewrite Forall_forall in H5; apply H5 in Hin.
             intro HC; rewrite Hin in HC; inv HC; inv Hc.
           - apply RS. }
      destruct H0 as (v2 & Hop & Hv2).
      eapply Memory.Mem.loadv_extends in H1; eauto.
      destruct H1 as (v3 & Hmem & Hv3).
      eexists; econstructor.
      2: { apply maybe_zap_refl. }
      eapply exec_Iload; eauto.

    (* exec_Istore *)
    - eapply Op.eval_addressing_lessdef with (vl2 := rs2 ## args) in H0.
      2: { apply forall_lessdef_list.
           apply Forall_forall; intros r Hin.
           destruct fault.
           - unfold match_rs in RS. inv_rs; inv_wc.
             apply_RS.
             rewrite Forall_forall in H8; apply H8 in Hin.
             intro HC; rewrite Hin in HC; inv HC; inv Hc.
           - apply RS. }
      destruct H0 as (v2 & Hop & Hv2).
      eapply Memory.Mem.storev_extends in H1.
      2: { eauto. }
      2: { eauto. }
      2: { destruct fault.
           - unfold match_rs in RS.
             inv_rs; inv_wc.
             apply_RS.
             intro HC; rewrite H4 in HC; inv HC; inv Hc.
           - apply RS. }
      destruct H1 as (v3 & Hmem & Hv3).
      eexists; econstructor.
      2: { apply maybe_zap_refl. }
      eapply exec_Istore; eauto.

    (* exec_Icall *)
    - simpl in *.
      destruct ros.
      + eapply find_function_lessdef in H0.
        2: { intros x Hx; subst; inv Hx.
             destruct fault.
             - unfold match_rs in RS. inv_rs; inv_wc.
               apply_RS.
               intro HC; rewrite H5 in HC; auto; inv HC; inv Hc.
             - apply RS. }
        eexists; econstructor.
        2: { apply maybe_zap_refl. }
        eapply exec_Icall; eauto.
      + eexists; econstructor.
        2: { apply maybe_zap_refl. }
        eapply exec_Icall; eauto.

    (* exec_Itailcall *)
    - simpl in *.
      eapply Memory.Mem.free_parallel_extends in H2; eauto.
      destruct H2 as (m2' & Hfree & Hm2').
      destruct ros.
      + eapply find_function_lessdef in H0.
        2: { intros x Hx; subst; inv Hx.
             destruct fault.
             - unfold match_rs in RS. inv_rs; inv_wc.
               apply_RS.
               intro HC; rewrite H3 in HC; auto; inv HC; inv Hc.
             - apply RS. }
        eexists; econstructor.
        2: { apply maybe_zap_refl. }
        eapply exec_Itailcall; eauto.
      + eexists; econstructor.
        2: { apply maybe_zap_refl. }
        eapply exec_Itailcall; eauto.

    (* exec_Ibuiltin *)
    - destruct (is_vote_builtinb_spec ef) as [Hbuiltin|Hbuiltin].
      + pose proof H as Hpc.
        inv_wc; try solve [apply vote_not_green_smove in Hbuiltin; congruence];
          try solve [apply vote_not_blue_smove in Hbuiltin; congruence];
          try solve [exfalso; inv Hbuiltin; vm_compute in H6; discriminate].
        simpl in *.
        destruct vargs.
        { inv H0. }
        destruct vargs.
        { inv H0; inv H13. }
        destruct vargs.
        { inv H0; inv H13; inv H14. }
        destruct vargs.
        2: { inv H0; inv H13; inv H14; inv H15. }
        inv H0.
        inv H13; inv H14; inv H15.
        inv H5; inv H4; inv H12.
        unfold match_rs in RS.
        destruct fault.
        2: { eapply external_call_mem_extends with
          (vargs' := rs2 ## (arg1 :: arg2 :: arg3 :: nil)) in H1; eauto.
             2: { constructor; auto. }
             destruct H1 as (vres' & m2' & Hext & Hvres & Hmem & Hmem').
             apply external_call_Three_Two' in Hext.
             destruct Hext as [v' [Hext _]].
             eexists; econstructor.
             2: { apply maybe_zap_refl. }
             eapply exec_Ibuiltin; eauto.
             repeat constructor. }
        eapply external_call_vote_lessdef
          with (vs2 := rs2 ## (arg1 :: arg2 :: arg3 :: nil)) in H1; eauto.
        destruct H1 as (v' & Hext & Hv').
        2: { inv_rs.
             assert (Hparams_in: forall r, In r (arg1 :: arg2 :: arg3 :: nil) ->
                       Regset.In r (ProofLiveness.transfer f pc (live !! pc))).
             { intros r' Hr'. eapply args_in_transfer_ibuiltin; eauto. }
             destruct c.
             - apply list_lessdef_mod_1_cons.
               repeat constructor.
               + apply RS; [apply Hparams_in; simpl; auto|].
                 intro HC; rewrite H8 in HC; inv HC.
               + apply RS; [apply Hparams_in; simpl; auto|].
                 intro HC; rewrite H9 in HC; inv HC.
             - apply list_lessdef_mod_1_cons_lessdef.
               { apply RS; [apply Hparams_in; simpl; auto|].
                 intro HC; rewrite H7 in HC; inv HC. }
               apply list_lessdef_mod_1_cons.
               repeat constructor.
               + apply RS; [apply Hparams_in; simpl; auto|].
                 intro HC; rewrite H9 in HC; inv HC.
             - apply list_lessdef_mod_1_cons_lessdef.
               { apply RS; [apply Hparams_in; simpl; auto|].
                 intro HC; rewrite H7 in HC; inv HC. }
               apply list_lessdef_mod_1_cons_lessdef.
               { apply RS; [apply Hparams_in; simpl; auto|].
                 intro HC; rewrite H8 in HC; inv HC. }
               apply list_lessdef_mod_1_cons.
               repeat constructor.
             - inv Hc.
             - inv Hc. }
        eexists; econstructor.
        2: { apply maybe_zap_refl. }
        eapply exec_Ibuiltin; eauto.
        repeat constructor.
      + destruct (builtin_can_replicate ef) eqn:Hcan.
        * (* Safe builtin *)
          assert (HtE0: t = E0) by (eapply (@safe_external_call_E0 Three VoteSemantics_Three); eauto).
          subst t.
          eapply eval_builtin_args_val_compat in H0 as H0'; eauto.
          destruct H0' as (vargs2 & Heval2 & Hcompat).
          eapply (@safe_external_call_total Three VoteSemantics_Three) in H1 as Hcall; eauto.
          destruct Hcall as (vres2 & Hcall2).
          apply external_call_Three_Two' in Hcall2.
          destruct Hcall2 as (v' & Hcall2 & _).
          eexists; econstructor.
          2: { apply maybe_zap_refl. }
          eapply exec_Ibuiltin; eauto.
        * (* Non-safe, non-vote builtin *)
          eapply eval_builtin_args_lessdef' with (e2 := fun r => rs2 # r) in H0; eauto.
          2: { apply Forall_forall.
               intros barg Hin.
               inv_wc; try contradiction; try congruence.
             - (* smove_green *)
               inv Hin; [|contradiction].
               simpl.
               destruct fault.
               + unfold match_rs in RS. inv_rs.
                 apply RS.
                 * eapply args_in_transfer_ibuiltin; eauto. simpl; auto.
                 * intro HC; rewrite H7 in HC; inv HC; inv Hc.
               + apply RS.
             - (* smove_blue *)
               inv Hin; [|contradiction].
               simpl.
               destruct fault.
               + unfold match_rs in RS. inv_rs.
                 apply RS.
                 * eapply args_in_transfer_ibuiltin; eauto. simpl; auto.
                 * intro HC; rewrite H7 in HC; inv HC; inv Hc.
               + apply RS.
             - (* general builtin *)
               pose proof Hin as Hin_save.
               match goal with
               | [ HF : Forall (builtin_arg_forall _) _ |- _ ] =>
                   rewrite Forall_forall in HF; apply HF in Hin
               end.
               destruct fault.
               + unfold match_rs in RS. inv_rs.
                 eapply builtin_arg_forall_impl_in.
                 2: { exact Hin. }
                 simpl; intros a Ha Hin_barg.
                 apply RS.
                 * eapply args_in_transfer_ibuiltin; eauto.
                   eapply in_builtin_arg_in_params_args; eauto.
                 * intro HC; rewrite Ha in HC; inv HC; inv Hc.
               + eapply builtin_arg_forall_impl with (P := fun _ => True); auto.
                 apply builtin_arg_forall_true. }
        destruct H0 as (vl2 & Heval & Hvl2).
        eapply external_call_mem_extends in H1; eauto.
        destruct H1 as (vres' & m2' & Hext & Hvres' & Hmem & Hmem').
        apply external_call_Three_Two' in Hext.
        destruct Hext as [v' [Hext _]].
        eexists; econstructor.
        2: { apply maybe_zap_refl. }
        eapply exec_Ibuiltin; eauto.

    (* exec_Icond *)
    - simpl in *.
      eapply Op.eval_condition_lessdef in H0.
      2: { apply forall_lessdef_list.
           apply Forall_forall; intros r Hin.
           destruct fault.
           - unfold match_rs in RS. inv_rs; inv_wc.
             apply_RS.
             rewrite Forall_forall in H3; apply H3 in Hin.
             intro HC; rewrite Hin in HC; inv HC; inv Hc.
           - apply RS. }
      2: { eauto. }
      eexists; econstructor.
      2: { apply maybe_zap_refl. }
      eapply exec_Icond; eauto.

    (* exec_Ijumptable *)
    - eexists; econstructor.
      2: { apply maybe_zap_refl. }
      eapply exec_Ijumptable; eauto.
      assert (Hlessdef: Val.lessdef (rs # arg) (rs2 # arg)).
      { destruct fault.
        - unfold match_rs in RS. inv_rs; inv_wc.
          apply_RS.
          intro HC; rewrite H4 in HC; inv HC; inv Hc.
        - apply RS. }
      rewrite H0 in Hlessdef; inv Hlessdef; reflexivity.

    (* exec_Ireturn *)
    - eapply Memory.Mem.free_parallel_extends in H0; eauto.
      destruct H0 as (m2' & Hmem2 & Hm2').
      eexists.
      eapply fstep_step_State.
      2: { apply maybe_zap_refl. }
      apply exec_Ireturn; eauto.

    (* exec_function_internal *)
    - eapply Memory.Mem.alloc_extends
        with (lo2 := 0) (hi2 := fn_stacksize f) in H0;
        eauto; try reflexivity.
      destruct H0 as (m2' & Halloc & Hm2').
      eexists.
      repeat constructor; eauto.
      eapply has_argtype_list_lessdef; eauto.

    (* exec_function_external *)
    - eapply external_call_mem_extends in H; eauto.
      2: { apply forall2_lessdef_list; eauto. }
      destruct H as (vres' & m2' & Hcall & Hvres' & Hext & Hmem).
      apply external_call_Three_Two' in Hcall.
      destruct Hcall as (v' & Hcall & Hv').
      eexists.
      repeat constructor; simpl; eauto.

    (* exec_return *)
    - inv STK; inv H1.
      eexists; repeat constructor.
  Qed.

  Lemma external_call_mem_extends
    ef vargs1 vargs2 m1 m2 t vres1 vres2 m1' m2' :
    Val.lessdef_list vargs1 vargs2 ->
    Memory.Mem.extends m1 m2 ->
    @external_call Three VoteSemantics_Three ef (Genv.globalenv prog) vargs1 m1 t vres1 m1' ->
    @external_call Two VoteSemantics_Two ef (Genv.globalenv prog) vargs2 m2 t vres2 m2' ->
    Memory.Mem.extends m1' m2'.
  Proof.
    intros Hlessdef Hmem Hext1 Hext2.
    apply external_call_Three_Two' in Hext1.
    destruct Hext1 as [v' [Hext1 _]].
    eapply external_call_mem_extends in Hext1; eauto.
    destruct Hext1 as (vres' & m2'' & Hext1 & Hld & Hmem' & Hmem'').
    eapply external_call_deterministic in Hext2; eauto.
    destruct Hext2; subst.
    auto.
  Qed.
  
  Lemma find_function_wc_fundef p ros rs fd :
    wc_program p ->
    find_function (Genv.globalenv p) ros rs = Some fd ->
    wc_fundef fd.
  Proof.
    intros Hwc Hfind.
    destruct ros; simpl in Hfind.
    - apply Genv.find_funct_inversion in Hfind.
      destruct Hfind as [i Hin].
      eapply Hwc; eauto.
    - destruct (Genv.find_symbol _ _); try congruence.
      apply Genv.find_funct_ptr_inversion in Hfind.
      destruct Hfind as [id Hin].
      eapply Hwc; eauto.
  Qed.

  Lemma forall2_lessdef_rs_compat_init_regs args1 args2 params :
    Forall2 Val.lessdef args1 args2 ->
    rs_compat (init_regs args1 params) (init_regs args2 params).
  Proof.
    revert args1 args2.
    induction params; simpl; intros args1 args2 Hforall.
    { intro r; apply val_compat_refl. }
    intro r.
    destruct args1; inv Hforall.
    { apply val_compat_refl. }
    destruct (peq r a); subst.
    - rewrite 2!Regmap.gss.
      apply val_lessdef_compat; assumption.
    - rewrite 2!Regmap.gso; auto.
      apply IHparams; assumption.
  Qed.

  
  Lemma forall2_lessdef_match_rs_init_regs live args1 args2 col b params :
    Forall2 Val.lessdef args1 args2 ->
    match_rs live col b (init_regs args1 params) (init_regs args2 params).
  Proof.
    revert b args1 args2.
    induction params; simpl; intros b args1 args2 Hforall.
    { destruct b.
      - exists Red; split; [constructor|].
        intros r _ _; apply Val.lessdef_refl.
      - intro r; apply Val.lessdef_refl. }
    destruct b.
    - destruct args1; inv Hforall.
      { exists Red; split; [constructor|].
        intros r _ _; apply Val.lessdef_refl. }
      eapply IHparams with (b := true) in H3; eauto.
      destruct H3 as (c & Hc & RS).
      exists c; split; auto.
      intros r Hlive Hr.
      destruct (peq r a); subst.
      + rewrite 2!Regmap.gss; assumption.
      + rewrite 2!Regmap.gso; auto.
    - destruct args1; inv Hforall.
      { intro r; apply Val.lessdef_refl. }
      intro r.
      destruct (peq r a); subst.
      + rewrite 2!Regmap.gss; assumption.
      + rewrite 2!Regmap.gso; auto.
        eapply IHparams with (b := false) in H3; eauto.
  Qed.

  Lemma step_simulation
    s2 t s2' b :
    Step (@RTL.semantics Two VoteSemantics_Two prog) s2 t s2' ->
    forall i (s1 : state (@RTL.semantics Three VoteSemantics_Three prog)),
      match_states i s1 {| fs_state := s2; fault := b |} ->
      safe (RTL.semantics prog) s1 ->
      exists i' s1',
        Step (RTL.semantics prog) s1 t s1' /\
          match_states i' s1' {| fs_state := s2'; fault := b |}.
  Proof.
    simpl; intros Hstep i s1 Hmatch Hsafe; subst.
    exists i.
    inv Hstep.

    (* exec_Inop *)
    - inv Hmatch.
      assert (Hwc_instr: wc_instruction live col pc (Inop pc')).
      { inv WC_FUN. rewrite LIVE in WC_LIVE; inv WC_LIVE.
        apply WC_CODE; assumption. }
      inv Hwc_instr.
      eexists; split.
      + eapply exec_Inop; eauto.
      + econstructor; eauto.
        unfold match_rs in *.
        destruct b; auto.
        destruct RS as (c & Hc & RS).
        exists c; split; [auto|].
        intros r Hr Hcol.
        assert (Hsub: Regset.Subset (ProofLiveness.transfer f pc' (live !! pc'))
                                    (live !! pc)).
        { eapply transfer_succ_subset; eauto. simpl; auto. }
        assert (Hin_live: Regset.In r (live !! pc)).
        { apply Hsub; auto. }
        assert (Hin_xfer: Regset.In r (ProofLiveness.transfer f pc (live !! pc))).
        { unfold ProofLiveness.transfer. rewrite H. exact Hin_live. }
        apply RS; auto.
        rewrite (H1 r Hin_live); auto.

    (* exec_Iop *)
    - inv Hmatch.
      specialize (Hsafe _ (star_refl _ _ _)).
      destruct Hsafe as [[r Hfin] | (t & s'' & Hstep)].
      { inv Hfin. }
      inv Hstep; try congruence.
      eexists; split.
      { eapply exec_Iop; eauto. }
      rewrite H in H9; inv H9.
      econstructor; eauto.
      + intro r.
        destruct (peq r res0); subst.
        * rewrite 2!Regmap.gss.
          destruct (is_protectedb_spec op0).
          { apply val_lessdef_compat.
            eapply Op.eval_operation_lessdef
              with (vl2 := rs ## args0) in H10; eauto.
            2: { apply forall_lessdef_list.
                 apply Forall_forall.
                 intros r Hin.
                 destruct b; auto.
                 inv_rs; inv_wc.
                 apply RS; [eapply args_in_transfer_iop; eauto|].
                 intro HC.
                 rewrite Forall_forall in H6; apply H6 in Hin.
                 rewrite Hin in HC; inv HC; inv Hc. }
            destruct H10 as (v2 & Hop & Hv2).
            simpl in *.
            rewrite H0 in Hop; inv Hop; assumption. }
          eapply eval_operation_val_compat; eauto.
        * rewrite 2!Regmap.gso; auto.
      + unfold match_rs in *.
        destruct b; simpl in *.
        * inv_rs; exists c; split; auto.
          intros r Hr.
          assert (Hin_live: Regset.In r (live !! pc)).
          { eapply transfer_succ_subset; eauto. simpl; auto. }
          inv_wc; try unify_live.
          { (* Safe op (replicated) *)
            destruct (peq r res0); subst.
            - rewrite 2!Regmap.gss.
              intro Hcol_ne.
              eapply Op.eval_operation_lessdef
                with (vl2 := rs ## args0) in H10; eauto.
              2: { apply forall_lessdef_list.
                   apply Forall_forall.
                   intros r Hin.
                   apply RS.
                   + eapply args_in_transfer_iop; eauto.
                   + rewrite Forall_forall in H7; apply H7 in Hin.
                     rewrite Hin. exact Hcol_ne. }
              destruct H10 as (v2 & Hop & Hv2).
              rewrite H0 in Hop; inv Hop; assumption.
            - rewrite 2!Regmap.gso; auto.
              intro Hcol_ne.
              apply RS.
              + eapply live_in_transfer_iop; eauto.
              + intro HC. apply Hcol_ne.
                rewrite <- (H8 r Hin_live n). exact HC. }
          (* Protected op (voted) *)
          destruct (peq r res0); subst.
          { rewrite 2!Regmap.gss.
            intro Hcol_ne.
            eapply Op.eval_operation_lessdef
              with (vl2 := rs ## args0) in H10; eauto.
            2: { apply forall_lessdef_list.
                 apply Forall_forall.
                 intros r Hin.
                 apply RS.
                 + eapply args_in_transfer_iop; eauto.
                 + rewrite Forall_forall in H6; apply H6 in Hin.
                   intro HC; rewrite Hin in HC; inv HC; inv Hc. }
            destruct H10 as (v2 & Hop & Hv2).
            rewrite H0 in Hop; inv Hop; assumption. }
          rewrite 2!Regmap.gso; auto.
          intro Hcol_ne.
          apply RS.
          { destruct (in_dec peq r args0).
            - eapply args_in_transfer_iop; eauto.
            - eapply live_in_transfer_iop; eauto. }
          intro HC.
          destruct (in_dec peq r args0).
          { rewrite Forall_forall in H6; apply H6 in i.
            rewrite i in HC; inv HC; inv Hc. }
          apply Hcol_ne. rewrite <- (H8 r Hin_live n0 n). exact HC.
        * intro r; destruct (peq r res0); subst.
          { rewrite 2!Regmap.gss.
            eapply Op.eval_operation_lessdef
              with (vl2 := rs ## args0) in H10; eauto.
            2: { apply forall_lessdef_list.
                 apply Forall_forall.
                 intros r Hin; auto. }
            destruct H10 as (v2 & Hop & Hv2).
            rewrite H0 in Hop; inv Hop; assumption. }
          rewrite 2!Regmap.gso; auto.

    (* exec_Iload *)
    - inv Hmatch.
      specialize (Hsafe _ (star_refl _ _ _)).
      destruct Hsafe as [[r Hfin] | (t & s'' & Hstep)].
      { inv Hfin. }
      inv Hstep; try congruence.
      eexists; split.
      { eapply exec_Iload; eauto. }
      rewrite H in H10; inv H10.
      simpl in *.
      assert (Hlessdef_list: Val.lessdef_list (rs1 ## args0 ) (rs ## args0)).
      { apply forall_lessdef_list.
        apply Forall_forall; intros r Hin.
        destruct b; auto.
        inv_rs; inv_wc.
        apply RS; [eapply args_in_transfer_iload; eauto|].
        rewrite Forall_forall in H5; apply H5 in Hin.
        intro HC; rewrite Hin in HC; inv HC; inv Hc. }
      assert (Hlessdef_v: Val.lessdef v0 v).
      { eapply Op.eval_addressing_lessdef in H11; eauto.
        destruct H11 as (v2 & Heval & Hv2).
        rewrite H0 in Heval; inv Heval.
        eapply Memory.Mem.loadv_extends in H12; eauto.
        destruct H12 as (v3 & Hload & Hv3).
        rewrite H1 in Hload; inv Hload; assumption. }
      econstructor; eauto.
      + intro r.
        destruct (peq r dst0); subst.
        * rewrite 2!Regmap.gss.
          apply val_lessdef_compat; auto.
        * rewrite 2!Regmap.gso; auto.
      + unfold match_rs in *.
        destruct b; simpl in *.
        * inv_rs; exists c; split; auto.
          intros r Hr.
          destruct (peq r dst0); subst.
          { rewrite 2!Regmap.gss; intro; exact Hlessdef_v. }
          rewrite 2!Regmap.gso; auto.
          assert (Hin_live: Regset.In r (live !! pc)).
          { eapply transfer_succ_subset; eauto. simpl; auto. }
          inv_wc; try unify_live.
          intro Hcol_ne.
          apply RS.
          { destruct (in_dec peq r args0).
            - eapply args_in_transfer_iload; eauto.
            - eapply live_in_transfer_iload; eauto. }
          intro HC.
          destruct (in_dec peq r args0).
          { rewrite Forall_forall in H5.
            apply H5 in i; rewrite i in HC; inv HC; inv Hc. }
          apply Hcol_ne. rewrite <- (H9 r Hin_live n0 n). exact HC.
        * intro r.
          destruct (peq r dst0); subst.
          { rewrite 2!Regmap.gss; auto. }
          rewrite 2!Regmap.gso; auto.

    (* exec_Istore *)
    - inv Hmatch.
      specialize (Hsafe _ (star_refl _ _ _)).
      destruct Hsafe as [[r Hfin] | (t & s'' & Hstep)].
      { inv Hfin. }
      inv Hstep; try congruence.
      eexists; split.
      { eapply exec_Istore; eauto. }
      rewrite H in H10; inv H10.
      simpl in *.
      assert (Hlessdef_list: Val.lessdef_list (rs1 ## args0 ) (rs ## args0)).
      { apply forall_lessdef_list.
        apply Forall_forall; intros r Hin.
        destruct b; auto.
        inv_rs; inv_wc.
        apply RS; [eapply args_in_transfer_istore; eauto|].
        rewrite Forall_forall in H8; apply H8 in Hin.
        intro HC; rewrite Hin in HC; inv HC; inv Hc. }
      assert (Ha: Val.lessdef a0 a).
      { eapply Op.eval_addressing_lessdef in H11; eauto.
        destruct H11 as (v2 & Heval & Hv2).
        rewrite H0 in Heval; inv Heval; assumption. }
      assert (Hsrc: Val.lessdef (rs1 # src0) (rs # src0)).
      { destruct b; auto; inv_rs; inv_wc.
        apply RS; [eapply src_in_transfer_istore; eauto|].
        intro HC; rewrite H5 in HC; inv HC; inv Hc. }
      assert (Memory.Mem.extends m'0 m').
      { eapply Memory.Mem.storev_extends in H12; eauto.
        destruct H12 as (m2' & Hstore & Hm2').
        rewrite H1 in Hstore; inv Hstore; auto. }
      econstructor; eauto.
      destruct b; auto.
      inv_rs; inv_wc; try unify_live; exists c; split; auto.
      intros r Hr.
      assert (Hin_live: Regset.In r (live !! pc)).
      { eapply transfer_succ_subset; eauto. simpl; auto. }
      intro Hcol_ne.
      apply RS.
      { eapply live_in_transfer_istore; eauto. }
      intro HC.
      destruct (peq r src0) as [Heq_src | Hneq_src].
      { subst r.
        match goal with
        | [ Hsrc : col _ src0 = White, HC0 : col _ src0 = ?c0,
            Hc0 : is_basic ?c0 |- _ ] =>
            rewrite Hsrc in HC0; inv HC0; inv Hc0
        end. }
      destruct (in_dec peq r args0).
      { match goal with
        | [ Hforall : Forall (fun arg => col _ arg = White) ?al,
            Hin0 : In r ?al, HC0 : col _ r = ?c0,
            Hc0 : is_basic ?c0 |- _ ] =>
            rewrite Forall_forall in Hforall; apply Hforall in Hin0;
            rewrite Hin0 in HC0; inv HC0; inv Hc0
        end. }
      apply Hcol_ne.
      match goal with
      | [ Hfa : Regset.For_all _ (live !! pc) |- _ ] =>
          rewrite <- (Hfa r Hin_live n Hneq_src); exact HC
      end.

    (* exec_Icall *)
    - inv Hmatch.
      specialize (Hsafe _ (star_refl _ _ _)).
      destruct Hsafe as [[r Hfin] | (t & s'' & Hstep)].
      { inv Hfin. }
      inv Hstep; try congruence.
      eexists; split.
      { eapply exec_Icall; eauto. }
      rewrite H in H9; inv H9.
      simpl in *.
      eapply find_function_lessdef with (rs2 := rs) in H10.
      2: { intros r Hr.
           destruct b; auto.
           inv_rs; inv_wc.
           apply RS; [eapply ros_in_transfer_icall; eauto|].
           intro HC.
           rewrite (H6 _ (eq_refl _)) in HC; inv HC; inv Hc. }
      rewrite H0 in H10; inv H10.
      assert (Hlessdef: Forall2 Val.lessdef rs1 ## args0 rs ## args0).
      { apply forall2_lessdef.
        apply Forall_forall.
        intros r Hin.
        destruct b; auto.
        inv_rs; inv_wc.
        apply RS; [eapply args_in_transfer_icall; eauto|].
        rewrite Forall_forall in H8; apply H8 in Hin.
        intro HC; rewrite Hin in HC; inv HC; inv Hc. }
      econstructor; auto.
      2: { eapply find_function_wc_fundef; eauto. }
      constructor; auto.
      econstructor; eauto.
      destruct b.
      2: { unfold match_rs in RS; unfold match_rs_upto; intros r Hneq; apply RS. }
      inv_rs.
      assert (Hsucc_subset: Regset.Subset
                (ProofLiveness.transfer f pc'0 (live !! pc'0)) (live !! pc)).
      { eapply transfer_succ_subset; eauto. simpl; auto. }
      inv_wc; try unify_live; exists c; split; auto.
      intros r Hneq Hr Hcol_ne.
      destruct (peq r res0); subst; try congruence.
      assert (Hin_live: Regset.In r (live !! pc)).
      { apply Hsucc_subset; assumption. }
      destruct (in_dec peq r args0) as [Hin_args | Hni_args].
      { apply RS; [eapply args_in_transfer_icall; eauto|].
        intro HC.
        match goal with
        | [ Hforall : Forall _ args0 |- _ ] =>
            rewrite Forall_forall in Hforall; specialize (Hforall _ Hin_args);
            rewrite Hforall in HC; inv HC; inv Hc
        end. }
      apply RS; [eapply live_in_transfer_icall; eauto|].
      intro HC; apply Hcol_ne.
      assert (Hros_ne: forall x, ros0 = inl x -> r <> x).
      { intros x Hx.
        intro Heq; subst r.
        match goal with
        | [ Hros : forall _, _ = inl _ -> _ |- _ ] =>
            specialize (Hros _ Hx); rewrite Hros in HC; inv HC; inv Hc
        end. }
      match goal with
      | [ Hfa : Regset.For_all _ _ |- _ ] =>
          rewrite <- (Hfa r Hin_live Hni_args n Hros_ne); exact HC
      end.

    (* exec_Itailcall *)
    - inv Hmatch.
      specialize (Hsafe _ (star_refl _ _ _)).
      destruct Hsafe as [[r Hfin] | (t & s'' & Hstep)].
      { inv Hfin. }
      inv Hstep; try congruence.
      pose proof H13 as Hfree.
      eapply Memory.Mem.free_parallel_extends in Hfree; eauto.
      destruct Hfree as (m2' & Hfree & Hm2').
      rewrite H2 in Hfree; inv Hfree.
      eexists; split.
      { eapply exec_Itailcall; eauto. }
      rewrite H in H10; inv H10.
      simpl in *.
      eapply find_function_lessdef with (rs2 := rs) in H11.
      2: { intros r Hr.
           destruct b; auto.
           inv_rs; inv_wc.
           apply RS; [eapply ros_in_transfer_itailcall; eauto|].
           intro HC.
           rewrite (H5 _ (eq_refl _)) in HC; inv HC; inv Hc. }
      rewrite H0 in H11; inv H11.
      assert (Hlessdef: Forall2 Val.lessdef rs1 ## args0 rs ## args0).
      { apply forall2_lessdef.
        apply Forall_forall.
        intros r Hin.
        destruct b; auto.
        inv_rs; inv_wc.
        apply RS; [eapply args_in_transfer_itailcall; eauto|].
        rewrite Forall_forall in H7; apply H7 in Hin.
        intro HC; rewrite Hin in HC; inv HC; inv Hc. }
      econstructor; auto.
      eapply find_function_wc_fundef; eauto.

    (* exec_Ibuiltin *)
    - inv Hmatch.
      specialize (Hsafe _ (star_refl _ _ _)).
      destruct Hsafe as [[r Hfin] | (t' & s'' & Hstep)].
      { inv Hfin. }
      inv Hstep; try congruence.
      rewrite H in H10; inv H10.
      pose proof H as Hop.
      unfold match_rs in RS.
      destruct b.
      + (* Fault has occurred *)
        inv_rs.
        pose proof WC_FUN as Hwc.
        inv_wc; try unify_live.
        * (* green smove *)
          repeat match goal with
                 | [ H : eval_builtin_args _  _ _ _ _ _ |- _ ] => inv H
                 | [ H : list_forall2 _ _ _ |- _ ]  => inv H
                 | [ H : eval_builtin_arg _ _ _ _ (BA _) _ |- _ ] => inv H
                 end.
          replace t with E0 in *.
          2: { symmetry; eapply external_call_green_smove_E0; eauto. }
          replace t' with E0 in *.
          2: { symmetry; eapply (@external_call_green_smove_E0 _ VoteSemantics_Three); eauto. }
          replace m' with m in *.
          2: { eapply external_call_green_smove_mem; eauto. }
          replace m'0 with m1 in *.
          2: { eapply (@external_call_green_smove_mem _ VoteSemantics_Three); eauto. }
          assert (Hlessdef: Val.lessdef vres0 vres).
          { pose proof H12 as Hext.
            apply external_call_Three_Two' in H12.
            destruct H12 as (v' & Hext' & Hv').
            eapply Events.external_call_mem_extends
              with (vargs' := [rs # arg]) in Hext'; eauto.
            2: { repeat constructor.
                 apply RS; [eapply args_in_transfer_ibuiltin; eauto; simpl; auto|].
                 intro HC; destruct c; try (inv Hc); congruence. }
            destruct Hext' as (vres' & m2' & Hext' & Hvres' & Hmem & Hmem').
            eapply external_call_deterministic in Hext'.
            2: { eapply H1. }
            destruct Hext'; subst.
            eapply Val.lessdef_trans; eauto. }
          eexists; split.
          { eapply exec_Ibuiltin; eauto.
            repeat constructor. }
          simpl in *.
          econstructor; eauto.
          { intro r.
            destruct (peq r res); subst.
            - rewrite 2!Regmap.gss.
              apply val_lessdef_compat; auto.
            - rewrite 2!Regmap.gso; auto. }
          exists c; split; auto.
          intros r Hr Hcol_ne.
          destruct (peq r res); subst.
          { rewrite 2!Regmap.gss; auto. }
          rewrite 2!Regmap.gso; auto.
          destruct (peq r arg); subst.
          { apply RS; [eapply args_in_transfer_ibuiltin; eauto; simpl; auto|].
            intro HC; destruct c; try (inv Hc); congruence. }
          assert (Hin_live: Regset.In r (live !! pc)).
          { eapply transfer_succ_subset; try eassumption. simpl; auto. }
          apply RS.
          { eapply live_in_transfer_ibuiltin; eauto. intros x Hx; inv Hx; congruence. }
          intro HC; apply Hcol_ne.
          match goal with
          | [ Hfa : Regset.For_all (fun r0 => r0 <> _ -> r0 <> _ -> _ = _) _ |- _ ] =>
              rewrite <- (Hfa r Hin_live); auto
          end.

        * (* blue smove *)
          repeat match goal with
                 | [ H : eval_builtin_args _  _ _ _ _ _ |- _ ] => inv H
                 | [ H : list_forall2 _ _ _ |- _ ]  => inv H
                 | [ H : eval_builtin_arg _ _ _ _ (BA _) _ |- _ ] => inv H
                 end.
          replace t with E0 in *.
          2: { symmetry; eapply external_call_blue_smove_E0; eauto. }
          replace t' with E0 in *.
          2: { symmetry; eapply (@external_call_blue_smove_E0 _ VoteSemantics_Three); eauto. }
          replace m' with m in *.
          2: { eapply external_call_blue_smove_mem; eauto. }
          replace m'0 with m1 in *.
          2: { eapply (@external_call_blue_smove_mem _ VoteSemantics_Three); eauto. }
          assert (Hlessdef: Val.lessdef vres0 vres).
          { pose proof H12 as Hext.
            apply external_call_Three_Two' in H12.
            destruct H12 as (v' & Hext' & Hv').
            eapply Events.external_call_mem_extends
              with (vargs' := [rs # arg]) in Hext'; eauto.
            2: { repeat constructor.
                 apply RS; [eapply args_in_transfer_ibuiltin; eauto; simpl; auto|].
                 intro HC; destruct c; try (inv Hc); congruence. }
            destruct Hext' as (vres' & m2' & Hext' & Hvres' & Hmem & Hmem').
            eapply external_call_deterministic in Hext'.
            2: { eapply H1. }
            destruct Hext'; subst.
            eapply Val.lessdef_trans; eauto. }
          eexists; split.
          { eapply exec_Ibuiltin; eauto.
            repeat constructor. }
          simpl in *.
          econstructor; eauto.
          { intro r.
            destruct (peq r res); subst.
            - rewrite 2!Regmap.gss.
              apply val_lessdef_compat; auto.
            - rewrite 2!Regmap.gso; auto. }
          exists c; split; auto.
          intros r Hr Hcol_ne.
          destruct (peq r res); subst.
          { rewrite 2!Regmap.gss; auto. }
          rewrite 2!Regmap.gso; auto.
          destruct (peq r arg); subst.
          { apply RS; [eapply args_in_transfer_ibuiltin; eauto; simpl; auto|].
            intro HC; destruct c; try (inv Hc); congruence. }
          assert (Hin_live: Regset.In r (live !! pc)).
          { eapply transfer_succ_subset; try eassumption. simpl; auto. }
          apply RS.
          { eapply live_in_transfer_ibuiltin; eauto. intros x Hx; inv Hx; congruence. }
          intro HC; apply Hcol_ne.
          match goal with
          | [ Hfa : Regset.For_all (fun r0 => r0 <> _ -> r0 <> _ -> _ = _) _ |- _ ] =>
              rewrite <- (Hfa r Hin_live); auto
          end.

        * (* vote *)
          repeat match goal with
                 | [ H : eval_builtin_args _  _ _ _ _ _ |- _ ] => inv H
                 | [ H : list_forall2 _ _ _ |- _ ]  => inv H
                 | [ H : eval_builtin_arg _ _ _ _ (BA _) _ |- _ ] => inv H
                 end.
          replace t with E0 in *.
          2: { symmetry; eapply external_call_vote_E0; eauto. }
          replace t' with E0 in *.
          2: { symmetry; eapply (@external_call_vote_E0 _ VoteSemantics_Three); eauto. }
          eexists; split.
          { eapply exec_Ibuiltin; eauto.
            repeat constructor. }
          assert (Val.lessdef vres0 vres).
          { eapply external_call_vote_lessdef
              with (vs2 := rs ## [arg1; arg2; arg3]) in H12; eauto.
            - destruct H12 as (v' & Hext & Hv').
              eapply external_call_deterministic in H1; eauto.
              destruct H1; subst; auto.
            - destruct c.
              + apply list_lessdef_mod_1_cons.
                repeat constructor.
                * apply RS; [eapply args_in_transfer_ibuiltin; eauto; simpl; auto|].
                  intro HC; congruence.
                * apply RS; [eapply args_in_transfer_ibuiltin; eauto; simpl; auto|].
                  intro HC; congruence.
              + apply list_lessdef_mod_1_cons_lessdef.
                * apply RS; [eapply args_in_transfer_ibuiltin; eauto; simpl; auto|].
                  intro HC; congruence.
                * apply list_lessdef_mod_1_cons.
                  {  repeat constructor.
                     apply RS; [eapply args_in_transfer_ibuiltin; eauto; simpl; auto|].
                     intro HC; congruence. }
              + apply list_lessdef_mod_1_cons_lessdef.
                * apply RS; [eapply args_in_transfer_ibuiltin; eauto; simpl; auto|].
                  intro HC; congruence.
                * apply list_lessdef_mod_1_cons_lessdef.
                  { apply RS; [eapply args_in_transfer_ibuiltin; eauto; simpl; auto|].
                    intro HC; congruence. }
                  { apply list_lessdef_mod_1_cons; constructor. }
              + inv Hc.
              + inv Hc. }
          econstructor; eauto.
          3: { apply external_call_vote_mem in H1; auto.
               apply external_call_vote_mem in H12; subst; auto. }
          { intro r; simpl in *.
            destruct (peq r res); subst.
            - rewrite 2!Regmap.gss.
              apply val_lessdef_compat; auto.
            - rewrite 2!Regmap.gso; auto. }
          exists c; split; auto.
          intros r Hr Hcol_ne; simpl in *.
          destruct (peq r res); subst.
          { rewrite 2!Regmap.gss; auto. }
          rewrite 2!Regmap.gso; auto.
          assert (Hin_live: Regset.In r (live !! pc)).
          { eapply transfer_succ_subset; try eassumption. simpl; auto. }
          apply RS.
          { eapply live_in_transfer_ibuiltin; eauto. intros x Hx; inv Hx; congruence. }
          intro HC; apply Hcol_ne.
          match goal with
          | [ Hfa : Regset.For_all (fun r0 => r0 <> _ -> _ = _) _ |- _ ] =>
              rewrite <- (Hfa r Hin_live); auto
          end.

        * (* safe builtin - faulted *)
          assert (Ht: t = E0) by (eapply (@safe_external_call_E0 Two VoteSemantics_Two); eauto).
          assert (Ht': t' = E0) by (eapply (@safe_external_call_E0 Three VoteSemantics_Three); eauto).
          assert (Hmem_t: m' = m) by (eapply (@safe_external_call_mem Two VoteSemantics_Two); eauto).
          assert (Hmem_s: m'0 = m1) by (eapply (@safe_external_call_mem Three VoteSemantics_Three); eauto).
          subst t t' m' m'0.
          (* val_compat of args via rs_compat *)
          assert (Hcompat_list: Forall2 val_compat vargs0 vargs).
          { pose proof H11 as H11c.
            eapply eval_builtin_args_val_compat in H11c; eauto.
            destruct H11c as (vl2 & Heval & Hfl).
            eapply eval_builtin_args_determ in Heval; [|exact H0].
            subst; auto. }
          (* val_compat of result via builtin_sem_val_compat *)
          assert (Hcompat_res: val_compat vres0 vres).
          { pose proof H12 as Hcall_src.
            eapply safe_external_call_val_compat in Hcall_src; eauto.
            destruct Hcall_src as (vres2 & Hcall2 & Hvc).
            apply external_call_Three_Two' in Hcall2.
            destruct Hcall2 as (v1 & Hcall2 & Hld1).
            eapply Events.external_call_mem_extends in Hcall2; eauto.
            2: { apply Val.lessdef_list_refl. }
            destruct Hcall2 as (v2 & m2 & Hcall3 & Hld2 & _ & _).
            eapply external_call_deterministic in Hcall3.
            2: { exact H1. }
            destruct Hcall3 as [? ?]; subst.
            eapply val_compat_trans; eauto.
            apply val_lessdef_compat.
            eapply Val.lessdef_trans; eauto. }
          eexists; split.
          { eapply exec_Ibuiltin; eauto. }
          simpl. econstructor; eauto.
          { intro r.
            destruct (peq r res); subst.
            - rewrite 2!Regmap.gss; auto.
            - rewrite 2!Regmap.gso; auto. }
          exists c; split; auto.
          intros r Hr Hcol_ne; simpl in *.
          destruct (peq r res); subst.
          { rewrite 2!Regmap.gss.
            (* col succ res ≠ c, so all arg registers have Val.lessdef *)
            assert (Hlessdef_list: Val.lessdef_list vargs0 vargs).
            { eapply eval_builtin_args_lessdef'
                with (e2 := fun r => rs # r) in H11; eauto.
              - destruct H11 as (vl2 & Heval & Hvl2).
                eapply eval_builtin_args_determ in H0; eauto; subst; auto.
              - apply Forall_forall.
                intros barg Hin_barg.
                match goal with | [ HF : Forall (builtin_arg_forall _) _ |- _ ] => rewrite Forall_forall in HF end.
                eapply builtin_arg_forall_impl_in; eauto.
                simpl; intros r Hr' Hin_r.
                apply RS.
                { eapply args_in_transfer_ibuiltin; eauto.
                  eapply in_builtin_arg_in_params_args; eauto. }
                intro HC; rewrite Hr' in HC; congruence. }
            pose proof H12 as H12_copy.
            eapply Events.external_call_mem_extends in H12_copy; eauto.
            destruct H12_copy as (vres' & m2' & Hext & Hvres' & _ & _).
            apply external_call_Three_Two' in Hext.
            destruct Hext as (v' & Hext & Hld).
            eapply external_call_deterministic in Hext.
            2: { exact H1. }
            destruct Hext as [Heq _]; subst.
            eapply Val.lessdef_trans; eauto. }
          rewrite 2!Regmap.gso; auto.
          assert (Hin_live: Regset.In r (live !! pc)).
          { eapply transfer_succ_subset; try eassumption. simpl; auto. }
          apply RS.
          { eapply live_in_transfer_ibuiltin; eauto. intros x Hx; inv Hx; congruence. }
          intro HC; apply Hcol_ne.
          match goal with
          | [ Hfa : Regset.For_all (fun r0 => r0 <> _ -> _ = _) _ |- _ ] =>
              rewrite <- (Hfa r Hin_live); auto
          end.

        * (* other builtin - faulted *)
          simpl in *.
          assert (Hlessdef_list: Val.lessdef_list vargs0 vargs).
          { eapply eval_builtin_args_lessdef'
              with (e2 := fun r => rs # r) in H11; eauto.
            - destruct H11 as (vl2 & Heval & Hvl2).
              eapply eval_builtin_args_determ in H0; eauto; subst; auto.
            - apply Forall_forall.
              intros barg Hin_barg.
              match goal with | [ HF : Forall (builtin_arg_forall _) _ |- _ ] => rewrite Forall_forall in HF end.
              eapply builtin_arg_forall_impl_in; eauto.
              simpl; intros r Hr Hin_r.
              apply RS.
              { eapply args_in_transfer_ibuiltin; eauto.
                eapply in_builtin_arg_in_params_args; eauto. }
              intro HC; rewrite Hr in HC; inv HC; inv Hc. }
          assert (exists vres' m'', @external_call _ VoteSemantics_Three
                                 ef0 (Genv.globalenv prog) vargs0 m1 t vres' m'' /\
                 Val.lessdef vres' vres /\ Memory.Mem.extends m'' m').
          { assert (match_traces (Genv.globalenv prog) t' t).
            { pose proof H12 as Hcall.
              eapply Events.external_call_mem_extends in Hcall; eauto.
              destruct Hcall as (vres' & m2' &Hcall' & Hvres' & Hm2' & Hunchanged).
              apply external_call_Three_Two' in Hcall'.
              destruct Hcall' as (v' & Hcall' & Hv').
              pose proof H1 as Hcall.
              eapply external_call_match_traces in Hcall; eauto. }
            eapply external_call_receptive in H12; eauto.
            destruct H12 as (vres' & m2 & H12).
            pose proof H12 as Hcall'.
            eapply Events.external_call_mem_extends in Hcall'; eauto.
            destruct Hcall' as (vres'' & m2' &Hcall' & Hvres' & Hm2' & Hunchanged).
            apply external_call_Three_Two' in Hcall'.
            destruct Hcall' as (v' & Hcall' & Hv').
            eapply external_call_deterministic in H1; eauto.
            destruct H1; subst.
            exists vres', m2; split; auto; split; auto.
            eapply Val.lessdef_trans; eauto. }
          destruct H2 as (vres' & m'' & Hcall & Hvres' & Hm'').
          eexists; split.
          { eapply exec_Ibuiltin; eauto. }
          econstructor; eauto.
          { destruct res0; simpl; auto.
            intro r; destruct (peq x r); subst.
            - rewrite 2!Regmap.gss; apply val_lessdef_compat; assumption.
            - rewrite 2!Regmap.gso; auto. }
          unfold match_rs in RS.
          exists c; split; auto; intros r Hr.
          assert (Hlessdef: existsb (in_builtin_argb r) args0 = true ->
                            Val.lessdef rs1 # r rs # r).
          { intro Hex.
            apply existsb_exists in Hex.
            destruct Hex as (y & Hy & Hin_argb).
            apply in_builtin_argb_sound in Hin_argb.
            pose proof Hy as Hy_orig.
            match goal with | [ HF : Forall (builtin_arg_forall _) _ |- _ ] => rewrite Forall_forall in HF; apply HF in Hy end.
            eapply in_builtin_arg_forall in Hy; eauto.
            apply RS.
            { eapply args_in_transfer_ibuiltin; eauto.
              eapply in_builtin_arg_in_params_args; eauto. }
            intro HC; rewrite Hy in HC; inv HC; inv Hc. }
          intro Hcol_ne.
          assert (Hin_live: Regset.In r (live !! pc)).
          { eapply transfer_succ_subset; try eassumption. simpl; auto. }
          destruct res0; simpl.
          { destruct (peq r x); subst.
            { rewrite 2!Regmap.gss; auto. }
            rewrite 2!Regmap.gso; auto.
            destruct (existsb (in_builtin_argb r) args0) eqn:Hex; auto.
            apply RS.
            { eapply live_in_transfer_ibuiltin; eauto.
              intros y Hy; inv Hy; congruence. }
            intro HC; apply Hcol_ne.
            match goal with
            | [ Hfa : Regset.For_all _ _ |- _ ] =>
                rewrite <- (Hfa r Hin_live)
            end.
            - exact HC.
            - intro Hexists.
              rewrite Exists_exists in Hexists.
              destruct Hexists as (y & Hy & Hin).
              assert (existsb (in_builtin_argb r) args0 = true).
              + apply existsb_exists.
                exists y; split; auto.
                destruct (in_builtin_argb_spec r y); auto.
              + congruence.
            - intros y Hy; inv Hy; assumption. }
          { destruct (existsb (in_builtin_argb r) args0) eqn:Hex; auto.
            apply RS.
            { eapply live_in_transfer_ibuiltin; try eassumption. intros x Hx; discriminate. }
            intro HC; apply Hcol_ne.
            match goal with
            | [ Hfa : Regset.For_all _ _ |- _ ] =>
                rewrite <- (Hfa r Hin_live)
            end.
            - exact HC.
            - intro Hexists.
              rewrite Exists_exists in Hexists.
              destruct Hexists as (y & Hy & Hin).
              assert (existsb (in_builtin_argb r) args0 = true).
              + apply existsb_exists.
                exists y; split; auto.
                destruct (in_builtin_argb_spec r y); auto.
                + congruence.
            - intros ? ?; discriminate. }
          (* BR_splitlong - regmap_setres is a no-op, transfer no longer kills *)
          { destruct (existsb (in_builtin_argb r) args0) eqn:Hex; auto.
            apply RS.
            { eapply live_in_transfer_ibuiltin; try eassumption.
              intros x Hx; discriminate. }
            intro HC; apply Hcol_ne.
            match goal with
            | [ Hfa : Regset.For_all _ _ |- _ ] =>
                rewrite <- (Hfa r Hin_live)
            end.
            - exact HC.
            - intro Hexists.
              rewrite Exists_exists in Hexists.
              destruct Hexists as (y & Hy & Hin).
              assert (existsb (in_builtin_argb r) args0 = true).
              + apply existsb_exists.
                exists y; split; auto.
                destruct (in_builtin_argb_spec r y); auto.
                + congruence.
            - intros ? ?; discriminate. }

      + (* Fault has not occurred *)
        pose proof WC_FUN as Hwc.
        inv_wc.
        * (* green smove *)
          repeat match goal with
                 | [ H : eval_builtin_args _  _ _ _ _ _ |- _ ] => inv H
                 | [ H : list_forall2 _ _ _ |- _ ]  => inv H
                 | [ H : eval_builtin_arg _ _ _ _ (BA _) _ |- _ ] => inv H
                 end.
          replace t with E0 in *.
          2: { symmetry; eapply external_call_green_smove_E0; eauto. }
          replace t' with E0 in *.
          2: { symmetry; eapply (@external_call_green_smove_E0 _ VoteSemantics_Three); eauto. }
          replace m' with m in *.
          2: { eapply external_call_green_smove_mem; eauto. }
          replace m'0 with m1 in *.
          2: { eapply (@external_call_green_smove_mem _ VoteSemantics_Three); eauto. }
          assert (Hlessdef: Val.lessdef vres0 vres).
          { pose proof H12 as Hext.
            apply external_call_Three_Two' in H12.
            destruct H12 as (v' & Hext' & Hv').
            eapply Events.external_call_mem_extends
              with (vargs' := [rs # arg]) in Hext'; eauto.
            destruct Hext' as (vres' & m2' & Hext' & Hvres' & Hmem & Hmem').
            eapply external_call_deterministic in Hext'.
            2: { eapply H1. }
            destruct Hext'; subst.
            eapply Val.lessdef_trans; eauto. }
          eexists; split.
          { eapply exec_Ibuiltin; eauto.
            repeat constructor. }
          simpl in *.
          econstructor; eauto.
          { intro r.
            destruct (peq r res); subst.
            - rewrite 2!Regmap.gss.
              apply val_lessdef_compat; auto.
            - rewrite 2!Regmap.gso; auto. }
          intros r.
          destruct (peq r res); subst.
          { rewrite 2!Regmap.gss; auto. }
          rewrite 2!Regmap.gso; auto.

        * (* blue smove *)
          repeat match goal with
                 | [ H : eval_builtin_args _  _ _ _ _ _ |- _ ] => inv H
                 | [ H : list_forall2 _ _ _ |- _ ]  => inv H
                 | [ H : eval_builtin_arg _ _ _ _ (BA _) _ |- _ ] => inv H
                 end.
          replace t with E0 in *.
          2: { symmetry; eapply external_call_blue_smove_E0; eauto. }
          replace t' with E0 in *.
          2: { symmetry; eapply (@external_call_blue_smove_E0 _ VoteSemantics_Three); eauto. }
          replace m' with m in *.
          2: { eapply external_call_blue_smove_mem; eauto. }
          replace m'0 with m1 in *.
          2: { eapply (@external_call_blue_smove_mem _ VoteSemantics_Three); eauto. }
          assert (Hlessdef: Val.lessdef vres0 vres).
          { pose proof H12 as Hext.
            apply external_call_Three_Two' in H12.
            destruct H12 as (v' & Hext' & Hv').
            eapply Events.external_call_mem_extends
              with (vargs' := [rs # arg]) in Hext'; eauto.
            destruct Hext' as (vres' & m2' & Hext' & Hvres' & Hmem & Hmem').
            eapply external_call_deterministic in Hext'.
            2: { eapply H1. }
            destruct Hext'; subst.
            eapply Val.lessdef_trans; eauto. }
          eexists; split.
          { eapply exec_Ibuiltin; eauto.
            repeat constructor. }
          simpl in *.
          econstructor; eauto.
          { intro r.
            destruct (peq r res); subst.
            - rewrite 2!Regmap.gss.
              apply val_lessdef_compat; auto.
            - rewrite 2!Regmap.gso; auto. }
          intros r.
          destruct (peq r res); subst.
          { rewrite 2!Regmap.gss; auto. }
          rewrite 2!Regmap.gso; auto.

        * (* vote *)
          repeat match goal with
                 | [ H : eval_builtin_args _  _ _ _ _ _ |- _ ] => inv H
                 | [ H : list_forall2 _ _ _ |- _ ]  => inv H
                 | [ H : eval_builtin_arg _ _ _ _ (BA _) _ |- _ ] => inv H
                 end.
          replace t with E0 in *.
          2: { symmetry; eapply external_call_vote_E0; eauto. }
          replace t' with E0 in *.
          2: { symmetry; eapply (@external_call_vote_E0 _ VoteSemantics_Three); eauto. }
          eexists; split.
          { eapply exec_Ibuiltin; eauto.
            repeat constructor. }
          assert (Val.lessdef vres0 vres).
          { eapply external_call_vote_lessdef
              with (vs2 := rs ## [arg1; arg2; arg3]) in H12; eauto.
            - destruct H12 as (v' & Hext & Hv').
              eapply external_call_deterministic in H1; eauto.
              destruct H1; subst; auto.
            - apply list_lessdef_mod_1_cons.
              constructor; auto. }
          econstructor; eauto.
          3: { apply external_call_vote_mem in H1; auto.
               apply external_call_vote_mem in H12; subst; auto. }
          { intro r; simpl in *.
            destruct (peq r res); subst.
            - rewrite 2!Regmap.gss.
              apply val_lessdef_compat; auto.
            - rewrite 2!Regmap.gso; auto. }
          intros r; simpl in *.
          destruct (peq r res); subst.
          { rewrite 2!Regmap.gss; auto. }
          rewrite 2!Regmap.gso; auto.

        * (* safe builtin - non-faulted *)
          assert (Ht: t = E0) by (eapply (@safe_external_call_E0 Two VoteSemantics_Two); eauto).
          assert (Ht': t' = E0) by (eapply (@safe_external_call_E0 Three VoteSemantics_Three); eauto).
          assert (Hmem_t: m' = m) by (eapply (@safe_external_call_mem Two VoteSemantics_Two); eauto).
          assert (Hmem_s: m'0 = m1) by (eapply (@safe_external_call_mem Three VoteSemantics_Three); eauto).
          subst t t' m' m'0.
          pose proof H11 as H11_save. pose proof H12 as H12_save.
          assert (Hlessdef_list: Val.lessdef_list vargs0 vargs).
          { eapply eval_builtin_args_lessdef'
              with (e2 := fun r => rs # r) in H11; eauto.
            - destruct H11 as (vl2 & Heval & Hvl2).
              eapply eval_builtin_args_determ in H0; eauto; subst; auto.
            - apply Forall_forall.
              intros barg Hin.
              eapply builtin_arg_forall_impl.
              2: { match goal with
                   | [ HF : Forall (builtin_arg_forall _) _ |- _ ] =>
                       rewrite Forall_forall in HF; apply HF in Hin; exact Hin
                   end. }
              simpl; intros; auto. }
          assert (Hlessdef: Val.lessdef vres0 vres).
          { eapply Events.external_call_mem_extends in H12; eauto.
            destruct H12 as (vres' & m2' & Hext & Hvres' & Hmem_ext & _).
            apply external_call_Three_Two' in Hext.
            destruct Hext as (v' & Hext & Hld).
            eapply external_call_deterministic in Hext.
            2: { exact H1. }
            destruct Hext as [Heq _]; subst.
            eapply Val.lessdef_trans; eauto. }
          eexists; split.
          { eapply exec_Ibuiltin; eauto. }
          simpl. econstructor; eauto.
          { intro r.
            destruct (peq r res); subst.
            - rewrite 2!Regmap.gss.
              apply val_lessdef_compat; auto.
            - rewrite 2!Regmap.gso; auto. }
          intros r.
          destruct (peq r res); subst.
          { rewrite 2!Regmap.gss; auto. }
          rewrite 2!Regmap.gso; auto.

        * (* other builtin - non-faulted *)
          simpl in *.
          assert (Hlessdef_list: Val.lessdef_list vargs0 vargs).
          { eapply eval_builtin_args_lessdef'
              with (e2 := fun r => rs # r) in H11; eauto.
            - destruct H11 as (vl2 & Heval & Hvl2).
              eapply eval_builtin_args_determ in H0; eauto; subst; auto.
            - apply Forall_forall.
              intros barg Hin.
              match goal with | [ HF : Forall (builtin_arg_forall _) _ |- _ ] => rewrite Forall_forall in HF end.
              eapply builtin_arg_forall_impl; eauto. }
          assert (exists vres' m'', @external_call _ VoteSemantics_Three
                                 ef0 (Genv.globalenv prog) vargs0 m1 t vres' m'' /\
                 Val.lessdef vres' vres /\ Memory.Mem.extends m'' m').
          { assert (match_traces (Genv.globalenv prog) t' t).
            { pose proof H12 as Hcall.
              eapply Events.external_call_mem_extends in Hcall; eauto.
              destruct Hcall as (vres' & m2' &Hcall' & Hvres' & Hm2' & Hunchanged).
              apply external_call_Three_Two' in Hcall'.
              destruct Hcall' as (v' & Hcall' & Hv').
              pose proof H1 as Hcall.
              eapply external_call_match_traces in Hcall; eauto. }
            eapply external_call_receptive in H12; eauto.
            destruct H12 as (vres' & m2 & H12).
            pose proof H12 as Hcall'.
            eapply Events.external_call_mem_extends in Hcall'; eauto.
            destruct Hcall' as (vres'' & m2' &Hcall' & Hvres' & Hm2' & Hunchanged).
            apply external_call_Three_Two' in Hcall'.
            destruct Hcall' as (v' & Hcall' & Hv').
            eapply external_call_deterministic in H1; eauto.
            destruct H1; subst.
            exists vres', m2; split; auto; split; auto.
            eapply Val.lessdef_trans; eauto. }
          destruct H2 as (vres' & m'' & Hcall & Hvres' & Hm'').
          eexists; split.
          { eapply exec_Ibuiltin; eauto. }
          econstructor; eauto.
          { destruct res0; simpl; auto.
            intro r; destruct (peq x r); subst.
            - rewrite 2!Regmap.gss; apply val_lessdef_compat; assumption.
            - rewrite 2!Regmap.gso; auto. }
          unfold match_rs in RS.
          intro r.
          assert (Hlessdef: existsb (in_builtin_argb r) args0 = true ->
                            Val.lessdef rs1 # r rs # r).
          { intro Hex.
            apply existsb_exists in Hex.
            destruct Hex as (y & Hy & Hin).
            apply in_builtin_argb_sound in Hin.
            match goal with | [ HF : Forall (builtin_arg_forall _) _ |- _ ] => rewrite Forall_forall in HF; apply HF in Hy end.
            eapply in_builtin_arg_forall in Hy; eauto. }
          destruct res0; simpl.
          { destruct (peq r x); subst.
            { rewrite 2!Regmap.gss; auto. }
            rewrite 2!Regmap.gso; auto. }
          { destruct (existsb (in_builtin_argb r) args0) eqn:Hex; auto. }
          { destruct (existsb (in_builtin_argb r) args0) eqn:Hex; auto. }

    (* exec_Icond *)
    - inv Hmatch.
      specialize (Hsafe _ (star_refl _ _ _)).
      destruct Hsafe as [[r Hfin] | (t & s'' & Hstep)].
      { inv Hfin. }
      inv Hstep; try congruence.
      eexists; split.
      { eapply exec_Icond; eauto. }
      rewrite H in H9; inv H9.
      assert (Hlessdef_list: Val.lessdef_list (rs1 ## args0 ) (rs ## args0)).
      { apply forall_lessdef_list.
        apply Forall_forall; intros r Hin.
        destruct b; auto.
        inv_rs; inv_wc.
        apply RS; [eapply args_in_transfer_icond; eauto|].
        rewrite Forall_forall in H3; apply H3 in Hin.
        intro HC; rewrite Hin in HC; inv HC; inv Hc. }
      pose proof Hlessdef_list as Hll.
      eapply Op.eval_condition_lessdef in H10; eauto.
      rewrite H0 in H10; inv H10.
      assert (Hsucc_in: forall succ, (succ = ifso0 \/ succ = ifnot0) ->
                In succ (successors_instr (Icond cond0 args0 ifso0 ifnot0))).
      { intros succ [-> | ->]; simpl; auto. }
      econstructor; eauto.
      destruct b; auto.
      inv_rs.
      assert (Hin_succ: forall r succ, (succ = ifso0 \/ succ = ifnot0) ->
                Regset.In r (ProofLiveness.transfer f succ (live !! succ)) ->
                Regset.In r (live !! pc)).
      { intros r0 succ Hsucc Hr0.
        eapply transfer_succ_subset; eauto. }
      inv_wc; try unify_live; exists c; split; auto.
      intros r Hr Hcol_ne.
      assert (Hin_live: Regset.In r (live !! pc)).
      { eapply Hin_succ; [|exact Hr].
        match goal with
        | [ |- context [if ?b then _ else _] ] => destruct b; auto
        end. }
      apply RS.
      { eapply live_in_transfer_icond; eauto. }
      intro HC.
      destruct (in_dec peq r args0).
      { rewrite Forall_forall in H3; apply H3 in i;
        rewrite i in HC; inv HC; inv Hc. }
      apply Hcol_ne.
      match goal with
      | [ Hfa : Regset.For_all _ _ |- _ ] =>
          destruct (Hfa r Hin_live n) as [Hifso Hifnot]
      end.
      (* The successor is if b_cond then ifso else ifnot; color is preserved *)
      destruct b1; [rewrite <- Hifso | rewrite <- Hifnot]; exact HC.

    (* exec_Ijumptable *)
    - inv Hmatch.
      specialize (Hsafe _ (star_refl _ _ _)).
      destruct Hsafe as [[r Hfin] | (t & s'' & Hstep)].
      { inv Hfin. }
      inv Hstep; try congruence.
      eexists; split.
      { eapply exec_Ijumptable; eauto. }
      rewrite H in H10; inv H10.
      assert (Hlessdef: Val.lessdef (rs1 # arg0) (rs # arg0)).
      { destruct b; auto; inv_rs; inv_wc.
        apply RS; [eapply arg_in_transfer_ijumptable; eauto|].
        intro HC; destruct c; try (inv Hc); congruence. }
      (* Save list_nth_z fact before destructive rewrites *)
      assert (Hin_tbl: In pc'0 tbl0).
      { eapply list_nth_z_in; eauto. }
      rewrite H0, H11 in Hlessdef; inv Hlessdef.
      rewrite H1 in H12; inv H12.
      econstructor; eauto.
      destruct b; auto.
      inv_rs.
      assert (Hsucc_subset: Regset.Subset
                (ProofLiveness.transfer f pc'0 (live !! pc'0)) (live !! pc)).
      { eapply transfer_succ_subset; eauto. }
      inv_wc; try unify_live.
      exists c; split; auto.
      intros r Hr Hcol_ne.
      assert (Hin_live: Regset.In r (live !! pc)).
      { apply Hsucc_subset; assumption. }
      destruct (peq r arg0); subst.
      + apply RS; [eapply arg_in_transfer_ijumptable; eauto|].
        intro HC; destruct c; try (inv Hc); congruence.
      + apply RS.
        { eapply live_in_transfer_ijumptable; eauto. }
        intro HC; apply Hcol_ne.
        specialize (H5 r Hin_live n0).
        rewrite Forall_forall in H5.
        rewrite <- (H5 pc'0); [exact HC | exact Hin_tbl].

    (* exec_Ireturn *)
    - inv Hmatch.
      specialize (Hsafe _ (star_refl _ _ _)).
      destruct Hsafe as [[r Hfin] | (t & s'' & Hstep)].
      { inv Hfin. }
      inv Hstep; try congruence.
      eexists; split.
      { eapply exec_Ireturn; eauto. }
      rewrite H in H9; inv H9.
      eapply Memory.Mem.free_parallel_extends in H10; eauto.
      destruct H10 as (m2' & Hfree & Hm2').
      rewrite H0 in Hfree; inv Hfree.
      econstructor; eauto.
      destruct or0; simpl; auto.
      destruct b; auto.
      inv_rs; inv_wc.
      apply RS; [eapply optarg_in_transfer_ireturn; eauto|].
      intro HC; destruct c; try (inv Hc); congruence.

    (* exec_function_internal *)
    - inv Hmatch.
      specialize (Hsafe _ (star_refl _ _ _)).
      destruct Hsafe as [[r Hfin] | (t & s'' & Hstep)].
      { inv Hfin. }
      inv Hstep; try congruence.
      eexists; split.
      { eapply exec_function_internal; eauto. }
      eapply Memory.Mem.alloc_extends
        with (lo2 := 0) (hi2 := fn_stacksize f) in H8; eauto; try reflexivity.
      destruct H8 as (m2' & Halloc & Hm2').
      rewrite H0 in Halloc; inv Halloc.
      destruct WC_FD as (col0 & Hwc0).
      inv Hwc0.
      econstructor; eauto.
      { econstructor; eauto. }
      { apply forall2_lessdef_rs_compat_init_regs; assumption. }
      { apply forall2_lessdef_match_rs_init_regs; assumption. }

    (* exec_function_external *)
    - inv Hmatch.
      specialize (Hsafe _ (star_refl _ _ _)).
      destruct Hsafe as [[r Hfin] | (t' & s'' & Hstep)].
      { inv Hfin. }
      inv Hstep; try congruence.
      simpl in *.
      assert (Hext: exists res' m'', @external_call _ VoteSemantics_Three
                                  ef (Genv.globalenv prog) args1 m1 t res' m'' /\
                                  Val.lessdef res' res /\ Memory.Mem.extends m'' m').
      { assert (match_traces (Genv.globalenv prog) t' t).
        { pose proof H6 as Hcall.
          eapply Events.external_call_mem_extends in Hcall; eauto.
          destruct Hcall as (res' & m2' &Hcall' & Hres' & Hm2' & Hunchanged).
          apply external_call_Three_Two' in Hcall'.
          destruct Hcall' as (v' & Hcall' & Hv').
          pose proof H as Hcall.
          eapply external_call_match_traces in Hcall; eauto.
          apply forall2_lessdef_list; assumption. }
        eapply external_call_receptive in H6; eauto.
        destruct H6 as (res' & m2 & H6).
        pose proof H6 as Hcall'.
        eapply Events.external_call_mem_extends in Hcall'; eauto.
        2: { apply forall2_lessdef_list; eassumption. }
        destruct Hcall' as (res'' & m2' &Hcall' & Hres' & Hm2' & Hunchanged).
        apply external_call_Three_Two' in Hcall'.
        destruct Hcall' as (v' & Hcall' & Hv').
        eapply external_call_deterministic in H; eauto.
        destruct H; subst.
        exists res', m2; split; auto; split; auto.
        eapply Val.lessdef_trans; eauto. }
      destruct Hext as (res' & m'' & Hcall & Hres' & Hm'').
      eexists; split.
      { eapply exec_function_external; eauto. }
      econstructor; eauto.

    (* exec_return *)
    - inv Hmatch.
      specialize (Hsafe _ (star_refl _ _ _)).
      destruct Hsafe as [[r Hfin] | (t & s'' & Hstep)].
      { inv Hfin; inv STK. }
      inv Hstep; try congruence.
      eexists; split.
      { eapply exec_return; eauto. }
      inv STK.
      inv H2.
      econstructor; eauto.
      + intro x.
        destruct (peq x res); subst.
        * rewrite 2!Regmap.gss.
          apply val_lessdef_compat; assumption.
        * rewrite 2!Regmap.gso; auto.
      + unfold match_rs_upto in RS.
        unfold match_rs.
        destruct b.
        * destruct RS as (c & Hc & RS).
          exists c; split; auto.
          intros r Hr Hcol_ne.
          destruct (peq r res); subst.
          { rewrite 2!Regmap.gss; auto. }
          rewrite 2!Regmap.gso; [|assumption|assumption].
          apply RS; assumption.
        * intro r.
          destruct (peq r res); subst.
          { rewrite 2!Regmap.gss; auto. }
          rewrite 2!Regmap.gso; auto.
  Qed.

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
    - eapply step_simulation in STEP; eauto.
      destruct STEP as (i' & s1' & Hstep & Hmatch').
      replace i with b in *.
      2: { apply match_states_fault_inv in Hmatch; auto. }
      replace i' with b in *.
      2: { apply match_states_fault_inv in Hmatch'; auto. }
      exists b', s1'; split.
      + left; apply plus_one; auto.
      + eapply maybe_zap_preserves_match_states; eauto.
    - eapply step_simulation in STEP; eauto.
      destruct STEP as (i' & s1' & Hstep & Hmatch').
      replace i with b in *.
      2: { apply match_states_fault_inv in Hmatch; auto. }
      replace i' with b in *.
      2: { apply match_states_fault_inv in Hmatch'; auto. }
      exists b, s1'; split; auto.
      left; apply plus_one; auto.
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
      + specialize (Hsafe _ (star_refl _ _ _)).
        destruct Hsafe as [[r' Hfin] | (t & s'' & Hstep)].
        * inv Hfin; inv LESSDEF; constructor.
        * inv Hstep.
    - (* bsim_progress *)
      apply faulty_progress.
    - (* bsim_simulation *)
      apply faulty_simulation.
    - (* bsim_public_preserved *)
      intros; reflexivity.
  Qed.

End TOLERANCE.
