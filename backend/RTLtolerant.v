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

Definition match_rs
  (col : reg -> option color) (faulted : bool) (rs1 rs2 : regset) : Prop :=
  if faulted then
    exists c, is_basic c /\
           forall r, col r <> Some c -> Val.lessdef (rs1 # r) (rs2 # r)
  else
    forall r, Val.lessdef (rs1 # r) (rs2 # r).

Definition match_rs_upto (res : reg)
  (col : reg -> option color) (faulted : bool) (rs1 rs2 : regset) : Prop :=
  if faulted then
    exists c, is_basic c /\
           forall r, r <> res -> col r <> Some c -> Val.lessdef (rs1 # r) (rs2 # r)
  else
    forall r, r <> res -> Val.lessdef (rs1 # r) (rs2 # r).

Lemma match_rs_match_rs_upto res col faulted rs1 rs2 :
  match_rs col faulted rs1 rs2 ->
  match_rs_upto res col faulted rs1 rs2.
Proof.
  unfold match_rs, match_rs_upto; intro RS.
  destruct faulted; auto.
  destruct RS as (c & Hc & RS).
  exists c; split; auto.
Qed.

Definition rs_compat (rs1 rs2 : regset) : Prop :=
  forall r, val_compat (rs1 # r) (rs2 # r).

Section match_states.

  (* (** When a fault has occurred elsewhere and regsets [rs1] and [rs2] *)
  (*     are unchanged, they still match. *) *)
  (* Lemma match_rs_fault col (pc : node) (rs1 rs2 : regset) : *)
  (*   match_rs (col pc) false rs1 rs2 -> *)
  (*   match_rs (col pc) true rs1 rs2. *)
  (* Proof. intro H; exists Red; split; auto; constructor. Qed. *)

  (** When a fault has occurred elsewhere and regsets [rs1] and [rs2]
      are unchanged, they still match. *)
  Lemma match_rs_upto_fault res col (pc : node) (rs1 rs2 : regset) :
    match_rs_upto res (col pc) false rs1 rs2 ->
    match_rs_upto res (col pc) true rs1 rs2.
  Proof. intro H; exists Red; split; auto; constructor. Qed.

  Inductive match_stackframes (faulted : bool)
    : RTL.stackframe -> RTL.stackframe -> Prop :=
  | match_stackframes_Stackframe :
    forall col res f sp pc rs1 rs2
      (WC_FUN: wc_function col f)
      (RS_COMPAT: rs_compat rs1 rs2)
      (RS: match_rs_upto res (col pc) faulted rs1 rs2),
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
      registers except those of the affected color. *)
  Inductive match_states : bool -> RTL.state -> fstate -> Prop :=
  | match_states_State :
    forall col stk1 stk2 f sp pc rs1 rs2 m1 m2 (b : bool)
      (STK: Forall2 (match_stackframes b) stk1 stk2)
      (* (VOTE: match_votes_function f1 f2) *)
      (WC_FUN: wc_function col f)
      (RS_COMPAT: rs_compat rs1 rs2)
      (RS: match_rs (col pc) b rs1 rs2)
      (MEM: Memory.Mem.extends m1 m2),
      match_states b (State stk1 f sp pc rs1 m1)
                   {| fs_state := State stk2 f sp pc rs2 m2; fault := b |}
  | match_states_Callstate :
    forall stk1 stk2 fd args1 args2 m1 m2 b
      (STK: Forall2 (match_stackframes b) stk1 stk2)
      (* (VOTE: match_votes_fundef fd1 fd2) *)
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

Lemma init_match_states_refl p s :
  RTL.initial_state p s ->
  match_states false s {| fs_state := s; fault := false |}.
Proof.
  intro Hinit; inv Hinit.
  constructor; auto.
  apply Memory.Mem.extends_refl.
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
    | [ Hwc : wc_code _ _, Hpc : (fn_code _) ! _ = Some _ |- _ ] =>
        apply Hwc in Hpc; inv Hpc; try congruence
    end.

  Lemma wc_col_succ_exists f col pc i r succ :
    (fn_code f) ! pc = Some i ->
    res_of_instruction i = Some r ->
    succ_of_instruction i = Some succ ->
    wc_function col f ->
    exists c, col succ r = Some c.
  Proof.
    intros Hpc Hr Hsucc Hwc.
    inv_wc; simpl in *; try congruence; inv Hr; inv Hsucc;
      try solve [exists White; auto]; try solve [eexists; eauto].
    - inv H0; eexists; eauto.
    - destruct bres; simpl in *; try congruence.
      inv H5; exists White; auto.
  Qed.

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
      assert (Hc: exists c, col pc' r = Some c /\ is_basic c).
      { pose proof H0 as Hop.
        inv Hmatch.
        eapply step_succ in Hstep; eauto.
        clear WC_FUN0.
        inv_wc; simpl in *; try congruence; inv H2; inv Hstep; try contradiction.
        inv H4; exists c; split; eauto. }
      destruct Hc as (c & Hr & Hc).
      exists c; split; auto.
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
          is_basic c /\ (forall r : reg, ?col ?pc r <> Some c ->
                                   Val.lessdef (?rs1 # r) (?rs2 # r)) |- _ ] =>
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

  Lemma val_compat_shrx v1 v2 vres n :
    val_compat v1 v2 ->
    Val.shrx v1 (Vint n) = Some vres ->
    exists vres' : val, Val.shrx v2 (Vint n) = Some vres'.
  Proof.
    intros Hcompat Hshrx.
    inv Hcompat; simpl in *; try congruence.
    destruct (Integers.Int.ltu _ _); inv Hshrx.
    eexists; reflexivity.
  Qed.

  Lemma val_compat_shrxl v1 v2 vres n :
    val_compat v1 v2 ->
    Val.shrxl v1 (Vint n) = Some vres ->
    exists vres' : val, Val.shrxl v2 (Vint n) = Some vres'.
  Proof.
    intros Hcompat Hshrxl.
    inv Hcompat; simpl in *; try congruence.
    destruct (Integers.Int.ltu _ _); inv Hshrxl.
    eexists; reflexivity.
  Qed.

  Lemma val_compat_floatofint v1 v2 vres :
    val_compat v1 v2 ->
    Val.floatofint v1 = Some vres ->
    exists vres' : val, Val.floatofint v2 = Some vres'.
  Proof.
    intros Hcompat Hfoi.
    inv Hcompat; simpl in *; try congruence.
    eexists; reflexivity.
  Qed.

  Lemma val_compat_singleofint v1 v2 vres :
    val_compat v1 v2 ->
    Val.singleofint v1 = Some vres ->
    exists vres' : val, Val.singleofint v2 = Some vres'.
  Proof.
    intros Hcompat Hsoi.
    inv Hcompat; simpl in *; try congruence.
    eexists; reflexivity.
  Qed.

  Lemma val_compat_floatoflong v1 v2 vres :
    val_compat v1 v2 ->
    Val.floatoflong v1 = Some vres ->
    exists vres' : val, Val.floatoflong v2 = Some vres'.
  Proof.
    intros Hcompat Hfol.
    inv Hcompat; simpl in *; try congruence.
    eexists; reflexivity.
  Qed.

  Lemma val_compat_singleoflong v1 v2 vres :
    val_compat v1 v2 ->
    Val.singleoflong v1 = Some vres ->
    exists vres' : val, Val.singleoflong v2 = Some vres'.
  Proof.
    intros Hcompat Hsol.
    inv Hcompat; simpl in *; try congruence.
    eexists; reflexivity.
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
    - eapply val_compat_shrx; eauto.
    - eapply val_compat_eval_addressing32; eauto.
    - eapply val_compat_eval_addressing32; eauto.
    - eapply val_compat_shrxl; eauto.
    - eapply val_compat_eval_addressing64; eauto.
    - eapply val_compat_eval_addressing64; eauto.
    - eapply val_compat_floatofint; eauto.
    - eapply val_compat_singleofint; eauto.
    - eapply val_compat_floatoflong; eauto.
    - eapply val_compat_singleoflong; eauto.
  Qed.

  Lemma val_compat_divs n1 n2 d1 d2 v1 v2 :
    val_compat n1 n2 ->
    val_compat d1 d2 ->
    Val.divs n1 d1 = Some v1 ->
    Val.divs n2 d2 = Some v2 ->
    val_compat v1 v2.
  Proof.
    intros Hn Hd Hdiv1 Hdiv2.
    inv Hn; inv Hd; simpl in *; try congruence.
    destruct (Integers.Int.eq _ _); simpl in *; try congruence.
    destruct (Integers.Int.eq _ _); simpl in *; try congruence.
    - destruct (Integers.Int.eq _ _); simpl in *; try congruence.
      inv Hdiv1.
      destruct (Integers.Int.eq _ _); simpl in *; try congruence.
      destruct (Integers.Int.eq _ _); simpl in *; try congruence.
      + destruct (Integers.Int.eq _ _); simpl in *; try congruence.
        inv Hdiv2; constructor.
      + inv Hdiv2; constructor.
    - inv Hdiv1.
      destruct (Integers.Int.eq _ _); simpl in *; try congruence.
      destruct (Integers.Int.eq _ _); simpl in *; try congruence.
      + destruct (Integers.Int.eq _ _); simpl in *; try congruence.
        inv Hdiv2; constructor.
      + inv Hdiv2; constructor.
  Qed.

  Lemma val_compat_divu n1 n2 d1 d2 v1 v2 :
    val_compat n1 n2 ->
    val_compat d1 d2 ->
    Val.divu n1 d1 = Some v1 ->
    Val.divu n2 d2 = Some v2 ->
    val_compat v1 v2.
  Proof.
    intros Hn Hd Hdiv1 Hdiv2.
    inv Hn; inv Hd; simpl in *; try congruence.
    repeat destruct (Integers.Int.eq _ _); simpl in *; try congruence.
    inv Hdiv1; inv Hdiv2; constructor.
  Qed.

  Lemma val_compat_mods n1 n2 d1 d2 v1 v2 :
    val_compat n1 n2 ->
    val_compat d1 d2 ->
    Val.mods n1 d1 = Some v1 ->
    Val.mods n2 d2 = Some v2 ->
    val_compat v1 v2.
  Proof.
    intros Hn Hd Hmod1 Hmod2.
    inv Hn; inv Hd; simpl in *; try congruence.
    destruct (Integers.Int.eq _ _); simpl in *; try congruence.
    destruct (Integers.Int.eq _ _); simpl in *; try congruence.
    - destruct (Integers.Int.eq _ _); simpl in *; try congruence.
      inv Hmod1.
      destruct (Integers.Int.eq _ _); simpl in *; try congruence.
      destruct (Integers.Int.eq _ _); simpl in *; try congruence.
      + destruct (Integers.Int.eq _ _); simpl in *; try congruence.
        inv Hmod2; constructor.
      + inv Hmod2; constructor.
    - inv Hmod1.
      destruct (Integers.Int.eq _ _); simpl in *; try congruence.
      destruct (Integers.Int.eq _ _); simpl in *; try congruence.
      + destruct (Integers.Int.eq _ _); simpl in *; try congruence.
        inv Hmod2; constructor.
      + inv Hmod2; constructor.
  Qed.

  Lemma val_compat_modu n1 n2 d1 d2 v1 v2 :
    val_compat n1 n2 ->
    val_compat d1 d2 ->
    Val.modu n1 d1 = Some v1 ->
    Val.modu n2 d2 = Some v2 ->
    val_compat v1 v2.
  Proof.
    intros Hn Hd Hmod1 Hmod2.
    inv Hn; inv Hd; simpl in *; try congruence.
    repeat destruct (Integers.Int.eq _ _); simpl in *; try congruence.
    inv Hmod1; inv Hmod2; constructor.
  Qed.

  Lemma eval_operation_val_compat rs1 rs2 sp op args m1 m2 v v' :
    rs_compat rs1 rs2 ->
    Op.eval_operation (Genv.globalenv prog) sp op rs1 ## args m1 = Some v ->
    Op.eval_operation (Genv.globalenv prog) sp op rs2 ## args m2 = Some v' ->
    val_compat v v'.
  Proof.
    intros Hcompat H0 H1.
    destruct op; simpl in *;
      try solve [destruct args; simpl in *; try congruence;
                 try solve [inv H0; inv H1; constructor];
                 try solve [inv H0; inv H1; apply val_compat_refl];
                 destruct args; simpl in *; try congruence;
                 inv H0; inv H1; auto];
      try solve [do 2 (destruct args; simpl in *; try congruence);
                 inv H0; inv H1;
                 specialize (Hcompat p); inv Hcompat; simpl;
                 try apply val_compat_refl; constructor];
      try solve [do 3 (destruct args; simpl in *; try congruence);
                 inv H0; inv H1;
                 pose proof (Hcompat p0) as Hp0; specialize (Hcompat p);
                 inv Hp0; inv Hcompat; constructor].
    - do 3 (destruct args; simpl in *; try congruence).
      eapply val_compat_divs; eauto.
    - do 3 (destruct args; simpl in *; try congruence).
      eapply val_compat_divu; eauto.
    - do 3 (destruct args; simpl in *; try congruence).
      eapply val_compat_mods; eauto.
    - do 3 (destruct args; simpl in *; try congruence).
      eapply val_compat_modu; eauto.
    - do 3 (destruct args; simpl in *; try congruence).
      inv H0; inv H1.
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

  (* Lemma rs_eq_map {A : Type} (rs1 rs2 : Regmap.t A) args : *)
  (*   Forall (fun a => rs1 # a = rs2 # a) args -> *)
  (*   rs1 ## args = rs2 ## args. *)
  (* Proof. *)
  (*   induction args; simpl; intro Hforall; auto. *)
  (*   inv Hforall; rewrite H1, IHargs; auto. *)
  (* Qed. *)
  
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

  (* Fixpoint builtin_arg_rs_eq (rs1 rs2 : Regmap.t val) (barg : builtin_arg reg) : Prop := *)
  (*   match barg with *)
  (*   | BA r => rs1 # r = rs2 # r *)
  (*   | BA_splitlong hi lo => builtin_arg_rs_eq rs1 rs2 hi /\ builtin_arg_rs_eq rs1 rs2 lo *)
  (*   | BA_addptr a1 a2 => builtin_arg_rs_eq rs1 rs2 a1 /\ builtin_arg_rs_eq rs1 rs2 a2 *)
  (*   | _ => True *)
  (*   end. *)

  (* Lemma in_builtin_arg_rs_eq rs1 rs2 arg : *)
  (*   (forall r, in_builtin_arg r arg -> rs1 # r = rs2 # r) -> *)
  (*   builtin_arg_rs_eq rs1 rs2 arg. *)
  (* Proof. *)
  (*   induction arg; simpl; intros Hin; auto. *)
  (*   - apply Hin; constructor. *)
  (*   - split; try apply IHarg1; try apply IHarg2; *)
  (*       intros x Hx; apply Hin; solve [constructor; auto]. *)
  (*   - split; try apply IHarg1; try apply IHarg2; *)
  (*       intros x Hx; apply Hin; solve [constructor; auto]. *)
  (* Qed. *)

  (* Lemma rs_eq_eval_builtin_arg rs1 rs2 barg sp m b : *)
  (*   builtin_arg_rs_eq rs1 rs2 barg -> *)
  (*   eval_builtin_arg (Genv.globalenv prog) (fun r : positive => rs1 # r) sp m barg b -> *)
  (*   eval_builtin_arg (Genv.globalenv prog) (fun r : positive => rs2 # r) sp m barg b. *)
  (* Proof. *)
  (*   revert b. *)
  (*   induction barg; simpl; intros b Heq Heval; inv Heval; try solve [constructor; auto]. *)
  (*   - rewrite Heq; constructor. *)
  (*   - destruct Heq as [Heq0 Heq1]; constructor; auto. *)
  (*   - destruct Heq as [Heq0 Heq1]; constructor; auto. *)
  (* Qed. *)

  (* Lemma rs_eq_eval_builtin_args rs1 rs2 sp m args vargs : *)
  (*   Forall (builtin_arg_rs_eq rs1 rs2) args -> *)
  (*   eval_builtin_args (Genv.globalenv prog) (fun r : positive => rs1 # r) sp m args vargs -> *)
  (*   eval_builtin_args (Genv.globalenv prog) (fun r : positive => rs2 # r) sp m args vargs. *)
  (* Proof. *)
  (*   revert vargs; induction args; intro vargs; *)
  (*     intros Hforall Heval; inv Heval; constructor; inv Hforall. *)
  (*   - eapply rs_eq_eval_builtin_arg; eauto. *)
  (*   - apply IHargs; auto. *)
  (* Qed. *)

  Ltac inv_stk :=
    match goal with
    | [ H : Forall2 (match_stackframes false)
              (Stackframe ?res ?f ?sp ?pc ?rs :: ?s) ?stk2 |- _ ] =>
        inv H
    end.

  (* Ltac inv_match_rs := *)
  (*   inv_wc; *)
  (*   erewrite rs_eq_map; eauto; apply Forall_forall; intros r Hin; *)
  (*   match goal with *)
  (*   | [ Hrs : match_rs _ true _ _ |- _ ] => *)
  (*       destruct Hrs as (c & Hc & Hrs); rewrite Hrs; auto; *)
  (*       match goal with *)
  (*       | [ H : Forall (fun arg : reg => is_white _ /\ is_red _) _ |- _ ] => *)
  (*           rewrite Forall_forall in H; *)
  (*           apply H in Hin; destruct Hin as [Hwhite _]; *)
  (*           intros HC; rewrite Hwhite in HC; inv HC; inv Hc *)
  (*       end *)
  (*   end. *)

  (* Ltac inv_match_rs' := *)
  (*   inv_wc; *)
  (*   match goal with *)
  (*   | [ Hrs : match_rs _ true _ _, Hwhite : is_white _ |- _ ] => *)
  (*       destruct Hrs as (c & Hc & Hrs); rewrite <- Hrs; eauto; *)
  (*       intros HC; rewrite Hwhite in HC; inv HC; inv Hc *)
  (*   end. *)

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
        destruct v0; inv H0; eexists; eexists; constructor; reflexivity.
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
    
  (* Lemma builtin_or_external_sem_Three_Two name sg vargs m t v m' : *)
  (*   @builtin_or_external_sem Three VoteSemantics_Three *)
  (*     name sg (Genv.globalenv prog) vargs m t v m' -> *)
  (*   exists v' m'', @builtin_or_external_sem Two VoteSemantics_Two *)
  (*               name sg (Genv.globalenv prog) vargs m t v' m''. *)
  (* Proof. *)
  (*   unfold builtin_or_external_sem. *)
  (*   intro Hsem. *)
  (*   destruct (Builtins.lookup_builtin_function _ _) eqn:Hlookup. *)
  (*   -  unfold Builtins.lookup_builtin_function in *. *)
  (*      simpl in *. *)
  (*      destruct (string_dec name _ && signature_eq sg _%asttyp); *)
  (*        eapply known_builtin_sem_Three_Two; eauto. *)
  (*   - eexists; eexists; eauto. *)
  (* Qed. *)
  
  Lemma builtin_or_external_sem_Three_Two name sg vargs m t v m' :
    @builtin_or_external_sem Three VoteSemantics_Three
      name sg (Genv.globalenv prog) vargs m t v m' ->
    exists v', @builtin_or_external_sem Two VoteSemantics_Two
            name sg (Genv.globalenv prog) vargs m t v' m'.
  Proof.
    unfold builtin_or_external_sem.
    intro Hsem.
    destruct (Builtins.lookup_builtin_function _ _) eqn:Hlookup.
    -  unfold Builtins.lookup_builtin_function in *.
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
    -  unfold Builtins.lookup_builtin_function in *.
       simpl in *.
       destruct (string_dec name _ && signature_eq sg _%asttyp);
         eapply known_builtin_sem_Three_Two'; eauto.
    - eexists; eauto.
  Qed.

  (* Lemma external_call_Three_Two ef vargs m t v m' : *)
  (*   @external_call Three VoteSemantics_Three *)
  (*     ef (Genv.globalenv prog) vargs m t v m' -> *)
  (*   exists v' m'', @external_call Two VoteSemantics_Two *)
  (*               ef (Genv.globalenv prog) vargs m t v' m''. *)
  (* Proof. *)
  (*   intro Hef. *)
  (*   destruct ef; simpl in *; *)
  (*     try solve [eexists; eexists; eauto]; *)
  (*     eapply builtin_or_external_sem_Three_Two; eauto. *)
  (* Qed. *)

  (* TODO: remove this and replace with better version below. *)
  Lemma external_call_Three_Two ef vargs m t v m' :
    @external_call Three VoteSemantics_Three
      ef (Genv.globalenv prog) vargs m t v m' ->
    exists v', @external_call Two VoteSemantics_Two
            ef (Genv.globalenv prog) vargs m t v' m'.
  Proof.
    intro Hef.
    destruct ef; simpl in *;
      try solve [eexists; eauto];
      eapply builtin_or_external_sem_Three_Two; eauto.
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

  (* Inductive list_eq_mod_1 {A : Type} : list A -> list A -> Prop := *)
  (* | list_eq_mod_1_nil : list_eq_mod_1 nil nil *)
  (* | list_eq_mod_1_cons_eq : forall x l1 l2, *)
  (*     list_eq_mod_1 l1 l2 -> *)
  (*     list_eq_mod_1 (x :: l1 ) (x :: l2) *)
  (* | list_eq_mod_1_cons_neq : forall x y l, *)
  (*     x <> y -> *)
  (*     list_eq_mod_1 (x :: l) (y :: l). *)

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

  (* Lemma lessdef_vote3_vote x x0 x1 y y0 y1 : *)
  (*   Val.lessdef x y -> *)
  (*   Val.lessdef x0 y0 -> *)
  (*   Val.lessdef x1 y1 -> *)
  (*   Val.lessdef (vote3 Tint x x0 x1) (vote Tint y y0 y1). *)
  (* Proof. *)
  (*   intros H0 H1 H2. *)
  (*   unfold vote3, vote. *)
  (*   inv H0; inv H1; inv H2; simpl; *)
  (*     destruct (Val.has_type_dec _ _); simpl; try constructor; *)
  (*     destruct (Val.eq _ _); simpl; try constructor; subst; *)
  (*     destruct (Val.eq _ _); subst; simpl; constructor. *)
  (* Qed. *)
  
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

  Lemma external_call_smove_E0 {VT: Builtins2.vote_type} {vsem: Builtins2.VoteSemantics VT}
    ef vs m t v m' :
    is_smove_builtin ef ->
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

  Lemma external_call_smove_mem {VT: Builtins2.vote_type} {vsem: Builtins2.VoteSemantics VT}
    ef vs m t v m' :
    is_smove_builtin ef ->
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

  (* Lemma external_call_smove_res {VT: Builtins2.vote_type} {vsem: Builtins2.VoteSemantics VT} *)
  (*   ef m t v v' m' : *)
  (*   is_smove_builtin ef -> *)
  (*   external_call ef (Genv.globalenv prog) [v] m t v' m' -> *)
  (*   v' = v. *)
  (* Proof. *)
  (*   intros Hef Hcall. *)
  (*   unfold external_call, builtin_or_external_sem, *)
  (*     Builtins.lookup_builtin_function in Hcall. *)
  (*   simpl in Hcall. *)
  (*   inv Hef; simpl in *; destruct (signature_eq _ _); *)
  (*     try congruence; inv Hcall; auto. *)
  (*   simpl in *. *)
  (*   - destruct v; simpl in *; inv H; auto. *)
  (* Qed. *)

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

  (* TODO: the four cases in this proof are literally the same except
     the type argument to [vote]. *)
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
    - destruct (is_unsafeb_spec op).
      + (* op is unsafe *)
        eapply Op.eval_operation_lessdef with (vl2 := rs2 ## args) in H0; eauto.
        2: { apply forall_lessdef_list.
             apply Forall_forall; intros r Hin.
             unfold match_rs in RS.
             destruct fault; auto.
             inv_rs; inv_wc.
             apply RS.
             rewrite Forall_forall in H6; apply H6 in Hin.
             intro HC; rewrite Hin in HC; inv HC; inv Hc. }
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
           unfold match_rs in RS.
           destruct fault; auto.
           inv_rs; inv_wc.
           apply RS.
           rewrite Forall_forall in H5; apply H5 in Hin.
           intro HC; rewrite Hin in HC; inv HC; inv Hc. }
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
           unfold match_rs in RS.
           destruct fault; auto.
           inv_rs; inv_wc.
           apply RS.
           rewrite Forall_forall in H8; apply H8 in Hin.
           intro HC; rewrite Hin in HC; inv HC; inv Hc. }
      destruct H0 as (v2 & Hop & Hv2).
      eapply Memory.Mem.storev_extends in H1.
      2: { eauto. }
      2: { eauto. }
      2: { unfold match_rs in RS.
           destruct fault.
           - inv_rs; inv_wc.
             apply RS.
             intro HC; rewrite H4 in HC; inv HC; inv Hc.
             - auto. }
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
             - inv_rs; inv_wc.
               apply RS.
               intro HC; rewrite H5 in HC; auto; inv HC; inv Hc.
             - auto. }
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
             - inv_rs; inv_wc.
               apply RS.
               intro HC; rewrite H3 in HC; auto; inv HC; inv Hc.
             - auto. }
        eexists; econstructor.
        2: { apply maybe_zap_refl. }
        eapply exec_Itailcall; eauto.
      + eexists; econstructor.
        2: { apply maybe_zap_refl. }
        eapply exec_Itailcall; eauto.

    (* exec_Ibuiltin *)
    - destruct (is_vote_builtinb_spec ef) as [Hbuiltin|Hbuiltin].
      + pose proof H as Hpc.
        inv_wc; try solve [apply vote_not_smove in Hbuiltin; congruence].
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
             apply external_call_Three_Two in Hext.
             destruct Hext as [v' Hext].
             eexists; econstructor.
             2: { apply maybe_zap_refl. }
             eapply exec_Ibuiltin; eauto.
             repeat constructor. }
        eapply external_call_vote_lessdef
          with (vs2 := rs2 ## (arg1 :: arg2 :: arg3 :: nil)) in H1; eauto.
        destruct H1 as (v' & Hext & Hv').
        2: { inv_rs.
             destruct c.
             - apply list_lessdef_mod_1_cons.
               repeat constructor.
               + apply RS; intro HC; rewrite H8 in HC; inv HC.
               + apply RS; intro HC; rewrite H9 in HC; inv HC.
             - apply list_lessdef_mod_1_cons_lessdef.
               { apply RS; intro HC; rewrite H7 in HC; inv HC. }
               apply list_lessdef_mod_1_cons.
               repeat constructor.
               + apply RS; intro HC; rewrite H9 in HC; inv HC.
             - apply list_lessdef_mod_1_cons_lessdef.
               { apply RS; intro HC; rewrite H7 in HC; inv HC. }
               apply list_lessdef_mod_1_cons_lessdef.
               { apply RS; intro HC; rewrite H8 in HC; inv HC. }
               apply list_lessdef_mod_1_cons.
               repeat constructor.
             - inv Hc.
             - inv Hc. }
        eexists; econstructor.
        2: { apply maybe_zap_refl. }
        eapply exec_Ibuiltin; eauto.
        repeat constructor.
      + unfold match_rs in RS.
        eapply eval_builtin_args_lessdef' with (e2 := fun r => rs2 # r) in H0; eauto.
        2: { apply Forall_forall.
             intros barg Hin.
             inv_wc.
             - inv Hin; simpl.
               + unfold match_rs in RS.
                 destruct fault; auto.
                 inv_rs; apply RS.
                 intro HC; rewrite H7 in HC; inv HC; inv Hc.
               + inv H.
             - inv Hin; simpl.
               + unfold match_rs in RS.
                 destruct fault; auto.
                 inv_rs; apply RS.
                 intro HC; rewrite H7 in HC; inv HC; inv Hc.
               + inv H.
             - rewrite Forall_forall in H8.
               apply H8 in Hin.
               destruct fault.
               + inv_rs.
                 eapply builtin_arg_forall_impl; eauto.
                 simpl; intros a Ha.
                 apply RS; intro HC; rewrite Ha in HC; inv HC; inv Hc.
               + eapply builtin_arg_forall_impl with (P := fun _ => True); auto.
                 apply builtin_arg_forall_true. }
        destruct H0 as (vl2 & Heval & Hvl2).
        eapply external_call_mem_extends in H1; eauto.
        destruct H1 as (vres' & m2' & Hext & Hvres' & Hmem & Hmem').
        apply external_call_Three_Two in Hext.
        destruct Hext as [v' Hext].
        eexists; econstructor.
        2: { apply maybe_zap_refl. }
        eapply exec_Ibuiltin; eauto.

    (* exec_Icond *)
    - simpl in *.
      eapply Op.eval_condition_lessdef in H0.
      2: { apply forall_lessdef_list.
           apply Forall_forall; intros r Hin.
           destruct fault.
           - inv_rs; inv_wc.
             rewrite Forall_forall in H3; apply H3 in Hin.
             apply RS; intro HC; rewrite Hin in HC; inv HC; inv Hc.
           - auto. }
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
        - inv_rs; inv_wc.
          apply RS; intro HC; rewrite H4 in HC; inv HC; inv Hc.
        - auto. }
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

  (* Lemma external_call_mem_extends *)
  (*   {VT1: Builtins2.vote_type} {vsem1: Builtins2.VoteSemantics VT1} *)
  (*   {VT2: Builtins2.vote_type} {vsem2: Builtins2.VoteSemantics VT2} *)
  (*   ef vargs1 vargs2 m1 m2 t vres1 vres2 m1' m2' : *)
  (*   Val.lessdef_list vargs1 vargs2 -> *)
  (*   Memory.Mem.extends m1 m2 -> *)
  (*   @external_call VT1 vsem1 ef (Genv.globalenv prog) vargs1 m1 t vres1 m1' -> *)
  (*   @external_call VT2 vsem2 ef (Genv.globalenv prog) vargs2 m2 t vres2 m2' -> *)
  (*   Memory.Mem.extends m1' m2'. *)
  (* Proof. *)
  (*   intros Hlessdef Hmem Hext1 Hext2. *)
  (*   eapply external_call_mem_extends in Hext1; eauto. *)
  (*   destruct Hext1 as (vres' & m2'' & Hext1 & Hld & Hmem' & Hmem''). *)
  (*   eapply external_call_deterministic in Hext2; eauto. *)
  (*   destruct Hext2; subst. *)
  (*   auto. *)
  (* Qed. *)

  Lemma external_call_mem_extends
    ef vargs1 vargs2 m1 m2 t vres1 vres2 m1' m2' :
    Val.lessdef_list vargs1 vargs2 ->
    Memory.Mem.extends m1 m2 ->
    @external_call Three VoteSemantics_Three ef (Genv.globalenv prog) vargs1 m1 t vres1 m1' ->
    @external_call Two VoteSemantics_Two ef (Genv.globalenv prog) vargs2 m2 t vres2 m2' ->
    Memory.Mem.extends m1' m2'.
  Proof.
    intros Hlessdef Hmem Hext1 Hext2.
    apply external_call_Three_Two in Hext1.
    destruct Hext1 as [v' Hext1].
    eapply external_call_mem_extends in Hext1; eauto.
    destruct Hext1 as (vres' & m2'' & Hext1 & Hld & Hmem' & Hmem'').
    eapply external_call_deterministic in Hext2; eauto.
    destruct Hext2; subst.
    auto.
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
      eexists; split.
      + eapply exec_Inop; eauto.
      + econstructor; eauto.
        inv WC_FUN.
        apply wc_fn_code in H; inv H.
        unfold match_rs in *.
        destruct b; simpl in *; auto.
        inv_rs; exists c; split; auto.

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
          eapply eval_operation_val_compat; eauto.
        * rewrite 2!Regmap.gso; auto.
      + unfold match_rs in *.
        destruct b; simpl in *.
        * inv_rs; exists c; split; auto.
          intros r Hr.
          inv_wc.
          { (* Safe op (replicated *)
            destruct (peq r res0); subst.
            - rewrite 2!Regmap.gss.
              eapply Op.eval_operation_lessdef with (vl2 := rs ## args0) in H10; eauto.
              2: { apply forall_lessdef_list.
                   apply Forall_forall.
                   intros r Hin.
                   apply RS; intro HC; apply Hr.                   
                   rewrite Forall_forall in H7.
                   apply H7 in Hin. rewrite <- Hin; auto. }
              destruct H10 as (v2 & Hop & Hv2).
              rewrite H0 in Hop; inv Hop; assumption.
            - rewrite 2!Regmap.gso; auto. }
          (* Unsafe op (voted) *)
          destruct (peq r res0); subst.
          { rewrite 2!Regmap.gss.
            eapply Op.eval_operation_lessdef with (vl2 := rs ## args0) in H10; eauto.
            2: { apply forall_lessdef_list.
                 apply Forall_forall.
                 intros r Hin.
                 apply RS; intro HC.
                 rewrite Forall_forall in H6; apply H6 in Hin.
                 rewrite Hin in HC; inv HC; inv Hc. }
            destruct H10 as (v2 & Hop & Hv2).
            rewrite H0 in Hop; inv Hop; assumption. }
          rewrite 2!Regmap.gso; auto; apply RS; intro HC.
          destruct (in_dec peq r args0).
          { rewrite Forall_forall in H6; apply H6 in i.
            rewrite i in HC; inv HC; inv Hc. }
          apply H8 in HC; auto.
        * intro r; destruct (peq r res0); subst.
          { rewrite 2!Regmap.gss.
            eapply Op.eval_operation_lessdef with (vl2 := rs ## args0) in H10; eauto.
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
        rewrite Forall_forall in H5; apply H5 in Hin.
        apply RS; intro HC; rewrite Hin in HC; inv HC; inv Hc. }
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
          { rewrite 2!Regmap.gss; auto. }
          rewrite 2!PMap.gso; auto.
          inv_wc.
          apply RS; intro HC.
          destruct (in_dec peq r args0).
          { rewrite Forall_forall in H5.
            apply H5 in i; rewrite i in HC; inv HC; inv Hc. }
          apply Hr, H9; auto.
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
        rewrite Forall_forall in H8; apply H8 in Hin.
        apply RS; intro HC; rewrite Hin in HC; inv HC; inv Hc. }
      assert (Ha: Val.lessdef a0 a).
      { eapply Op.eval_addressing_lessdef in H11; eauto.
        destruct H11 as (v2 & Heval & Hv2).
        rewrite H0 in Heval; inv Heval; assumption. }
      assert (Hsrc: Val.lessdef (rs1 # src0) (rs # src0)).
      { destruct b; auto; inv_rs; inv_wc.
        apply RS; intro HC; rewrite H5 in HC; inv HC; inv Hc. }
      assert (Memory.Mem.extends m'0 m').
      { eapply Memory.Mem.storev_extends in H12; eauto.
        destruct H12 as (m2' & Hstore & Hm2').
        rewrite H1 in Hstore; inv Hstore; auto. }
      econstructor; eauto.
      destruct b; auto.
      inv_rs; inv_wc; exists c; split; auto.
      intros r Hr.
      apply RS; intro HC.
      destruct (peq r src0); subst.
      { rewrite H6 in HC; inv HC; inv Hc. }
      destruct (in_dec peq r args0).
      { rewrite Forall_forall in H9; apply H9 in i.
        rewrite i in HC; inv HC; inv Hc. }
      apply Hr, H10; auto.

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
           apply RS; intro HC.
           rewrite (H6 _ (eq_refl _)) in HC; inv HC; inv Hc. }
      rewrite H0 in H10; inv H10.
      assert (Hlessdef: Forall2 Val.lessdef rs1 ## args0 rs ## args0).
      { apply forall2_lessdef.
        apply Forall_forall.
        intros r Hin.
        destruct b; auto.
        inv_rs; inv_wc.
        rewrite Forall_forall in H8; apply H8 in Hin.
        apply RS; intro HC; rewrite Hin in HC; inv HC; inv Hc. }
      econstructor; auto.
      constructor; auto.
      econstructor; eauto.
      destruct b.
      2: { apply match_rs_match_rs_upto; assumption. }
      inv_rs; inv_wc; exists c; split; auto.
      intros r Hneq Hr.
      destruct (peq r res0); subst; try congruence.
      destruct (in_dec peq r args0).
      { rewrite Forall_forall in H8; apply H8 in i.
        apply RS; intro HC; rewrite i in HC; inv HC; inv Hc. }
      destruct ros0.
      { destruct (peq r r0); subst.
        - apply RS; intro HC; rewrite H6 in HC; auto; inv HC; inv Hc.
        - apply RS; intro HC; apply Hr; apply H10; auto.
          intros x Hx; inv Hx; assumption. }
      apply RS; intro HC; apply Hr; apply H10; auto.
      intros x Hx; inv Hx; assumption.

    (* exec_Itailcall *)
    - admit.

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
        inv_wc.
        * (* white smove *)
          repeat match goal with
                 | [ H : eval_builtin_args _  _ _ _ _ _ |- _ ] => inv H
                 | [ H : list_forall2 _ _ _ |- _ ]  => inv H
                 | [ H : eval_builtin_arg _ _ _ _ (BA _) _ |- _ ] => inv H
                 end.
          replace t with E0 in *.
          2: { symmetry; eapply external_call_smove_E0; eauto. }
          replace t' with E0 in *.
          2: { symmetry; eapply external_call_smove_E0; eauto. }
          replace m' with m in *.
          2: { eapply external_call_smove_mem; eauto. }
          replace m'0 with m1 in *.
          2: { eapply external_call_smove_mem; eauto. }
          assert (Hlessdef: Val.lessdef vres0 vres).
          { pose proof H12 as Hext.
            apply external_call_Three_Two' in H12.
            destruct H12 as (v' & Hext' & Hv').
            eapply Events.external_call_mem_extends
              with (vargs' := [rs # arg]) in Hext'; eauto.
            2: { repeat constructor; apply RS.
                 intro HC; rewrite H7 in HC; inv HC; inv Hc. }
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
          intros r Hr.
          destruct (peq r res); subst.
          { rewrite 2!Regmap.gss; auto. }
          rewrite 2!Regmap.gso; auto.
          destruct (peq r arg); subst.
          { apply RS; intro HC.
            rewrite H7 in HC; inv HC; inv Hc. }
          apply RS; intro HC; apply Hr, H10; auto.

        * (* pink smove *)
          repeat match goal with
                 | [ H : eval_builtin_args _  _ _ _ _ _ |- _ ] => inv H
                 | [ H : list_forall2 _ _ _ |- _ ]  => inv H
                 | [ H : eval_builtin_arg _ _ _ _ (BA _) _ |- _ ] => inv H
                 end.
          replace t with E0 in *.
          2: { symmetry; eapply external_call_smove_E0; eauto. }
          replace t' with E0 in *.
          2: { symmetry; eapply external_call_smove_E0; eauto. }
          replace m' with m in *.
          2: { eapply external_call_smove_mem; eauto. }
          replace m'0 with m1 in *.
          2: { eapply external_call_smove_mem; eauto. }
          assert (Hlessdef: Val.lessdef vres0 vres).
          { pose proof H12 as Hext.
            apply external_call_Three_Two' in H12.
            destruct H12 as (v' & Hext' & Hv').
            eapply Events.external_call_mem_extends
              with (vargs' := [rs # arg]) in Hext'; eauto.
            2: { repeat constructor; apply RS.
                 intro HC; rewrite H7 in HC; inv HC; inv Hc. }
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
          intros r Hr.
          destruct (peq r res); subst.
          { rewrite 2!Regmap.gss; auto. }
          rewrite 2!Regmap.gso; auto.
          destruct (peq r arg); subst.
          { apply RS; intro HC.
            rewrite H7 in HC; inv HC; inv Hc. }
          apply RS; intro HC; apply Hr, H10; auto.

        * (* vote *)
          repeat match goal with
                 | [ H : eval_builtin_args _  _ _ _ _ _ |- _ ] => inv H
                 | [ H : list_forall2 _ _ _ |- _ ]  => inv H
                 | [ H : eval_builtin_arg _ _ _ _ (BA _) _ |- _ ] => inv H
                 end.
          replace t with E0 in *.
          2: { symmetry; eapply external_call_vote_E0; eauto. }
          replace t' with E0 in *.
          2: { symmetry; eapply external_call_vote_E0; eauto. }
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
                * apply RS; intro HC; rewrite H8 in HC; inv HC.
                * apply RS; intro HC; rewrite H9 in HC; inv HC.
              + apply list_lessdef_mod_1_cons_lessdef.
                * apply RS; intro HC; rewrite H7 in HC; inv HC.
                * apply list_lessdef_mod_1_cons.
                  {  repeat constructor.
                     apply RS; intro HC; rewrite H9 in HC; inv HC. }
              + apply list_lessdef_mod_1_cons_lessdef.
                * apply RS; intro HC; rewrite H7 in HC; inv HC.
                * apply list_lessdef_mod_1_cons_lessdef.
                  { apply RS; intro HC; rewrite H8 in HC; inv HC. }
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
          intros r Hr; simpl in *.
          destruct (peq r res); subst.
          { rewrite 2!Regmap.gss; auto. }
          rewrite 2!Regmap.gso; auto.
          apply RS; intro HC; apply Hr; apply H13; auto.

        * (* other builtin *)
          admit.

      + (* Fault has not occurred *)
        admit.

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
          intros r Hr.
          destruct (peq r res); subst.
          { rewrite 2!Regmap.gss; auto. }
          rewrite 2!Regmap.gso; auto.
        * intro r.
          destruct (peq r res); subst.
          { rewrite 2!Regmap.gss; auto. }
          rewrite 2!Regmap.gso; auto.
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
