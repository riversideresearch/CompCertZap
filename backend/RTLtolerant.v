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
  Replicate
  Replicatespec
  RTL
  RTLcolor
  RTLfault
  Smallstep
  Values
.

Import ListNotations.
Local Open Scope string_scope.

Definition not_builtin (i : instruction) : Prop :=
  match i with
  | Ibuiltin _ _ _ _ => False
  | _ => True
  end.

Inductive match_builtins : string -> string -> Prop :=
| match_builtins_int :
  match_builtins "__builtin_vote_int3" "__builtin_vote_int"
| match_builtins_long :
  match_builtins "__builtin_vote_long3" "__builtin_vote_long"
| match_builtins_single :
  match_builtins "__builtin_vote_single3" "__builtin_vote_single"
| match_builtins_float :
  match_builtins "__builtin_vote_float3" "__builtin_vote_float"
| match_builtins_other : forall nm,
    ~ In nm ["__builtin_vote_int3"; "__builtin_vote_int";
             "__builtin_vote_long3"; "__builtin_vote_long";
             "__builtin_vote_single3"; "__builtin_vote_single";
             "__builtin_vote_float3"; "__builtin_vote_float"] ->
    match_builtins nm nm.

Inductive match_votes_instruction : instruction -> instruction -> Prop :=
| match_votes_builtin : forall nm1 nm2 sig args res succ
    (BUILTIN: match_builtins nm1 nm2),
    match_votes_instruction
      (Ibuiltin (EF_builtin nm1 sig) args res succ)
      (Ibuiltin (EF_builtin nm2 sig) args res succ)
| match_votes_other : forall i,
    not_builtin i ->
    match_votes_instruction i i.

Inductive liftOpt {A B : Type} (R : A -> B -> Prop) : option A -> option B -> Prop :=
| liftOpt_None :
  liftOpt R None None
| liftOpt_Some : forall x y
    (HR: R x y),
    liftOpt R (Some x) (Some y).

Definition match_votes_code (c c' : code) : Prop :=
  forall pc, liftOpt match_votes_instruction (c ! pc) (c' ! pc).

(* Inductive match_votes_function : function -> function -> Prop := *)
(* | match_votes_fun : forall sig params stacksize c c' entrypoint *)
(*     (CODE: match_votes_code c c'), *)
(*     match_votes_function {| fn_sig := sig *)
(*                           ; fn_params := params *)
(*                           ; fn_stacksize := stacksize *)
(*                           ; fn_code := c *)
(*                           ; fn_entrypoint := entrypoint |} *)
(*                          {| fn_sig := sig *)
(*                           ; fn_params := params *)
(*                           ; fn_stacksize := stacksize *)
(*                           ; fn_code := c' *)
(*                           ; fn_entrypoint := entrypoint |}. *)

Inductive match_votes_function : function -> function -> Prop :=
| match_votes_fun :
  forall f1 f2
    (CODE: match_votes_code f1.(fn_code) f2.(fn_code)),
    match_votes_function f1 f2.

Lemma match_function_match_votes_function re rm f tf1 tf2 :
      match_function Three re rm f tf1 ->
      match_function Two re rm f tf2 ->
      match_votes_function tf1 tf2.
Proof.
  intros H0 H1.
  inv H0; inv H1.
  simpl.
  (* Might need to either record something more concrete about how
     live_regs is computed in match_function, or just state this lemma
     wrt. transf_function (which probably wouldn't be a big deal).  *)
Admitted.

Inductive match_votes_fundef : fundef -> fundef -> Prop :=
| match_votes_internal : forall f1 f2
    (FUN: match_votes_function f1 f2),
    match_votes_fundef (Internal f1) (Internal f2)
| match_votes_external : forall f,
    match_votes_fundef (External f) (External f).

Definition match_votes_program (prog3 prog2 : program) :=
  match_program (fun cu f1 f2 => match_votes_fundef f1 f2) eq prog3 prog2.

Lemma match_votes_wc (col : node -> reg -> color) (p1 p2 : program) :
  match_votes_program p1 p2 ->
  wc_program col p1 ->
  wc_program col p2.
Admitted.

Definition match_rs (col : reg -> color) (faulted : bool) (rs1 rs2 : regset) : Prop :=
  if faulted then
    exists c, basic_color c /\
           forall r, (col r <> c -> Val.lessdef (rs1 # r) (rs2 # r)) /\
                  (col r = c -> val_compat (rs1 # r) (rs2 # r))
  else
    forall r, Val.lessdef (rs1 # r) (rs2 # r).

Section match_states.
  Variable col : node -> reg -> color.

  (** When a fault has occurred elsewhere and regsets [rs1] and [rs2]
      are unchanged, they still match. *)
  Lemma match_rs_fault (pc : node) (rs1 rs2 : regset) :
    match_rs (col pc) false rs1 rs2 ->
    match_rs (col pc) true rs1 rs2.
  Proof.
    intro H; exists Red; split; constructor; auto.
    intro Hcol; apply val_lessdef_compat; auto.
  Qed.

  Inductive match_stackframes (faulted : bool)
    : RTL.stackframe -> RTL.stackframe -> Prop :=
  | match_stackframes_Stackframe : forall res f1 f2 sp pc rs1 rs2,
      match_votes_function f1 f2 ->
      match_rs (col pc) faulted rs1 rs2 ->
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
    constructor; auto.
    apply match_rs_fault; auto.
  Qed.

  (** When a fault hasn't occurred, Val.lessdef should hold between
      all registers. When a fault has occurred, it should hold between
      all registers except those of the affected color. *)
  Inductive match_states : RTL.state -> fstate -> Prop :=
  (* TODO: need lessdef on memories. *)
  | match_states_State :
    forall stk1 stk2 f1 f2 sp pc rs1 rs2 m (b : bool)
      (STK: Forall2 (match_stackframes b) stk1 stk2)
      (VOTE: match_votes_function f1 f2)
      (RS: match_rs (col pc) b rs1 rs2),
      match_states (State stk1 f1 sp pc rs1 m)
                   {| fs_state := State stk2 f2 sp pc rs2 m; fault := b |}
  | match_states_Callstate :
    forall stk1 stk2 fd1 fd2 args1 args2 m b
      (STK: Forall2 (match_stackframes b) stk1 stk2)
      (VOTE: match_votes_fundef fd1 fd2)
      (LESSDEF: Forall2 Val.lessdef args1 args2),
      match_states (Callstate stk1 fd1 args1 m)
                   {| fs_state := Callstate stk2 fd2 args2 m; fault := b |}
  | match_state_Returnstate :
    forall stk1 stk2 v1 v2 m b
      (STK: Forall2 (match_stackframes b) stk1 stk2)
      (LESSDEF: Val.lessdef v1 v2),
      match_states (Returnstate stk1 v1 m)
                   {| fs_state := Returnstate stk2 v2 m; fault := b |}.

End match_states.

Section TOLERANCE.
  Variable prog1 : program.
  Variable prog2 : program.
  Hypothesis PROG : match_votes_program prog1 prog2.
  Let ge1 := Genv.globalenv prog1.
  Let ge2 := Genv.globalenv prog2.

  (* Assume prog1 is well-colored (which should also imply through
     match_votes_prog that prog2 is well-colored). Maybe the same for
     well-typedness, but that shouldn't be necessary... *)
  Variable col : node -> reg -> color.
  Hypothesis WC : wc_program col prog1.

  (* Corollary wc_prog2 : wc_program col prog2. *)
  (* Proof. eapply match_votes_wc; eauto. Qed. *)

  Lemma match_votes_function_not_builtin f1 f2 pc i :
    not_builtin i ->
    (fn_code f1) ! pc = Some i ->
    match_votes_function f1 f2 ->
    (fn_code f2) ! pc = Some i.
  Proof.
    intros Hi Hpc Hmatch.
    inv Hmatch.
    specialize (CODE pc).
    inv CODE; try congruence.
    inv HR; try congruence.
    rewrite <- H0 in Hpc; inv Hpc.
    inv Hi.
  Qed.

  Theorem faulty_step_exists s1 t1 s1' s2 :
    match_states col s1 s2 ->
    RTL.step ge1 s1 t1 s1' ->
    exists t2 s2', fstep ge2 s2 t2 s2'.
  Proof.
    intros Hmatch Hstep.
    inv Hstep.
    - destruct s2.
      inv Hmatch.
      eexists; eexists.
      econstructor.
      + apply exec_Inop.
        eapply match_votes_function_not_builtin; eauto; constructor.
      + constructor.
    - destruct s2.
      inv Hmatch.
      eexists; eexists.
      econstructor.
      + eapply exec_Iop.
        eapply match_votes_function_not_builtin; eauto; constructor.
        (* By RS, in rs2 all the args are at least as defined as (and
           compatible with) their values in rs.  *)
        admit.
      + constructor.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  Theorem faulty_step_simulation s1 t1 s1' s2 t2 s2' :
    match_states col s1 s2 ->
    RTL.step ge1 s1 t1 s1' ->
    fstep ge2 s2 t2 s2' ->
    t1 = t2 /\ match_states col s1' s2'.
  Proof.
    intros Hmatch Hstep Hfstep.
    inv Hstep.

    (* exec_Inop *)
    - inv Hmatch.
      inv VOTE.
      simpl in *.
      generalize (CODE pc); intro Hmatchvote.
      inv Hmatchvote; try congruence.
      inv HR; try congruence.
      inv Hfstep.
      inv ZAP.
      + inv STEP; simpl in *; try congruence.
        split; auto.
        rewrite H in H1; inv H1.
        rewrite <- H2 in H11; inv H11.
        repeat constructor; auto.
        admit.
      + inv STEP; simpl in *; try congruence.
        split; auto.
        rewrite H in H1; inv H1.
        rewrite <- H2 in H11; inv H11.
        repeat constructor; auto.
        { eapply Forall2_impl.
          2: { eauto. }
          intros; apply match_stackframes_fault; auto. }
        unfold match_rs.
        exists (col pc0 r); split.
        * admit.
        * admit.

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

  Lemma initial_states_match s fs :
    initial_state (RTL.semantics prog1) s ->
    initial_state (faulty_semantics prog2) fs ->
    match_states col s fs.
  Proof.
    simpl; intros Hs Hfs.
    inv Hs; inv Hfs; inv H3.
    replace (prog_main prog1) with (prog_main prog2) in * by
        (eapply match_program_main in PROG; auto).
    replace b0 with b in *.
    2: { eapply Genv.find_symbol_match in PROG.
         unfold ge, ge0 in *.
         rewrite H0, H5 in PROG; inv PROG; reflexivity. }
    pose proof PROG as Hmatchvote.
    eapply Genv.init_mem_match in PROG; eauto.
    rewrite PROG in H4; inv H4.
    constructor; auto.
    unfold match_votes_program in Hmatchvote.
    eapply Genv.find_funct_ptr_match in Hmatchvote.
    - destruct Hmatchvote as (cunit & tf & Htf & Hmatch & Hlink).
      unfold ge0 in *.
      rewrite H6 in Htf.
      inv Htf; eauto.
    - auto.
  Qed.

  Lemma final_state_no_faulty_step s fs r :
    match_states col s fs ->
    final_state (RTL.semantics prog1) s r ->
    Nostep (faulty_semantics prog2) fs.
  Proof.
    intros Hmatch Hfin.
    inv Hfin; inv Hmatch.
    intros t fs' Hfstep.
    inv Hfstep; inv STK; inv STEP.
  Qed.

  Lemma final_state_no_step s fs r :
    match_states col s fs ->
    final_state (faulty_semantics prog2) fs r ->
    Nostep (RTL.semantics prog1) s.
  Proof.
    intros Hmatch Hfin t s' Hstep.
    inv Hfin; inv Hmatch; simpl in *; try congruence.
    inv H0; inv STK; inv LESSDEF; inv Hstep.
  Qed.

  (* Lemma asdf t s s' fs  r : *)
  (*   match_states col s fs -> *)
  (*   Star (RTL.semantics prog1) s t s' -> *)
  (*   final_state (RTL.semantics prog1) s' r -> *)
  (*   exists fs', Star (faulty_semantics prog2) fs t fs' /\ *)
  (*            Nostep (faulty_semantics prog2) fs' /\ *)
  (*            match_states col s' fs'. *)
  (* Proof. *)
  (* Admitted. *)

  (* TODO: should be able to prove
     [match s fs => (star s t s' /\ fstar fs t' fs') => t <= t' \/ t' <= t]. *)

  Lemma star_final_prog1_not_forever_silent t s s' fs r :
    match_states col s fs ->
    Star (RTL.semantics prog1) s t s' ->
    final_state (RTL.semantics prog1) s' r ->
    Forever_silent (faulty_semantics prog2) fs ->
    False.
  Proof.
    intros H Hstar.
    revert H.
    revert fs r.
    induction Hstar; intros fs r Hmatch Hfin Hsil; inv Hsil.
    - eapply final_state_no_faulty_step in Hfin; eauto.
      eapply Hfin; eauto.
    - eapply faulty_step_simulation in H; eauto.
      destruct H as [? Hmatch']; subst.
      eapply IHHstar; eauto.
  Qed.

  Lemma terminates_diverges_False t t' s s' fs fs' r :
    match_states col s fs ->
    Star (RTL.semantics prog1) s t s' ->
    final_state (RTL.semantics prog1) s' r ->
    Star (faulty_semantics prog2) fs t' fs' ->
    Forever_silent (faulty_semantics prog2) fs' ->
    False.
  Proof.
    intros Hmatch Hstar Hfin Hstar' Hsil.
    revert Hmatch Hstar Hfin Hsil.
    revert s t s' r.
    induction Hstar'; intros s0 t' s' r Hmatch Hstar Hfin Hsil.
    - eapply star_final_prog1_not_forever_silent; eauto.
    - inv Hstar.
      + eapply final_state_no_faulty_step in Hfin; eauto.
        eapply Hfin; eauto.
      + eapply faulty_step_simulation in H; eauto.
        destruct H as [? Hmatch']; subst.
        eapply IHHstar'; eauto.
  Qed.

  (* This isn't true because RTL.final_state requires that the result
     value be a Vint, but here it could be Vundef. *)
  (* Lemma faulty_final_state_final s fs r : *)
  (*   match_states col s fs -> *)
  (*   final_state (faulty_semantics prog2) fs r -> *)
  (*   final_state (RTL.semantics prog1) s r. *)
  (* Proof. *)
  (*   intros Hmatch Hfin. *)
  (*   inv Hfin; inv Hmatch; simpl in *; try congruence. *)
  (*   inv H0; inv STK. *)    

  Lemma star_final_prog2_not_silent t s fs fs' r :
    match_states col s fs ->
    Forever_silent (RTL.semantics prog1) s ->
    Star (faulty_semantics prog2) fs t fs' ->
    final_state (faulty_semantics prog2) fs' r ->
    False.
  Proof.
    intros Hmatch Hsil Hstar.
    revert Hmatch Hsil.
    revert s r.
    induction Hstar; intros s0 r Hmatch Hsil Hfin; inv Hsil.
    - eapply final_state_no_step in Hfin; eauto.
      eapply Hfin; eauto.
    - eapply faulty_step_simulation in H1; eauto.
      destruct H1 as [? Hmatch']; subst.
      eapply IHHstar; eauto.
  Qed.

  Lemma diverges_terminates_False t t' s s' fs fs' r :
    match_states col s fs ->
    Star (RTL.semantics prog1) s t s' ->
    Forever_silent (RTL.semantics prog1) s' ->
    Star (faulty_semantics prog2) fs t' fs' ->
    final_state (faulty_semantics prog2) fs' r ->
    False.
  Proof.
    intros Hmatch Hstar.
    revert Hmatch.
    revert fs t' fs' r.
    induction Hstar; intros fs t' fs' r Hmatch Hsil Hstar' Hfin.
    - eapply star_final_prog2_not_silent; eauto.
    - inv Hstar'.
      + eapply final_state_no_step in Hfin; eauto.
        eapply Hfin; eauto.
      + eapply faulty_step_simulation in H1; eauto.
        destruct H1 as [? Hmatch']; subst.
        eapply IHHstar; eauto.
    Qed.

  Lemma star_silent_not_reactive t s s' fs T :
    match_states col s fs ->
    Star (RTL.semantics prog1) s t s' ->
    Forever_silent (RTL.semantics prog1) s' ->
    Forever_reactive (faulty_semantics prog2) fs T ->
    False.
  Proof.
    intros Hmatch Hstar.
    revert Hmatch.
    revert fs T.
    induction Hstar; intros fs T Hmatch Hsil Hreact.
    - admit.
    - subst.
      inv Hsil.
      eapply IHHstar.
    (*   + eapply final_state_no_step in Hfin; eauto. *)
    (*     eapply Hfin; eauto. *)
    (*   + eapply faulty_step_simulation in H1; eauto. *)
    (*     destruct H1 as [? Hmatch']; subst. *)
    (*     eapply IHHstar; eauto. *)
    (* Qed. *)
  Admitted.

  Lemma star_final_not_reactive t s s' fs r T :
    match_states col s fs ->
    Star (RTL.semantics prog1) s t s' ->
    final_state (RTL.semantics prog1) s' r ->
    Forever_reactive (faulty_semantics prog2) fs T ->
    False.
  Proof.
    intros H Hstar.
    revert H.
    revert fs r T.
    induction Hstar; intros fs r T Hmatch Hfin Hreact; inv Hreact.
    - inv H; try congruence.
      eapply final_state_no_faulty_step in Hfin; eauto.
      eapply Hfin; eauto.
    - inv H1; try congruence.
      eapply faulty_step_simulation in H; eauto.
      destruct H as [? Hmatch']; subst.
      eapply IHHstar; eauto.
      eapply star_forever_reactive; eauto.
  Qed.

  Lemma match_states_final s fs r :
    match_states col s fs ->
    final_state (RTL.semantics prog1) s r ->
    final_state (faulty_semantics prog2) fs r.
  Proof.
    intros Hmatch Hfin; inv Hfin.
    inv Hmatch; inv STK; inv LESSDEF.
    constructor.
  Qed.

  Lemma faulty_final_state_nostep fs r :
    final_state (faulty_semantics prog2) fs r ->
    Nostep (faulty_semantics prog2) fs.
  Proof.
    intro Hfin; inv Hfin.
    destruct fs; simpl in *; rewrite <- H0.
    intros t fs' Hstep; inv Hstep; inv STEP.
  Qed.

  Lemma star_final_nostep_final s t s' r fs :
    match_states col s fs ->
    Star (RTL.semantics prog1) s t s' ->
    final_state (RTL.semantics prog1) s' r ->
    Nostep (faulty_semantics prog2) fs ->
    final_state (faulty_semantics prog2) fs r.
  Proof.
    intros Hmatch Hstar Hfin Hnostep.
    inv Hstar.
    { eapply match_states_final; eauto. }
    eapply faulty_step_exists in H; eauto.
    destruct H as (t' & fs' & Hfstep).
    exfalso; eapply Hnostep; eauto.
  Qed.

  Lemma star_final_star_nostep_final s t s' r fs t' fs' :
    match_states col s fs ->
    Star (RTL.semantics prog1) s t s' ->
    final_state (RTL.semantics prog1) s' r ->
    Star (faulty_semantics prog2) fs t' fs' ->
    Nostep (faulty_semantics prog2) fs' ->
    final_state (faulty_semantics prog2) fs' r.
  Proof.
    intros Hmatch Hstar Hfin Hstar'.
    revert Hmatch Hstar Hfin.
    revert s t s' r.
    induction Hstar'; intros s0 t0 s' r Hmatch Hstar Hfin Hnostep.
    { eapply star_final_nostep_final; eauto. }
    inv Hstar.
    - clear IHHstar'.
      exfalso.
      eapply match_states_final in Hfin; eauto.
      eapply faulty_final_state_nostep; eauto.
    - eapply IHHstar'; auto.
      3: { eauto. }
      2: { eauto. }
      eapply faulty_step_simulation; eauto.
  Qed.

  Lemma star_final_final s t s' r fs r' :
    match_states col s fs ->
    Star (RTL.semantics prog1) s t s' ->
    final_state (RTL.semantics prog1) s' r ->
    final_state (faulty_semantics prog2) fs r' ->
    t = E0 /\ r = r'.
  Proof.
    intros Hmatch Hstar Hfin Hfin'.
    inv Hstar.
    - split; auto.
      inv Hfin; inv Hfin'; inv Hmatch.
      inv H0; inv LESSDEF; reflexivity.
    - exfalso; eapply final_state_no_step; eauto.
  Qed.

  Lemma star_final_star_final s t s' r fs t' fs' r' :
    match_states col s fs ->
    Star (RTL.semantics prog1) s t s' ->
    final_state (RTL.semantics prog1) s' r ->
    Star (faulty_semantics prog2) fs t' fs' ->
    final_state (faulty_semantics prog2) fs' r' ->
    t = t' /\ r = r'.
  Proof.
    intros Hmatch Hstar Hfin Hstar'.
    revert Hmatch Hstar Hfin.
    revert s t s' r r'.
    induction Hstar'; intros s0 t' s' r r' Hmatch Hstar Hfin Hfin'.
    { eapply star_final_final; eauto. }
    inv Hstar.
    - exfalso; eapply final_state_no_faulty_step; eauto.
    - cut (t3 = t2 /\ r = r').
      { intros [? ?]; subst; split; auto; f_equal.
        eapply faulty_step_simulation; eauto. }
      eapply IHHstar'; eauto.
      eapply faulty_step_simulation; eauto.
  Qed.

  Lemma star_silent_silent s t s' fs :
    match_states col s fs ->
    Star (RTL.semantics prog1) s t s' ->
    Forever_silent (faulty_semantics prog2) fs ->
    t = E0.
  Proof.
    intros Hmatch Hstar.
    revert Hmatch.
    revert fs.
    induction Hstar; intros fs Hmatch Hsil.
    - split; auto.
    - inv Hsil.
      eapply faulty_step_simulation in H; eauto.
      destruct H as [? Hmatch']; subst; simpl.
      eapply IHHstar; eauto.
  Qed.

  Lemma star_silent_star_silent s t s' fs t' fs' :
    match_states col s fs ->
    Star (RTL.semantics prog1) s t s' ->
    Forever_silent (RTL.semantics prog1) s' ->
    Star (faulty_semantics prog2) fs t' fs' ->
    Forever_silent (faulty_semantics prog2) fs' ->
    t = t'.
  Proof.
    intros Hmatch Hstar Hsil Hstar'.
    revert Hmatch Hstar Hsil.
    revert s t s'.
    induction Hstar'; intros s0 t' s' Hmatch Hstar Hsil Hsil'.
    { eapply star_silent_silent; eauto. }
    subst.
    inv Hstar.
    - inv Hsil.
      eapply faulty_step_simulation in H0; eauto.
      destruct H0 as [? Hmatch']; subst; simpl.
      eapply IHHstar'; eauto.
      apply star_refl.
    - eapply faulty_step_simulation in H0; eauto.
      destruct H0 as [? Hmatch']; subst; f_equal.
      eapply IHHstar'; eauto.
  Qed.

  Lemma rtl_state_behaves_faulty_improves (s : RTL.state) (fs : fstate) beh1 beh2 :
    RTL.initial_state prog1 s ->
    initial_state (faulty_semantics prog2) fs ->
    state_behaves (RTL.semantics prog1) s beh1 ->
    state_behaves (faulty_semantics prog2) fs beh2 ->
    behavior_improves beh1 beh2.
  Proof.
    intros Hinit1 Hinit2 Hbeh1 Hbeh2.
    generalize (initial_states_match _ _ Hinit1 Hinit2); intro Hmatch.
    inv Hbeh1.
    - left; inv Hbeh2.
      + f_equal; eapply star_final_star_final; eauto.
      + exfalso; eapply terminates_diverges_False; eauto.
      + exfalso; eapply star_final_not_reactive; eauto.
      + exfalso; eapply H3, star_final_star_nostep_final; eauto.
    - left; inv Hbeh2.
      + exfalso; eapply diverges_terminates_False; eauto.
      + f_equal; eapply star_silent_star_silent; eauto.
      + exfalso; eapply star_silent_not_reactive; eauto.
      + exfalso.
        admit.
    - left; inv Hbeh2.
      + exfalso.
        admit.
      + exfalso.
        admit.
      + f_equal.
        admit. (* might be weird... extensionality axiom for traceinf_sim? *)
      + exfalso.
        admit.
    - right.
      exists t; split; auto.
      admit.
  Admitted.

  (* TODO: conversion between 2-vote and 3-vote versions of functions. *)

  Theorem faulty_behavior_improves beh1 beh2 :
    program_behaves (RTL.semantics prog1) beh1 ->
    program_behaves (faulty_semantics prog2) beh2 ->
    behavior_improves beh1 beh2.
  Proof.
    intros Hbeh1 Hbeh2.
    inv Hbeh1.
    - inv Hbeh2.
      2: { (* exfalso; apply (H1 {| fs_state := s; fault := false |}). *)
        (* constructor. *)
        (* rewrite <- match_votes_program_initial_state; eauto. *)
        (* apply H. } *)
        admit. }
      eapply rtl_state_behaves_faulty_improves; eauto.
    - inv Hbeh2.
      { (* inv H0. *)
        (* exfalso; apply (H s0). *)
        (* eapply match_votes_program_initial_state; eauto. *)
        admit. }
      constructor; reflexivity.
  Admitted.

End TOLERANCE.

(* Lemma match_votes_program_initial_state p1 p2 s : *)
(*   match_votes_program p1 p2 -> *)
(*   RTL.initial_state p1 s <-> RTL.initial_state p2 s. *)
(* Proof. *)
(*   intro Hmatchvotes. *)

(*   (* destruct Hmatchvotes as (Hdefs & Hmain & Hpub). *) *)
(*   split; intro Hinit. *)
(*   - inv Hinit; simpl. *)
(*     econstructor; auto. *)
(*     + eapply Genv.init_mem_match in Hmatchvotes; eauto. *)
(*     + rewrite <- H0. *)
(*       pose proof Hmatchvotes as H'. *)
(*       eapply match_program_main in H'. *)
(*       rewrite H'. *)
(*       eapply Genv.find_symbol_match in Hmatchvotes; eauto. *)
(*     + eapply Genv.find_funct_ptr_match in Hmatchvotes. *)
(*       2: { eauto. } *)
(*       destruct Hmatchvotes as (cunit & tf & Hptr & Hmatch & Hlink). *)
      
(*       rewrite Hmatchvotes. *)
(*       unfold match_votes_program in Hmatchvotes. *)
(*       unfold match_program in Hmatchvotes. *)
(*       apply Hmatchvotes. *)
(*     unfold Genv.init_mem. *)
    
(*     unfold Genv.alloc_globals. *)
(* Admitted. *)

(* IDEA: implement a single version of the compiler that first
   generates 3-vote code and then in a second pass replaces them with
   2-votes. Maybe that wont' work because we will want to have asm
   programs with 3-votes to do the proof at asm. *)
