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

Inductive match_votes_function : function -> function -> Prop :=
| match_votes_fun : forall sig params stacksize c c' entrypoint
    (CODE: match_votes_code c c'),
    match_votes_function {| fn_sig := sig
                          ; fn_params := params
                          ; fn_stacksize := stacksize
                          ; fn_code := c
                          ; fn_entrypoint := entrypoint |}
                         {| fn_sig := sig
                          ; fn_params := params
                          ; fn_stacksize := stacksize
                          ; fn_code := c'
                          ; fn_entrypoint := entrypoint |}.

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
  (* TODO:  need lessdef on memories. *)
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

End TOLERANCE.

(** TODO: top level theorem(s). Probably at least analogues of
    transf_c_program_preservation and transf_c_program_is_refinement
    from driver/Complements.v. Maybe also
    transf_c_program_preserves_spec and
    transf_c_program_preserves_initial_trace. *)

(** Do we need to state these in terms of the original c programs, or
    is it sufficient to prove them just at the target language between
    non-faulty and faulty executions? They should compose, but it's a
    question of whether we want to explicitly (formally) do that or
    not. *)

Lemma rtl_state_behaves_faulty_improves p1 p2 (s : RTL.state) (fs : fstate) beh1 beh2 :
  match_votes_program p1 p2 ->
  RTL.initial_state p1 s ->
  initial_state (faulty_semantics p2) fs ->
  state_behaves (RTL.semantics p1) s beh1 ->
  state_behaves (faulty_semantics p2) fs beh2 ->
  behavior_improves beh1 beh2.
Proof.
  intros Hmatchvotes Hinit1 Hinit2 Hbeh1 Hbeh2.
  inv Hbeh1.
  - left.
    inv Hbeh2.
    + admit.
    + admit. (* contra *)
    + admit. (* contra *)
    + admit. (* contra *)
  - left.
    admit.
  - left.
    admit.
  - right.
    exists t; split; auto.
    admit.
Admitted.

Lemma match_votes_program_initial_state p1 p2 s :
  match_votes_program p1 p2 ->
  RTL.initial_state p1 s <-> RTL.initial_state p2 s.
Admitted.

Theorem rtl_fault_tolerance p1 p2 beh1 beh2 :
  match_votes_program p1 p2 ->
  program_behaves (RTL.semantics p1) beh1 ->
  program_behaves (faulty_semantics p2) beh2 ->
  behavior_improves beh1 beh2.
Proof.
  intros Hmatchvotes Hbeh1 Hbeh2.
  inv Hbeh1.
  - inv Hbeh2.
    2: { exfalso; apply (H1 {| fs_state := s; fault := false |}).
         constructor.
         rewrite <- match_votes_program_initial_state; eauto.
         apply H. }
    eapply rtl_state_behaves_faulty_improves; eauto.
  - inv Hbeh2.
    { inv H0.
      exfalso; apply (H s0).
      eapply match_votes_program_initial_state; eauto. }
    constructor; reflexivity.
Qed.
