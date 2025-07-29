Require Import
  AST
  Builtins2
  Coqlib
  Events
  Globalenvs
  Linking
  Maps
  Registers
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
| match_votes_builtin : forall nm1 nm2 sig args res succ,
    (* (nm1 = "__builtin_vote_int3" <-> nm2 = "__builtin_vote_int") -> *)
    (* (nm1 = "__builtin_vote_long3" <-> nm2 = "__builtin_vote_long") -> *)
    (* (nm1 = "__builtin_vote_single3" <-> nm2 = "__builtin_vote_single") -> *)
    (* (nm1 = "__builtin_vote_float3" <-> nm2 = "__builtin_vote_float") -> *)
    match_builtins nm1 nm2 ->
    match_votes_instruction
      (Ibuiltin (EF_builtin nm1 sig) args res succ)
      (Ibuiltin (EF_builtin nm2 sig) args res succ)
| match_votes_other : forall i,
    not_builtin i ->
    match_votes_instruction i i.

Inductive liftOpt {A B : Type} (R : A -> B -> Prop) : option A -> option B -> Prop :=
| liftOpt_None :
  liftOpt R None None
| liftOpt_Some : forall x y,
    R x y ->
    liftOpt R (Some x) (Some y).

Definition match_votes_code (c c' : code) : Prop :=
  forall pc, liftOpt match_votes_instruction (c ! pc) (c' ! pc).

Inductive match_votes_function : function -> function -> Prop :=
| match_votes_fun : forall sig params stacksize c c' entrypoint,
    match_votes_code c c' ->
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
      match_function true re rm f tf1 ->
      match_function false re rm f tf2 ->
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
| match_votes_internal : forall f1 f2,
    match_votes_function f1 f2 ->
    match_votes_fundef (Internal f1) (Internal f2)
| match_votes_external : forall f,
    match_votes_fundef (External f) (External f).

Definition match_votes_program (prog3 prog2 : program) :=
  match_program (fun cu f1 f2 => match_votes_fundef f1 f2) eq prog3 prog2.

Lemma match_votes_wc (col : reg -> color) (p1 p2 : program) :
  match_votes_program p1 p2 ->
  wc_program col p1 ->
  wc_program col p2.
Admitted.

Section match_states.
  Variable col : reg -> color.

  (* TODO: need to know that the values of the faulted color registers
     are at still the same kind (either both undef, ints, floats,
     etc.). *)
  Definition match_rs (b : bool) (rs1 rs2 : regset) : Prop :=
    if b then
      exists c, basic_color c /\ forall r, col r <> c -> Val.lessdef (rs1 # r) (rs2 # r)
    else
      forall r, Val.lessdef (rs1 # r) (rs2 # r).

  Inductive match_stackframes : bool -> RTL.stackframe -> RTL.stackframe -> Prop :=
  | match_stackframes_Stackframe : forall (b : bool) res f1 f2 sp pc rs1 rs2,
      match_votes_function f1 f2 ->
      match_rs b rs1 rs2 ->
      match_stackframes b (Stackframe res f1 sp pc rs1) (Stackframe res f2 sp pc rs2).

  (** When a fault hasn't occurred, Val.lessdef should hold between
      all registers. When a fault has occurred, it should hold between
      all registers except those of the affected color. Should the
      fault state should track which color was faulted? *)
  Inductive match_states : RTL.state -> fstate -> Prop :=
  (* TODO:  need lessdef on memories. *)
  | match_states_State : forall stk1 stk2 f1 f2 sp pc rs1 rs2 m (b : bool),
      Forall2 (match_stackframes b) stk1 stk2 ->
      match_votes_function f1 f2 ->
      match_rs b rs1 rs2 ->
      match_states (State stk1 f1 sp pc rs1 m)
                   {| fs_state := State stk2 f2 sp pc rs2 m; fault := b |}
  | match_states_Callstate : forall stk1 stk2 fd1 fd2 args1 args2 m b,
      Forall2 (match_stackframes b) stk1 stk2 ->
      match_votes_fundef fd1 fd2 ->
      Forall2 Val.lessdef args1 args2 ->
      match_states (Callstate stk1 fd1 args1 m)
                   {| fs_state := Callstate stk2 fd2 args2 m; fault := b |}
  | match_state_Returnstate : forall stk1 stk2 v1 v2 m b,
      Forall2 (match_stackframes b) stk1 stk2 ->
      Val.lessdef v1 v2 ->
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
  Variable col : reg -> color.
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
    - inv Hmatch.
      inv H8.
      simpl in *.
      generalize (H0 pc); intro Hmatchvote.
      inv Hmatchvote; try congruence.
      inv H3; try congruence.
      inv Hfstep.
      + inv H10; simpl in *; try congruence.
        split; auto.
        rewrite H in H1.
        inv H1.
        rewrite <- H2 in H15.
        inv H15.
        repeat constructor; auto.
      + split; auto.
        inv H10.

        (* rewrite  *)
        (* rewrite H1 in H2. *)
        
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
