Require Import
  AST
  Coqlib
  Errors
  Globalenvs
  Linking
  Replicate
  Smallstep
  Values
.
Require Import RTL.
Require Import Replicate.

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

  Lemma symbols_preserved:
    forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof (Genv.find_symbol_match TRANSF).

  Lemma senv_preserved:
    Senv.equiv ge tge.
  Proof (Genv.senv_match TRANSF).

  Lemma functions_translated:
    forall (v: val) (f: fundef),
      Genv.find_funct ge v = Some f ->
      exists cu tf,
        Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf /\ linkorder cu prog.
  Proof (Genv.find_funct_match TRANSF).

  Lemma function_ptr_translated:
    forall (b: block) (f: fundef),
      Genv.find_funct_ptr ge b = Some f ->
      exists cu tf,
        Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf /\ linkorder cu prog.
  Proof (Genv.find_funct_ptr_match TRANSF).

  Lemma sig_function_translated:
    forall f tf,
      transf_fundef f = OK tf ->
      funsig tf = funsig f.
  Proof.
    intros [f | f] tf Heq; monadInv Heq; auto.
    monadInv EQ.
    unfold transf_fun' in EQ1.
    destruct (transf_fun x0 f _); inv EQ1; auto.
  Qed.  

  Lemma stacksize_translated:
    forall f tf,
      transf_function f = OK tf -> tf.(fn_stacksize) = f.(fn_stacksize).
  Proof.
    unfold transf_function; intros.
    monadInv H.
    unfold transf_fun' in EQ0.
    destruct (transf_fun _ _ _); inv EQ0; reflexivity.
  Qed.

  Inductive match_stackframes: stackframe -> stackframe -> Prop :=
  .

  Inductive match_states: state -> state -> Prop :=
  .

  Theorem step_simulation:
    forall S1 t S2,
      step ge S1 t S2 ->
      forall S1',
        match_states S1 S1' ->
        (* sound_state prog S1 -> *)
        exists S2', step tge S1' t S2' /\ match_states S2 S2'.
  Proof.
  Admitted.

  Lemma transf_initial_states:
    forall st1, initial_state prog st1 ->
           exists st2, initial_state tprog st2 /\ match_states st1 st2.
  Proof.
    intros. inversion H.
    exploit function_ptr_translated; eauto. intros (cu & tf & A & B & C).
    exists (Callstate nil tf nil m0); split.
    econstructor; eauto.
    eapply (Genv.init_mem_match TRANSF); eauto.
    replace (prog_main tprog) with (prog_main prog).
    rewrite symbols_preserved. eauto.
    symmetry; eapply match_program_main; eauto.
    rewrite <- H3. eapply sig_function_translated; eauto.
  Admitted.

  Lemma transf_final_states:
    forall st1 st2 r,
      match_states st1 st2 -> final_state st1 r -> final_state st2 r.
  Proof.
    intros. inv H0. inv H.
  Qed.

  Theorem transf_program_correct:
    forward_simulation (semantics prog) (semantics tprog).
  Proof.
    intros.
    apply forward_simulation_step with
      (match_states := fun s1 s2 => match_states s1 s2).
    - apply senv_preserved.
    - simpl; intros. exploit transf_initial_states; eauto.
    (* intros [st2 [A B]]. *)
    (* exists st2; intuition. eapply sound_initial; eauto. *)
    - simpl; intros. destruct H.
    (* eapply transf_final_states; eauto. *)
    - simpl; intros. destruct H0.
  Qed.
  (*   assert (sound_state prog s1') by (eapply sound_step; eauto). *)
  (*   fold ge; fold tge. exploit step_simulation; eauto. intros [st2' [A B]]. *)
  (*   exists st2'; auto. *)
  (* Qed. *)

End PRESERVATION.
