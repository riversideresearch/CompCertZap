
Require Import
  AST
  Behaviors
  Builtins2
  Coqlib
  LTL
  Maps
  (* Novotes *)
  Registers
  RTL
  Smallstep
  Values
.

Import ListNotations.

(* Section RTL_STRONG_AGREEMENT. *)
(*   Variable p : RTL.program. *)
(*   Context {VT: vote_type} {vsem: VoteSemantics VT}. *)
  
(*   Definition sem := RTL.semantics p. *)

(*   Inductive builtin_arg_eq (rs : regset) : builtin_arg reg -> builtin_arg reg -> Prop := *)
(*   | builtin_arg_eq_BA : forall r1 r2, *)
(*       eq (rs !! r1) (rs !! r2) -> *)
(*       builtin_arg_eq rs (BA r1) (BA r2) *)
(*   | builtin_arg_eq_BA_int : forall n, builtin_arg_eq rs (BA_int n) (BA_int n) *)
(*   | builtin_arg_eq_BA_long : forall n, builtin_arg_eq rs (BA_long n) (BA_long n) *)
(*   | builtin_arg_eq_BA_float : forall f, builtin_arg_eq rs (BA_float f) (BA_float f) *)
(*   | builtin_arg_eq_BA_single : forall f, builtin_arg_eq rs (BA_single f) (BA_single f) *)
(*   | builtin_arg_eq_BA_loadstack : forall chunk ofs, *)
(*       builtin_arg_eq rs (BA_loadstack chunk ofs) (BA_loadstack chunk ofs) *)
(*   | builtin_arg_eq_BA_addrstack : forall ofs, *)
(*       builtin_arg_eq rs (BA_addrstack ofs) (BA_addrstack ofs) *)
(*   | builtin_arg_eq_BA_loadglobal : forall chunk id ofs, *)
(*       builtin_arg_eq rs (BA_loadglobal chunk id ofs) (BA_loadglobal chunk id ofs) *)
(*   | builtin_arg_eq_BA_addrglobal : forall id ofs, *)
(*       builtin_arg_eq rs (BA_addrglobal id ofs) (BA_addrglobal id ofs) *)
(*   | builtin_arg_eq_BA_splitlong : forall hi hi' lo lo', *)
(*       builtin_arg_eq rs hi hi' -> *)
(*       builtin_arg_eq rs lo lo' -> *)
(*       builtin_arg_eq rs (BA_splitlong hi lo) (BA_splitlong hi' lo') *)
(*   | builtin_arg_eq_BA_addptr : forall a1 a1' a2 a2', *)
(*       builtin_arg_eq rs a1 a1' -> *)
(*       builtin_arg_eq rs a2 a2' -> *)
(*       builtin_arg_eq rs (BA_addptr a1 a2) (BA_addptr a1' a2'). *)

(*   Definition agreement_at_state (s : RTL.state) : Prop := *)
(*     match s with *)
(*     | State stk f sp pc rs m => *)
(*         forall ef args res pc', *)
(*           (fn_code f)!pc = Some (Ibuiltin ef args res pc') -> *)
(*           is_vote_builtin ef -> *)
(*           match args with *)
(*           | arg1 :: arg2 :: arg3 :: nil => *)
(*               builtin_arg_eq rs arg1 arg2 /\ builtin_arg_eq rs arg1 arg3 *)
(*           | _ => False *)
(*           end *)
(*     | _ => True *)
(*     end. *)

(*   Definition strong_agreement : Prop := *)
(*     forall s, *)
(*       RTL.initial_state p s -> *)
(*       forall t s', *)
(*         Star sem s t s' -> *)
(*         agreement_at_state s'. *)

(* End RTL_STRONG_AGREEMENT. *)

Section RTL_WEAK_AGREEMENT.
  Variable p : RTL.program.

  Definition rtl_sem2 := @RTL.semantics Two (VoteSemantics_Two) p.
  Definition rtl_sem3 := @RTL.semantics Three (VoteSemantics_Three) p.

  Definition rtl_weak_agreement :=
    forall beh,
      program_behaves rtl_sem2 beh ->
      program_behaves rtl_sem3 beh.

  (* Definition rtl_weak_agreement' := backward_simulation rtl_sem2 rtl_sem3. *)

  Definition rtl_weak_agreement' :=
    forall beh3, program_behaves rtl_sem3 beh3 ->
            exists beh2, program_behaves rtl_sem2 beh2 /\ behavior_improves beh2 beh3.

  (* Definition weak_agreement' := *)
  (*   forall beh, *)
  (*     program_behaves sem2 beh -> *)
  (*     exists beh', program_behaves sem3 beh' /\ behavior_improves beh beh'. *)

End RTL_WEAK_AGREEMENT.

(* Lemma agree_forever_silent {V: vote_type} {vsem: VoteSemantics V} *)
(*   (p : RTL.program) s : *)
(*   (forall t s', Step (RTL.semantics p) s t s' -> agreement_at_state s') -> *)
(*   Forever_silent (sem2 p) s -> *)
(*   Forever_silent (sem3 p) s. *)
(* Proof. *)

(* (* This should be true but not necessary for us to prove. *) *)
(* Lemma strong_agreement_implies_weak_agreement *)
(*   {VT: vote_type} {vsem: VoteSemantics VT} *)
(*   (p : RTL.program) : *)
(*   strong_agreement p -> *)
(*   weak_agreement p. *)
(* Proof. *)
(*   unfold strong_agreement. *)
(*   unfold weak_agreement. *)
(*   intros HSA beh Hbeh. *)
(*   inv Hbeh. *)
(*   - apply program_runs with s. *)
(*     { ... } *)
(*     inv H0. *)
(*     + apply state_terminates with s'. *)
(*       * ... *)
(*       * ... *)
(*     + apply state_diverges with s'. *)
(*       * ... *)
(*       * apply agree_forever_silent; auto. *)
(*         intros t' s'' Hstep'. *)
(*         eapply HSA with (t := t ++ t'); eauto. *)
(*         ... *)
(*     + apply state_reacts. *)
(*       ... *)
(*     + apply state_goes_wrong with s'. *)
(*       * ... *)
(*       * ... *)
(*       * ... *)
(*   - apply program_goes_initially_wrong. *)
(*     intros s Hinit. *)
(*     apply H with s. *)
(*     ... *)

(* Design note: An alternative approach would be to remove no_votes at the C level
and add an RTL pass that checks there are no votes before the replication pass.
This would give weak_agreement at the RTL level right before replication
(because no_votes implies weak_agreement trivially), then also after
replication via preservation by forward simulation, and so forth down
to asm. Benefits: 1) no_votes would not appear as an explicit hypothesis
in the top-level theorems, 2) weak_agreement would not need to be defined
for anything above RTL, and 3) weak agreement would not need to be
established via strong agreement at the replication pass. *)

(* Addendum: maybe we don't even need no_votes. The proof below
   doesn't seem to need it.. (it will be generalized so that the
   source language is C and the target is asm, for which we can obtain
   a big forward simulation just like in driver/Compiler.v.

   I guess the assumption of safety of the source program
   wrt. 3-voting semantics implies that if votes exist have equal
   arguments or their return values aren't used in a meaningful way by
   the program.

   EDIT: maybe we can only get the big forward simulation from
   Cstrategy to asm, so we actually want no_votes at some point before
   the replication pass to establish agreement and then use the
   forward simulations from that point to push it to asm.
*)

(* Section AGREEMENT_PRESERVATION. *)
(*   Variable p : RTL.program. *)
(*   Variable tp : RTL.program. *)

(*   Lemma initial_state_sem3_sem2 s : *)
(*     initial_state (sem3 tp) s -> *)
(*     initial_state (sem2 tp) s. *)
(*   Proof. intro Hinit; inv Hinit; econstructor; eauto. Qed. *)

(*   Theorem forward_simulation_preserves_weak_agreement : *)
(*     (forall beh, program_behaves (sem2 p) beh -> not_wrong beh) -> *)
(*     forward_simulation (sem2 p) (sem2 tp) -> *)
(*     forward_simulation (sem3 p) (sem3 tp) -> *)
(*     weak_agreement p -> *)
(*     weak_agreement tp. *)
(*   Proof. *)
(*     unfold weak_agreement. *)
(*     intros Hsafe Hforward2 Hforward3 Hagree beh Hbeh. *)

(*     assert (Hbackward: backward_simulation (sem3 p) (sem3 tp)). *)
(*     { apply forward_to_backward_simulation; auto. *)
(*       - apply semantics_receptive. *)
(*       - ... } *)

(*     assert (Hbackward2: backward_simulation (sem2 p) (sem2 tp)). *)
(*     { apply forward_to_backward_simulation; auto. *)
(*       - apply semantics_receptive. *)
(*       - ... } *)

(*     pose proof Hbeh as Hbeh'. *)
(*     inv Hbeh'. *)
(*     2: { constructor. *)
(*          intros s Hs. *)
(*          eapply H with s. *)
(*          eapply initial_state_sem3_sem2; auto. } *)

(*     eapply backward_simulation_same_safe_behavior in Hbeh. *)
(*     2: { eauto. } *)
(*     - eapply forward_simulation_same_safe_behavior; eauto. *)
(*     - intros beh' Hbeh'; eauto. *)
  
(* End AGREEMENT_PRESERVATION. *)
