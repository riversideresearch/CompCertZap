
Require Import
  AST
  Behaviors
  Builtins2
  Coqlib
  LTL
  Maps
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
