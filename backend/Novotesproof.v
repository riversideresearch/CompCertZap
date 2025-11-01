Require Import
  AST
  Builtins2
  Coqlib
  Errors
  Linking
  Maps
  Novotes
  Op
  RTL
  RTLagreement
  Smallstep
.
Import ListNotations.

Definition not_vote (instr : instruction) : Prop :=
  match instr with
  | Ibuiltin ef args res succ => not (is_vote_builtin ef)
  | _ => True
  end.

Definition no_votes_code (c : code) : Prop :=
  forall pc instr, c ! pc = Some instr -> not_vote instr.

Inductive no_votes_fundef : fundef -> Prop :=
| no_votes_Internal : forall f,
    no_votes_code f.(fn_code) ->
    no_votes_fundef (Internal f)
| no_votes_external : forall ef,
    no_votes_fundef (External ef).

Inductive no_votes_globdef : globdef fundef unit -> Prop :=
| no_votes_Gfun : forall fd,
    no_votes_fundef fd ->
    no_votes_globdef (Gfun fd)
| no_votes_Gvar : forall v,
    no_votes_globdef (Gvar v).

Inductive no_votes : RTL.program -> Prop :=
| no_votes_program : forall defs public main,
    Forall (fun id_def => no_votes_globdef (snd id_def)) defs ->
    no_votes {| prog_defs := defs
              ; prog_public := public
              ; prog_main := main |}.

Section IMPLIES_AGREEMENT.

Variable p : program.
  
Lemma no_votes_weak_agreement :
  no_votes p ->
  rtl_weak_agreement p.
Admitted.

End IMPLIES_AGREEMENT.

Lemma check_program_sound p tp :
  check_program p = OK tp ->
  no_votes tp.
Admitted.

Definition match_prog (prog tprog: program) :=
  match_program (fun cu f tf => check_fundef f = OK tf) eq prog tprog.

Lemma check_program_match:
  forall prog tprog, check_program prog = OK tprog -> match_prog prog tprog.
Proof.
  intros. eapply match_transform_partial_program_contextual; eauto.
Qed.

Theorem check_program_correct
  {VT: Builtins2.vote_type} {vsem: Builtins2.VoteSemantics VT} :
  forall p tp, match_prog p tp ->
          forward_simulation (RTL.semantics p) (RTL.semantics tp).
Proof.
Admitted.
