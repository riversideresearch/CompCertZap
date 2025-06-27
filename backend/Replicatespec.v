(** * Relational specificaton of the TMR transformation. *)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Sorting.Permutation.
Require Import
  AST
  Coqlib
  Errors
  Globalenvs
  Integers
  Linking
  Maps
  Memory
  Op
  Registers
  Replicate
  RTLgen
  RTLtyping
  Smallstep
  Values
.
Require Import RTL.
Require Import Replicate.
Require Import Errors.
Import ListNotations.

Local Open Scope positive_scope.

Ltac gen_contra :=
  try match goal with
  | [H: RTLgen.Error _ = RTLgen.OK _ _ _ |- _ ] => inv H
  | [H: RTLgen.OK _ _ _ = RTLgen.Error _ |- _ ] => inv H
  end.

Ltac gen_inv :=
  match goal with
  | [H: RTLgen.OK _ _ _ = RTLgen.OK _ _ _ |- _ ] => inv H
  end.

Ltac gen_case H :=
  match goal with
  | [ _: match ?X with
         | RTLgen.Error _ => _
         | RTLgen.OK _ _ _ => _ end = _ |- _ ] =>
      destruct X eqn:H
  end; gen_contra; try gen_inv.

Ltac egen_case :=
  let H := fresh "H" in
  gen_case H.

Ltac lr_case :=
  match goal with
  | [ _: match ?X with
         | left _ => _
         | right _ => _ end = _ |- _ ] =>
      destruct X
  end; gen_contra; try gen_inv.

Ltac reserve_instr_inv :=
  match goal with
  | [ H: reserve_instr ?s = RTLgen.OK ?n ?s' ?pf |- _ ] => inv H
  end.

Ltac state_incr_inv :=
  match goal with
  | [ H: state_incr ?s1 ?s2 |- _ ] => inv H
  end.

(**
<<rm_wf rm dom>> imposes an invariant on the restriction of
replication map <<rm>> to domain <<dom>>. Roughly, it means all
registers in the codomain are "fresh".
*)
Section rm_wf.
  Context {rm : replmap} {dom : list reg}.
  Notation R2 r1 := (fst (rm # r1)).
  Notation R3 r1 := (snd (rm # r1)).

  Record rm_wf : Prop := {
    rm_wf_nodup_1 r1 : In r1 dom -> NoDup [r1; R2 r1; R3 r1];
    rm_wf_nodup_2 r1 r1' : r1 <> r1' -> In r1 dom -> In r1' dom ->
      NoDup [r1; R2 r1; R3 r1; r1'; R2 r1'; R3 r1'];
  }.
End rm_wf.
#[global] Arguments rm_wf : clear implicits.

Create HintDb rm_wf discriminated.

Create HintDb symmetry discriminated.
Global Hint Extern 1000 (_ <> _) => symmetry : symmetry.

Section sep_1.
  Context {rm dom} (Hrm : rm_wf rm dom).
  Context (r1 : reg) (Hin : In r1 dom).
  Notation r2 := (fst (rm # r1)).
  Notation r3 := (snd (rm # r1)).

  Ltac proof :=
    generalize (rm_wf_nodup_1 Hrm _ Hin);
    rewrite !NoDup_cons_iff; clear; firstorder.
  Lemma rm_wf_ne_12 : r1 <> r2.
  Proof. proof. Qed.
  Lemma rm_wf_ne_13 : r1 <> r3.
  Proof. proof. Qed.
  Lemma rm_wf_ne_23 : r2 <> r3.
  Proof. proof. Qed.
End sep_1.
#[global] Hint Resolve
  rm_wf_ne_12 rm_wf_ne_23 rm_wf_ne_13
: rm_wf.

(**
Here and elsewhere we restate things with redundant assumptions <<rm #
r1 = (r2, r3)>> to facilitate proofs which need to <<destruct>> such
pairs. (We could perhaps make such <<destruct>>s optional by switching
from pairs to a dedicated record type with primitive projections.)
*)
Section sep_1_get.
  Context {rm dom} (Hrm : rm_wf rm dom).
  Context (r1 : reg) (Hin : In r1 dom).
  Context (r2 r3 : reg) (Hget : rm # r1 = (r2, r3)).

  Tactic Notation "lift" open_constr(lem) :=
    generalize (lem Hrm _ Hin); now rewrite Hget.
  Lemma rm_wf_ne_12_get : r1 <> r2.
  Proof. lift rm_wf_ne_12. Qed.
  Lemma rm_wf_ne_13_get : r1 <> r3.
  Proof. lift rm_wf_ne_13. Qed.
  Lemma rm_wf_ne_23_get : r2 <> r3.
  Proof. lift rm_wf_ne_23. Qed.
End sep_1_get.
#[global] Hint Resolve
  rm_wf_ne_12_get rm_wf_ne_13_get rm_wf_ne_23_get
: rm_wf.

Section sep_2.
  Context {rm dom} (Hrm : rm_wf rm dom).
  Context (r1 : reg) (Hin : In r1 dom).
  Context (r1' : reg) (Hin' : In r1' dom).
  Notation r2 := (fst (rm # r1)). Notation r3 := (snd (rm # r1)).
  Notation r2' := (fst (rm # r1')). Notation r3' := (snd (rm # r1')).

  Tactic Notation "from" open_constr(NE) :=
    generalize (rm_wf_nodup_2 Hrm _ _ NE Hin Hin');
    rewrite !NoDup_cons_iff; clear; firstorder.
  Tactic Notation "lift" open_constr(lem) :=
    let NE := fresh in
    destruct (peq r1 r1') as [->|NE];
    [ eapply lem; eauto
    | from NE ].
  Lemma rm_wf_ne_2'1 : r2' <> r1.
  Proof. symmetry. lift rm_wf_ne_12. Qed.
  Lemma rm_wf_ne_2'2 : r1 <> r1' -> r2' <> r2.
  Proof. intros NE. from NE. Qed.
  Lemma rm_wf_ne_2'3 : r2' <> r3.
  Proof. lift rm_wf_ne_23. Qed.
  Lemma rm_wf_ne_3'1 : r3' <> r1.
  Proof. symmetry. lift rm_wf_ne_13. Qed.
  Lemma rm_wf_ne_3'2 : r3' <> r2.
  Proof. symmetry. lift rm_wf_ne_23. Qed.
  Lemma rm_wf_ne_3'3 : r1 <> r1' -> r3' <> r3.
  Proof. intros NE. from NE. Qed.
End sep_2.
#[global] Hint Resolve
  rm_wf_ne_2'1 rm_wf_ne_2'2 rm_wf_ne_2'3
  rm_wf_ne_3'1 rm_wf_ne_3'2 rm_wf_ne_3'3
: rm_wf.

Section sep_2_get.
  Context {rm dom} (Hrm : rm_wf rm dom).
  Context (r1 : reg) (Hin : In r1 dom).
  Context (r2 r3 : reg) (Hget : rm # r1 = (r2, r3)).
  Context (r1' : reg) (Hin' : In r1' dom).
  Context (r2' r3' : reg) (Hget' : rm # r1' = (r2', r3')).

  Tactic Notation "lift" open_constr(lem) :=
    generalize (lem Hrm _ Hin _ Hin'); now rewrite ?Hget, ?Hget'.
  Lemma rm_wf_ne_2'1_get : r2' <> r1.
  Proof. lift rm_wf_ne_2'1. Qed.
  Lemma rm_wf_ne_2'2_get : r1 <> r1' -> r2' <> r2.
  Proof. lift rm_wf_ne_2'2. Qed.
  Lemma rm_wf_ne_2'3_get : r2' <> r3.
  Proof. lift rm_wf_ne_2'3. Qed.
  Lemma rm_wf_ne_3'1_get : r3' <> r1.
  Proof. lift rm_wf_ne_3'1. Qed.
  Lemma rm_wf_ne_3'2_get : r3' <> r2.
  Proof. lift rm_wf_ne_3'2. Qed.
  Lemma rm_wf_ne_3'3_get : r1 <> r1' -> r3' <> r3.
  Proof. lift rm_wf_ne_3'3. Qed.
End sep_2_get.
#[global] Hint Resolve
  rm_wf_ne_2'1_get rm_wf_ne_2'2_get rm_wf_ne_2'3_get
  rm_wf_ne_3'1_get rm_wf_ne_3'2_get rm_wf_ne_3'3_get
: rm_wf.

Lemma rm_wf_nil rm : rm_wf rm nil.
Proof. split; contradiction. Qed.

Lemma rm_wf_cons {rm dom} r1 r2 r3 :
  rm_wf rm dom ->
  NoDup [r1; r2; r3] ->
  (
    forall r1', r1 <> r1' -> In r1' dom ->
    NoDup [r1; r2; r3; r1'; fst (rm # r1'); snd (rm # r1')]
  ) ->
  rm_wf (rm # r1 <- (r2, r3)) (r1 :: dom).
Proof.
  intros Hrm ? Hnodup. split.
  { intros r [->|Hin]; [now rewrite Regmap.gss|].
    destruct (peq r r1) as [->|?]; [now rewrite Regmap.gss|].
    rewrite Regmap.gso; [|easy].
    eapply rm_wf_nodup_1; eauto. }
  { intros r s NE [->|Hin] [->|Hin'].
    - easy.
    - rewrite Regmap.gss, Regmap.gso; [|easy]. simpl.
      now apply Hnodup.
    - rewrite Regmap.gss, Regmap.gso; [|easy]. simpl.
      apply not_eq_sym in NE. generalize (Hnodup _ NE Hin).
      rewrite !NoDup_cons_iff. clear. firstorder.
    - destruct (peq r r1) as [->|?], (peq s r1) as [->|?].
      + contradiction.
      + rewrite Regmap.gss, Regmap.gso; [|easy]. simpl.
        now apply Hnodup.
      + rewrite Regmap.gso, Regmap.gss; [|easy]. simpl.
        apply not_eq_sym in NE. generalize (Hnodup _ NE Hin).
        rewrite !NoDup_cons_iff. clear. firstorder.
      + rewrite Regmap.gso, Regmap.gso; [|easy..].
        eapply rm_wf_nodup_2; eauto. }
Qed.

Lemma rm_wf_permute dom1 dom2 rm :
  Permutation dom1 dom2 ->
  rm_wf rm dom1 ->
  rm_wf rm dom2.
Proof.
  intros P ?. split.
  { intros r. rewrite <-P. eapply rm_wf_nodup_1; eauto. }
  { intros r s ?. rewrite <-P. eapply rm_wf_nodup_2; eauto. }
Qed.

Lemma rm_wf_mono dom1 dom2 rm :
  (forall r, In r dom2 -> In r dom1) ->
  rm_wf rm dom1 ->
  rm_wf rm dom2.
Proof.
  intros D ?. split.
  { intros r ?%D. eapply rm_wf_nodup_1; eauto. }
  { intros r s NE ?%D ?%D. eapply rm_wf_nodup_2; eauto. }
Qed.

Lemma rm_wf_cons_inv r1 dom rm :
  rm_wf rm (r1 :: dom) ->
  rm_wf rm dom.
Proof. apply rm_wf_mono. intros ??. now right. Qed.
#[global] Hint Resolve rm_wf_cons_inv : rm_wf.

#[global] Instance: Params (@rm_wf) 1 := {}.
#[global] Instance rm_wf_permute' rm :
  Proper (Permutation (A:=reg) ==> iff) (rm_wf rm).
Proof.
  intros dom1 dom2 P. split; now apply rm_wf_permute.
Qed.

Inductive rm_l (rm : replmap)
  : list reg -> list reg -> list reg -> Prop :=
| match_nil : rm_l rm [] [] []
| match_cons : forall r1 r2 r3 rs1 rs2 rs3,
    rm !! r1 = (r2, r3) ->
    rm_l rm rs1 rs2 rs3 ->
    rm_l rm (r1 :: rs1) (r2 :: rs2) (r3 :: rs3).

Definition comp_of_typ (ty : typ) : comparison -> condition :=
  match ty with
  | Tint => Ccompu
  | Tlong => Ccomplu
  | Tsingle => Ccompfs
  | Tfloat => Ccompf
  | _ => Ccomp
  end.

Definition is_actual_type (ty : typ) : Prop :=
  match ty with
  | Tany32 => False
  | Tany64 => False
  | _ => True
  end.

Inductive maj_voteR
  (c : code) (ty : typ) (r1 r2 r3 : reg) (pc succ : node) : Prop :=
| maj_vote_1 :
  forall vote,
    is_actual_type ty ->
    maj_vote_of_typ ty r1 r2 r3 = Some vote ->
    c ! pc = Some (vote succ) ->
    maj_voteR c ty r1 r2 r3 pc succ.

Inductive maj_vote_regsR c re rm : list reg -> node -> node -> Prop :=
| maj_vote_regs_nil :
  forall pc,
    maj_vote_regsR c re rm nil pc pc
| maj_vote_regs_cons :
  forall r1 r2 r3 args pc succ n,
    rm # r1 = (r2, r3) ->
    maj_vote_regsR c re rm args pc n ->
    maj_voteR c (re r1) r1 r2 r3 n succ ->
    maj_vote_regsR c re rm (r1 :: args) pc succ.

Inductive smoveR
  (c : code) (ty : typ) (src dst1 dst2 : reg) (pc succ : node): Prop :=
| smove_1 :
  forall n mov1 mov2,
    smove ty src dst1 = Some mov1 ->
    smove ty src dst2 = Some mov2 ->
    c ! pc = Some (mov1 n) ->
    c ! n = Some (mov2 succ) ->
    smoveR c ty src dst1 dst2 pc succ.

Ltac smoveR_inv :=
  try match goal with
  | [H: smoveR _ _ _ _ _ _ _ |- _ ] => inv H
  end.

Inductive copy_allR (re : regenv) (rm : replmap) (c : code) : list reg -> node -> node -> Prop :=
| copy_all_nil :
  forall n,
    copy_allR re rm c [] n n
| copy_all_cons :
  forall r1 rs succ n p r2 r3,
    rm # r1 = (r2, r3) ->
    copy_allR re rm c rs n p ->
    smoveR c (re r1) r1 r2 r3 p succ ->
    copy_allR re rm c (r1 :: rs) n succ.

Lemma copy_to_shadows_smoveR
  (rm : replmap) (ty : typ) (r1 r2 r3 : reg) (pc succ : node)
  (u : unit) (s0 s1 : RTLgen.state) pf (c : code) :
  rm # r1 = (r2, r3) ->
  pc < s0.(st_nextnode) ->
  copy_to_shadows rm ty r1 pc succ s0 = RTLgen.OK u s1 pf ->
  (forall p i, s1.(st_code) ! p = Some i -> c ! p = Some i) ->
  smoveR c ty r1 r2 r3 pc succ.
Proof.
  intros Hr1 Hpc Hcopy Hc.
  unfold copy_to_shadows in Hcopy.
  rewrite Hr1 in Hcopy.
  unfold RTLgen.bind in Hcopy.
  unfold error in Hcopy.
  simpl in *.
  destruct (smove ty r1 r2) eqn:Hmov1; gen_contra.
  destruct (smove ty r1 r3) eqn:Hmov2; gen_contra.
  unfold update_instr in Hcopy.
  repeat egen_case.
  repeat lr_case.
  simpl in *.
  repeat state_incr_inv.
  simpl in *; unfold Ple in *.
  econstructor; eauto.
  - apply Hc.
    rewrite PTree.gso; try lia.
    rewrite PTree.gss; reflexivity.
  - apply Hc.
    rewrite PTree.gss; reflexivity.
Qed.

Lemma copy_all_to_shadows_copy_allR re rm params n succ s0 s1 pf c :
  copy_all_to_shadows re rm params succ s0 = RTLgen.OK n s1 pf ->
  (forall p i, s1.(st_code) ! p = Some i -> c ! p = Some i) ->
  copy_allR re rm c params n succ.
Proof.
  revert pf.
  revert s0 s1 n succ.
  induction params; simpl; intros s0 s1 n succ pf Hcopy Hc; inv Hcopy.
  { constructor. }
  unfold RTLgen.bind in H0; simpl in H0.
  repeat egen_case.
  destruct (rm # a) eqn:Ha.
  econstructor; eauto.
  eapply copy_to_shadows_smoveR; eauto; simpl; try lia.
  intros p i Hpi.
  apply Hc.
  clear H1.
  repeat state_incr_inv.
  simpl in *.
  destruct (H2 p); congruence.
Qed.

Inductive is_BR {A: Type} : builtin_res A -> Prop :=
| is_br_BR : forall x, is_BR (BR x).

Definition is_BR_dec {A : Type} (br : builtin_res A)
  : { is_BR br } + { ~ is_BR br }.
Proof.
  destruct br.
  - left; constructor.
  - right; intro H; inv H.
  - right; intro H; inv H.
Qed.

(** [match_instr re rm c pc i] means that the translated code [c]
    contains instructions starting at pc] that correspond to
    instruction [i] in the original program, wrt. register environment
    [regenv] and replication map [rm]. *)
Inductive match_instr
  (re : regenv) (rm : replmap) (c : code) (pc : positive)
  : instruction -> Prop :=
| match_Inop :
  forall n,
    PTree.get pc c = Some (Inop n) ->
    match_instr re rm c pc (Inop n)
| match_Iop :
  forall op args1 args2 args3 res1 res2 res3 n1 n2 succ
    (ARGS : rm_l rm args1 args2 args3)
    (RM_RES : rm !! res1 = (res2, res3))
    (PC : c ! pc = Some (Iop op args2 res2 n1))
    (N1 : c ! n1 = Some (Iop op args3 res3 n2))
    (N2 : c ! n2 = Some (Iop op args1 res1 succ)),
    match_instr re rm c pc (Iop op args1 res1 succ)
| match_iload :
  forall chunk addr args res1 res2 res3 n1 n2 succ
    (VOTE_ARGS : maj_vote_regsR c re rm args pc n1)
    (N1 : c ! n1 = Some (Iload chunk addr args res1 n2))
    (RM_RES : rm !! res1 = (res2, res3))
    (MOVE : smoveR c (re res1) res1 res2 res3 n2 succ),
  match_instr re rm c pc (Iload chunk addr args res1 succ)
| match_Istore :
  forall chunk addr args src1 src2 src3 n succ
    (RM_SRC : rm !! src1 = (src2, src3))
    (VOTE_REGS : maj_vote_regsR c re rm (src1 :: args) pc n)
    (N : c ! n = Some (Istore chunk addr args src1 succ)),
    match_instr re rm c pc (Istore chunk addr args src1 succ)
| match_Icall :
  forall sig fn args res1 res2 res3 succ n1 n2
    (VOTE_ARGS : maj_vote_regsR c re rm (regs_of_fn fn ++ args) pc n1)
    (N1 : c ! n1 = Some (Icall sig fn args res1 n2))
    (RM_RES : rm !! res1 = (res2, res3))
    (MOVE : smoveR c (re res1) res1 res2 res3 n2 succ),
    match_instr re rm c pc (Icall sig fn args res1 succ)
| match_Itailcall :
  forall sig fn args n
    (VOTE_ARGS : maj_vote_regsR c re rm (regs_of_fn fn ++ args) pc n)
    (N : c ! n = Some (Itailcall sig fn args)),
    match_instr re rm c pc (Itailcall sig fn args)
| match_Ibuiltin_1 :
  forall ef bargs bres n succ
    (NORES : ~ is_BR bres) (* no result register *)
    (VOTE_ARGS : maj_vote_regsR c re rm (regs_of_builtin_args bargs) pc n)
    (N : c ! n = Some (Ibuiltin ef bargs bres succ)),
    match_instr re rm c pc (Ibuiltin ef bargs bres succ)
| match_Ibuiltin_2 :
  forall ef bargs res1 res2 res3 n1 n2 succ
    (VOTE_ARGS : maj_vote_regsR c re rm (regs_of_builtin_args bargs) pc n1)
    (N1 : c ! n1 = Some (Ibuiltin ef bargs (BR res1) n2))
    (RM_RES : rm # res1 = (res2, res3))
    (MOVE : smoveR c (re res1) res1 res2 res3 n2 succ),
    match_instr re rm c pc (Ibuiltin ef bargs (BR res1) succ)
| match_Icond :
  forall cond args ifso ifnot n
    (VOTE_ARGS : maj_vote_regsR c re rm args pc n)
    (N : c ! n = Some (Icond cond args ifso ifnot)),
    match_instr re rm c pc (Icond cond args ifso ifnot)
| match_Ijumptable :
  forall arg1 arg2 arg3 tbl n
    (RM_ARG : rm # arg1 = (arg2, arg3))
    (VOTE : maj_voteR c (re arg1) arg1 arg2 arg3 pc n)
    (N : c ! n = Some (Ijumptable arg1 tbl)),
    match_instr re rm c pc (Ijumptable arg1 tbl)
| match_Ireturn_1 :
  forall (PC : c ! pc = Some (Ireturn None)),
  match_instr re rm c pc (Ireturn None)
| match_Ireturn_2 :
  forall arg1 arg2 arg3 n
    (RM_ARG : rm # arg1 = (arg2, arg3))
    (VOTE : maj_voteR c (re arg1) arg1 arg2 arg3 pc n)
    (N : c ! n = Some (Ireturn (Some arg1))),
    match_instr re rm c pc (Ireturn (Some arg1)).

(** [match_code re rm c c'] when for every instruction [i] at location
    [pc] in the original code [c], there is a matching code sequence
    at [pc] in the translated code [c'].*)
Definition match_code (re : regenv) (rm : replmap) (c c': code) : Prop :=
  forall p i, c ! p = Some i -> match_instr re rm c' p i.

Section regs_of_builtin_args.
  Lemma params_of_builin_arg_regs_of_builtin_arg r a :
    In r (params_of_builtin_arg a) ->
    In r (regs_of_builtin_arg a).
  Proof.
    revert r. induction a; simpl; auto.
    all: intros r; rewrite !in_app_iff; firstorder.
  Qed.
  Local Hint Resolve params_of_builin_arg_regs_of_builtin_arg : core.

  Lemma params_of_builtin_args_regs_of_builtin_args r args :
    In r (params_of_builtin_args args) ->
    In r (regs_of_builtin_args args).
  Proof.
    induction args; simpl; auto.
    rewrite !in_app_iff. firstorder.
  Qed.
End regs_of_builtin_args.

(*
Inductive reg_used_in_instr (r : reg) : instruction -> Prop :=
| reg_used_Iop_args : forall op args res succ,
    In r args ->
    reg_used_in_instr r (Iop op args res succ)
| reg_used_Iop_res : forall op args succ,
    reg_used_in_instr r (Iop op args r succ)
| reg_used_Iload_args : forall chunk addr args res succ,
    In r args ->
    reg_used_in_instr r (Iload chunk addr args res succ)
| reg_used_Iload_res : forall chunk addr args succ,
    reg_used_in_instr r (Iload chunk addr args r succ)
| reg_used_Istore_args : forall chunk addr args src succ,
    In r args ->
    reg_used_in_instr r (Istore chunk addr args src succ)
| reg_used_Istore_src : forall chunk addr args succ,
    reg_used_in_instr r (Istore chunk addr args r succ)
| reg_used_Icall_fn : forall sig args dst succ,
    reg_used_in_instr r (Icall sig (inl r) args dst succ)
| reg_used_Icall_args : forall sig fn args dst succ,
    In r args ->
    reg_used_in_instr r (Icall sig fn args dst succ)
| reg_used_Icall_dst : forall sig fn args succ,
    reg_used_in_instr r (Icall sig fn args r succ)
| reg_used_Itailcall_fn : forall sig args,
    reg_used_in_instr r (Itailcall sig (inl r) args)
| reg_used_Itailcall_args : forall sig fn args,
    In r args ->
    reg_used_in_instr r (Itailcall sig fn args)
| reg_used_Ibuiltin_args : forall ef bargs bres succ,
    In r (regs_of_builtin_args bargs) ->
    reg_used_in_instr r (Ibuiltin ef bargs bres succ)
| reg_used_Ibuiltin_res : forall ef bargs succ,
    reg_used_in_instr r (Ibuiltin ef bargs (BR r) succ)
| reg_used_Icond : forall cond args ifso ifnot,
    In r args ->
    reg_used_in_instr r (Icond cond args ifso ifnot)
| reg_used_Ijumptable : forall tbl,
    reg_used_in_instr r (Ijumptable r tbl)
| reg_used_Ireturn :
  reg_used_in_instr r (Ireturn (Some r)).
*)
Definition reg_used_in_instr (r : reg) (instr : instruction) : Prop :=
  Regset.In r (instr_regs instr).

Section reg_used_in_instr.
  (* Local Hint Constructors reg_used_in_instr : core. *)
  Local Hint Resolve params_of_builtin_args_regs_of_builtin_args : core.

  Lemma instr_uses_reg_used_in_instr r i :
    In r (instr_uses i) -> reg_used_in_instr r i.
  Proof.
    unfold reg_used_in_instr.
    (* rewrite <- Regsetaux.in_elements. *)
    (* Regsetaux.in_elements:
  forall (r : reg) (X : Regset.t),
  In r (Regset.elements X) <-> Regset.In r X *)
    destruct i; simpl.
    - contradiction.
    - rewrite Regsetaux.FM.union_iff.
      intros H.
      left.
      apply Regsetaux.in_of_list_1.
      assumption.
    - rewrite Regsetaux.FM.union_iff.
      intros H.
      left.
      apply Regsetaux.in_of_list_1.
      assumption.
    - rewrite Regsetaux.FM.union_iff.
      intros [->|Fred].
      + right.
        apply Regset.singleton_2.
        reflexivity.
      + left.
        apply Regsetaux.in_of_list_1.
        assumption.
   (* We want to [destruct s0] but [s0] is fragile (because Rocq chose the
    * name], so instead we match on any hypothesis of the right type, which is
    * robust, and destruct that. *)
   - lazymatch goal with
     | H : reg + ident |- _ => destruct H
     end.
     + simpl.
       intros [->|?].
       * rewrite Regsetaux.FM.union_iff.
         left.
         now apply Regset.add_1.
       * rewrite Regsetaux.FM.union_iff.
         left.
         apply Regset.add_2.
         now apply Regsetaux.in_of_list_1.
     + rewrite Regsetaux.FM.union_iff.
       intros H.
       left.
       apply Regsetaux.in_of_list_1.
       assumption.
   - lazymatch goal with
     | H : reg + ident |- _ => destruct H
     end.
     + simpl.
       intros [->|?].
       * now apply Regset.add_1.
       * apply Regset.add_2.
         now apply Regsetaux.in_of_list_1.
     + apply Regsetaux.in_of_list_1.
   - rewrite Regsetaux.FM.union_iff.
     intros H.
     left.
     Set Nested Proofs Allowed.
     Lemma regs_params_of_builtin_args l :
       regs_of_builtin_args l = params_of_builtin_args l.
     Proof.
       unfold params_of_builtin_args.
       Search fold_right fold_left.
       unfold regs_of_builtin_args.
     (* TODO eliminate regs_of_builtin_args and just use params_of_builtin_args.
        Then this lemma won't be needed *)
       admit.
     Admitted.
     rewrite regs_params_of_builtin_args.
     apply Regsetaux.in_of_list_1.
     assumption.
   - apply Regsetaux.in_of_list_1.
   - intros [->|?]. Search Regset.In Regset.singleton.
     + apply Regset.singleton_2.
       reflexivity.
     + contradiction.
   - destruct o.
     + simpl.
       intros [->|?].
       * apply Regset.singleton_2.
         reflexivity.
       * contradiction.
     + contradiction.

  (* If the above have enough patterns, try something like this to compress proof:
    all: repeat lazymatch goal with
    | H : False |- _ => contradiction
    | H : (_ = _) \/ _ |- _ => destruct H as [->|?]
    | H : reg + ident |- _ => destruct H; simpl in Hr
    | H : option reg |- _ => destruct H; simpl in Hr
    | _ => auto
    end. *)
  Qed.
End reg_used_in_instr.

Definition reg_used_in_code (c : code) (r : reg) : Prop :=
  exists pc instr,
    c! pc = Some instr /\ reg_used_in_instr r instr.

Lemma instr_uses_reg_used_in_code c pc i :
  c!pc = Some i ->
  Forall (reg_used_in_code c) (instr_uses i).
Proof.
  intros. apply Forall_forall. intros r ?%instr_uses_reg_used_in_instr.
  firstorder.
Qed.

(** A register is 'used' in a function whenever it either appears in
    the function's parameter list or is used somewhere in its code. *)
Definition reg_used (params : list reg) (c : code) (r : reg) : Prop :=
  In r params \/ reg_used_in_code c r.

Lemma reg_used_in_params_used params c r :
  In r params -> reg_used params c r.
Proof. now left. Qed.
Lemma reg_used_in_code_used params c r :
  reg_used_in_code c r -> reg_used params c r.
Proof. now right. Qed.

#[global] Hint Resolve
  reg_used_in_params_used
  reg_used_in_code_used
: rm_wf.

Lemma reg_used_params params c :
  Forall (reg_used params c) params.
Proof.
  unfold reg_used; apply Forall_forall; auto.
Qed.

Lemma reg_used_cons p params c r :
  reg_used params c r ->
  reg_used (p :: params) c r.
Proof.
  intros [Hin | Hused].
  - left; right; auto.
  - right; auto.
Qed.

Lemma reg_used_cons_inv p ps c r :
  reg_used (p :: ps) c r -> r = p \/ reg_used ps c r.
Proof.
  destruct 1 as [Hused|Hused].
  { destruct Hused as [->|?]. now left. now right; left. }
  { now right; right. }
Qed.

(**
<<rm_inv U rm>> imposes an invariant on replication map <<rm>>.
Roughly, it says the map sends used registers (i.e., satisfying <<U>>)
to unused registers.
*)
Record rm_inv {U : reg -> Prop} {rm : replmap} : Prop := {
  rm_used_2 r1 : U r1 -> ~ U (fst (rm # r1));
  rm_used_3 r1 : U r1 -> ~ U (snd (rm # r1));
}.
#[global] Arguments rm_inv : clear implicits.

Create HintDb rm_inv discriminated.

Section used_get.
  Context {U rm} (Hrm : rm_inv U rm).
  Context (r1 : reg) (Hused : U r1).
  Context (r2 r3 : reg) (Hget : rm # r1 = (r2, r3)).

  Lemma rm_used_2_get : ~ U r2.
  Proof. generalize (rm_used_2 Hrm _ Hused). now rewrite Hget. Qed.
  Lemma rm_used_3_get : ~ U r3.
  Proof. generalize (rm_used_3 Hrm _ Hused). now rewrite Hget. Qed.
End used_get.
#[global] Hint Resolve
  rm_used_2_get rm_used_3_get
  reg_used_in_params_used
  reg_used_in_code_used
: rm_inv.

Section sep.
  Context {U rm} (Hrm : rm_inv U rm).
  Context (r1 : reg) (Hused : U r1).
  Notation r2 := (fst (rm # r1)).
  Notation r3 := (snd (rm # r1)).

  Tactic Notation "from" open_constr(lem) :=
    generalize (lem Hrm _ Hused); intros ?? ->; auto.
  Lemma rm_inv_ne_2 r : U r -> r <> r2.
  Proof. from rm_used_2. Qed.
  Lemma rm_inv_ne_3 r : U r -> r <> r3.
  Proof. from rm_used_3. Qed.
End sep.
#[global] Hint Resolve rm_inv_ne_2 rm_inv_ne_3 : rm_inv.

Section sep_get.
  Context {U rm} (Hrm : rm_inv U rm).
  Context (r1 : reg) (Hused : U r1).
  Context (r2 r3 : reg) (Hget : rm # r1 = (r2, r3)).
  Context (r : reg) (Hr : U r).

  Tactic Notation "lift" open_constr(lem) :=
    generalize (lem Hrm _ Hused _ Hr); rewrite Hget; auto.
  Lemma rm_inv_ne_2_get : r <> r2.
  Proof. lift rm_inv_ne_2. Qed.
  Lemma rm_inv_ne_3_get : r <> r3.
  Proof. lift rm_inv_ne_3. Qed.
End sep_get.
#[global] Hint Resolve
  rm_inv_ne_2_get rm_inv_ne_3_get
: rm_inv.

(** Possibly uninitialized registers *)

Create HintDb uregs_ok discriminated.

Record uregs_ok (c : code) (params : list reg) (uregs : list reg) : Prop := {
  uregs_ok_nodup : NoDup uregs;
  uregs_ok_params : list_disjoint params uregs;
  uregs_ok_code r : In r uregs -> reg_used_in_code c r;
}.

Lemma uregs_ok_nodup_params_uregs c params uregs :
  uregs_ok c params uregs ->
  NoDup params ->
  NoDup (params ++ uregs).
Proof.
  intros [HDu HD _] HDp. induction params as [|p params IH]; simpl; auto.
  rewrite NoDup_cons_iff in HDp. destruct HDp.
  constructor.
  { intros [?|Hp]%in_app_or; auto.
    apply list_disjoint_sym in HD.
    apply (list_disjoint_notin _ HD Hp).
    now left. }
  apply IH; auto. eapply list_disjoint_cons_left; eauto.
Qed.
#[global] Hint Resolve uregs_ok_nodup_params_uregs : uregs_ok.

Inductive match_function re rm : function -> function -> Prop :=
| match_fun : forall sig params uregs stacksize c c' entrypoint entrypoint'
  (RM_WF: rm_wf rm (all_regs_list params c))
  (RM_INV: rm_inv (reg_used params c) rm)
  (CODE: match_code re rm c c')
  (UREGS : uregs_ok c params uregs)
  (COPY: copy_allR re rm c' (prologue_copies params uregs) entrypoint' entrypoint),
    match_function re rm
      ({|
          fn_sig := sig
        ; fn_params := params
        ; fn_stacksize := stacksize
        ; fn_code := c
        ; fn_entrypoint := entrypoint
       |})
      ({|
          fn_sig := sig
        ; fn_params := params
        ; fn_stacksize := stacksize
        ; fn_code := c'
        ; fn_entrypoint := entrypoint'
        |}).

Inductive match_fundef: fundef -> fundef -> Prop :=
| match_internal :
  forall re rm f tf
    (WT: wt_function f re)
    (FUN : match_function re rm f tf),
    match_fundef (Internal f) (Internal tf)
| match_external :
  forall f,
    match_fundef (External f) (External f).

Lemma rm_l_map_rm rm l :
  rm_l rm l (map (fun r => fst rm # r) l) (map (fun r => snd rm # r) l).
Proof.
  induction l; constructor; auto.
  destruct (rm # a); reflexivity.
Qed.

Lemma state_incr_maj_voteR s s' ty r1 r2 r3 pc succ :
  (forall pc : positive, (st_code s) ! pc = None \/
                      (st_code s') ! pc = (st_code s) ! pc) ->
  maj_voteR (st_code s) ty r1 r2 r3 pc succ ->
  maj_voteR (st_code s') ty r1 r2 r3 pc succ.
Proof.
  intros Hle Hmaj; inv Hmaj.
  destruct (Hle pc) as [?|Hpc]; try congruence.
  econstructor; eauto.
  rewrite Hpc; eauto.
Qed.

Lemma state_incr_maj_vote_regsR re rm p s s' rs n :
  (forall pc : positive, (st_code s) ! pc = None \/
                      (st_code s') ! pc = (st_code s) ! pc) ->
  maj_vote_regsR (st_code s) re rm rs p n ->
  maj_vote_regsR (st_code s') re rm rs p n.
Proof.
  revert p n s s'.
  induction rs; intros p n s s' Hle Hmaj; inv Hmaj.
  { constructor. }
  econstructor; eauto.
  eapply state_incr_maj_voteR; eauto.
Qed.

Lemma state_incr_smoveR s s' ty r1 r2 r3 pc succ :
  (forall pc : positive, (st_code s) ! pc = None \/
                      (st_code s') ! pc = (st_code s) ! pc) ->
  smoveR (st_code s) ty r1 r2 r3 pc succ ->
  smoveR (st_code s') ty r1 r2 r3 pc succ.
Proof.
  intros Hle Hmaj; inv Hmaj.
  destruct (Hle pc) as [?|Hpc]; try congruence.
  destruct (Hle n) as [?|Hn]; try congruence.
  econstructor; eauto.
  - rewrite Hpc; eauto.
  - rewrite Hn; eauto.
Qed.

Lemma state_incr_copy_allR re rm p s s' rs n :
  (forall pc : positive, (st_code s) ! pc = None \/
                      (st_code s') ! pc = (st_code s) ! pc) ->
  copy_allR re rm (st_code s) rs p n ->
  copy_allR re rm (st_code s') rs p n.
Proof.
  revert p n s s'.
  induction rs; intros p n s s' Hle Hcopy; inv Hcopy.
  { constructor. }
  econstructor; eauto.
  eapply state_incr_smoveR; eauto.
Qed.

Lemma state_incr_match_instr re rm p i s s' :
  state_incr s s' ->
  match_instr re rm (st_code s) p i ->
  match_instr re rm (st_code s') p i.
Proof.
  intros Hs Hmatch.
  inv Hs.
  inv Hmatch.
  - constructor; destruct (H1 p); congruence.
  - destruct (H1 p) as [?|Hs']; try congruence.
    destruct (H1 n1) as [?|Hs'1]; try congruence.
    destruct (H1 n2) as [?|Hs'2]; try congruence.
    econstructor; eauto.
    + rewrite Hs'; eauto.
    + rewrite Hs'1; eauto.
    + rewrite Hs'2; eauto.
  - inv MOVE.
    destruct (H1 n) as [?|Hn]; try congruence.
    destruct (H1 n1) as [?|Hn1]; try congruence.
    destruct (H1 n2) as [?|Hn2]; try congruence.
    econstructor; eauto.
    + eapply state_incr_maj_vote_regsR; eauto.
    + rewrite Hn1; eauto.
    + econstructor; eauto.
      * rewrite Hn2; eauto.
      * rewrite Hn; auto.
  - destruct (H1 n) as [?|Hs']; try congruence.
    econstructor; eauto.
    2: { rewrite Hs'; auto. }
    eapply state_incr_maj_vote_regsR; eauto.
  - inv MOVE.
    destruct (H1 n) as [?|Hn]; try congruence.
    destruct (H1 n1) as [?|Hn1]; try congruence.
    destruct (H1 n2) as [?|Hn2]; try congruence.
    econstructor; eauto.
    + eapply state_incr_maj_vote_regsR; eauto.
    + rewrite Hn1; eauto.
    + econstructor; eauto.
      * rewrite Hn2; eauto.
      * rewrite Hn; auto.
  - destruct (H1 n) as [?|Hn]; try congruence.
    econstructor; eauto.
    + eapply state_incr_maj_vote_regsR; eauto.
    + rewrite Hn; eauto.
  - econstructor; auto.
    + eapply state_incr_maj_vote_regsR; eauto.
    + destruct (H1 n); congruence.
  - destruct (H1 n1) as [?|Hn1]; try congruence.
    eapply match_Ibuiltin_2.
    + eapply state_incr_maj_vote_regsR; eauto.
    + rewrite  Hn1; eauto.
    + eauto.
    + eapply state_incr_smoveR; eauto.
  - destruct (H1 n) as [?|Hn]; try congruence.
    econstructor; eauto.
    + eapply state_incr_maj_vote_regsR; eauto.
    + rewrite Hn; eauto.
  - destruct (H1 n) as [?|Hn]; try congruence.
    econstructor; eauto.
    + eapply state_incr_maj_voteR; eauto.
    + rewrite Hn; eauto.
  - destruct (H1 p) as [?|Hp]; try congruence.
    constructor; rewrite Hp; auto.
  - destruct (H1 n) as [?|Hn]; try congruence.
    econstructor; eauto.
    + eapply state_incr_maj_voteR; eauto.
    + rewrite Hn; auto.
Qed.

Lemma maj_vote_of_typ_is_actual_type ty r1 r2 r3 i :
  maj_vote_of_typ ty r1 r2 r3 = Some i ->
  is_actual_type ty.
Proof.
  destruct ty; simpl; intro Hmaj; auto; inv Hmaj.
Qed.

Lemma maj_vote_maj_voteR re r1 r2 r3 pc succ s s' pf :
  pc < s.(st_nextnode) ->
  maj_vote re r1 r2 r3 pc s = RTLgen.OK succ s' pf ->
  maj_voteR s'.(st_code) (re r1) r1 r2 r3 pc succ.
Proof.
  unfold maj_vote, RTLgen.bind; simpl; intros Hlt Hmaj.
  destruct (maj_vote_of_typ (re r1) r1 r2 r3) eqn:Hty.
  2: { inv Hmaj. }
  repeat egen_case.
  unfold update_instr in *; simpl in *.
  lr_case; try congruence; lr_case.
  simpl in *.
  econstructor; eauto.
  2: { rewrite PTree.gss; reflexivity. }
  eapply maj_vote_of_typ_is_actual_type; eauto.
Qed.

Lemma maj_vote_succ_lt_nextnode re r1 r2 r3 pc succ s s' pf :
  pc < s.(st_nextnode) ->
  maj_vote re r1 r2 r3 pc s = RTLgen.OK succ s' pf ->
  succ < s'.(st_nextnode).
Proof.
  unfold maj_vote, RTLgen.bind; simpl; intros Hlt Hmaj.
  destruct (maj_vote_of_typ (re r1) r1 r2 r3) eqn:Hty.
  2: { inv Hmaj. }
  repeat egen_case.
  unfold update_instr in *; simpl in *.
  lr_case; try congruence; lr_case.
  simpl in *; lia.
Qed.

Lemma maj_vote_regs_succ_lt_nextnode re rm regs pc succ s s' pf :
  pc < s.(st_nextnode) ->
  maj_vote_regs re rm regs pc s = RTLgen.OK succ s' pf ->
  succ < s'.(st_nextnode).
Proof.
  revert pc succ s s' pf.
  induction regs; intros pc n s s' pf Hlt Hmaj; inv Hmaj; auto.
  unfold RTLgen.bind in H0.
  gen_case Hmaj.
  destruct (rm # a) eqn:Ha.
  egen_case.
  apply IHregs in Hmaj; auto.
  eapply maj_vote_succ_lt_nextnode; eauto.
Qed.

Lemma maj_vote_regs_maj_vote_regsR re rm regs pc succ s s' pf :
  pc < s.(st_nextnode) ->
  maj_vote_regs re rm regs pc s = RTLgen.OK succ s' pf ->
  maj_vote_regsR s'.(st_code) re rm regs pc succ.
Proof.
  revert pc succ s s' pf.
  induction regs; simpl; intros pc succ s s' pf Hlt Hmaj.
  { inv Hmaj; constructor. }
  unfold RTLgen.bind in Hmaj.
  gen_case H0.
  destruct (rm # a) eqn:Ha.
  destruct (maj_vote re a r r0 n s'0) eqn:Hm; gen_contra; gen_inv.
  pose proof H0 as H0'.
  apply maj_vote_regs_succ_lt_nextnode in H0'; auto.
  apply IHregs in H0; auto.
  econstructor; eauto.
  - eapply state_incr_maj_vote_regsR.
    2: { eauto. }
    clear Hm; inv s1; auto.
  - eapply maj_vote_maj_voteR; eauto.
Qed.

Lemma maj_voteR_ptree_set c ty r1 r2 r3 pc succ n i :
  c ! n = None ->
  maj_voteR c ty r1 r2 r3 pc succ ->
  maj_voteR (PTree.set n i c) ty r1 r2 r3 pc succ.
Proof.
  intros Hc Hmaj; inv Hmaj.
  econstructor; eauto.
  destruct (peq n pc);
    subst; try congruence.
  rewrite PTree.gso; eauto.
Qed.

Lemma maj_vote_regsR_ptree_set c re rm rs pc succ n i :
  c ! n = None ->
  maj_vote_regsR c re rm rs pc succ ->
  maj_vote_regsR (PTree.set n i c) re rm rs pc succ.
Proof.
  revert pc succ.
  induction rs; intros pc succ Hc Hmaj; inv Hmaj.
  { constructor. }
  econstructor; eauto.
  apply maj_voteR_ptree_set; auto.
Qed.

Lemma smoveR_ptree_set c ty r1 r2 r3 pc succ n i :
  c ! n = None ->
  smoveR c ty r1 r2 r3 pc succ ->
  smoveR (PTree.set n i c) ty r1 r2 r3 pc succ.
Proof.
  intros Hc Hmove; inv Hmove.
  econstructor; eauto.
  - destruct (peq n pc);
      subst; try congruence; rewrite PTree.gso; eauto.
  - destruct (peq n n0);
      subst; try congruence; rewrite PTree.gso; eauto.
Qed.

Lemma copy_allR_ptree_set re rm c rs pc succ n i :
  c ! n = None ->
  copy_allR re rm c rs pc succ ->
  copy_allR re rm (PTree.set n i c) rs pc succ.
Proof.
  revert pc succ.
  induction rs; intros pc succ Hc Hmaj; inv Hmaj.
  { constructor. }
  econstructor; eauto.
  apply smoveR_ptree_set; auto.
Qed.

(** The translation algorithm meets its relational specification. *)
Lemma iterM_match_instr
  p i (l : list (positive * instruction)) re rm s s' pf u :
  p < s.(st_nextnode) ->
  In (p, i) l ->
  iterM (transf_instr re rm) l s = RTLgen.OK u s' pf ->
  match_instr re rm (st_code s') p i.
Proof.
  revert s s' pf; induction l; simpl; intros s s' pf Hlt Hin Htransf.
  { contradiction. }
  unfold RTLgen.bind in Htransf.
  gen_case Hiter.
  gen_case Htransf'.
  destruct Hin as [?|Hin]; subst.
  - simpl in Htransf'.
    destruct i.

    (* Inop *)
    + unfold update_instr in Htransf'.
      repeat lr_case.
      simpl; constructor; rewrite PTree.gss; reflexivity.

    (* Iop *)
    + unfold RTLgen.bind in Htransf'.
      repeat egen_case.
      unfold update_instr in *.
      repeat lr_case.
      inv H; inv H1.
      destruct (rm # r) eqn:Hrmr; simpl in *.
      assert (p < st_nextnode s'0).
      { clear Hiter; inv s0; simpl in *; unfold Ple in *; lia. }
      eapply match_Iop with (pc := p)
                            (n1 := s'0.(st_nextnode))
                            (n2 := Pos.succ (s'0.(st_nextnode))); eauto.
      { apply rm_l_map_rm. }
      * rewrite 2!PTree.gso; try lia.
        rewrite PTree.gss; reflexivity.
      * rewrite PTree.gso; try lia.
        rewrite PTree.gss; reflexivity.
      * rewrite PTree.gss; reflexivity.

    (* Iload *)
    + unfold RTLgen.bind in Htransf'; simpl in Htransf'.
      repeat egen_case.
      unfold update_instr in H2.
      repeat lr_case; simpl.
      destruct (rm # r) eqn:Hr.
      eapply copy_to_shadows_smoveR in H0; eauto.
      2: { simpl; lia. }
      eapply match_iload with (n1:=n0); eauto.
      3: { apply smoveR_ptree_set; eauto. }
      2: { rewrite PTree.gss; auto. }
      eapply maj_vote_regsR_ptree_set; auto.
      eapply state_incr_maj_vote_regsR.
      2: { eapply maj_vote_regs_maj_vote_regsR.
           2: { eauto. }
           clear Hiter; inv s0; unfold Ple in *; lia. }
      intro pc; inv s5; auto.

    (* Istore *)
    + unfold RTLgen.bind in Htransf'.
      simpl in Htransf'.
      gen_case Hmaj.
      gen_case Hupd.
      replace ((do succ <- maj_vote_regs re rm l0 p;
                   let (r2, r3) := rm # r in maj_vote re r r2 r3 succ) s'0)
        with (maj_vote_regs re rm (r :: l0) p s'0) in Hmaj by auto.
      apply maj_vote_regs_maj_vote_regsR in Hmaj.
      2: { clear Hiter; inv s0; unfold Ple in *; lia. }
      unfold update_instr in Hupd.
      repeat lr_case.
      simpl in *.
      inv s1; inv s3; inv pf; simpl in *; unfold Ple in *.
      destruct (rm # r) eqn:Hrmr; simpl in *.
      econstructor.
      { eauto. }
      2: { rewrite PTree.gss; reflexivity. }
      apply maj_vote_regsR_ptree_set; auto.

    (* Icall *)
    + simpl in Htransf'; unfold RTLgen.bind in Htransf'; simpl in Htransf'.
      repeat egen_case.
      unfold copy_to_shadows in H0.
      destruct (rm # r) eqn:Hrmr.
      unfold RTLgen.bind in H0.
      unfold error in *.
      destruct (smove (re r) r r0) eqn:Hmov1; gen_contra.
      destruct (smove (re r) r r1) eqn:Hmov2; gen_contra.
      repeat egen_case.
      unfold update_instr in *.
      repeat lr_case.
      simpl in *.
      assert (p < st_nextnode s'0).
      { clear Hiter; inv s0; simpl in *; unfold Ple in *; lia. }
      assert (Hn0: n0 < s'1.(st_nextnode)).
      { eapply maj_vote_regs_succ_lt_nextnode.
        2: { eauto. }
        auto. }
      apply maj_vote_regs_maj_vote_regsR in H; auto.
      reserve_instr_inv.
      simpl in *.
      repeat state_incr_inv.
      simpl in *; unfold Ple in *.
      econstructor; eauto.
      * repeat apply maj_vote_regsR_ptree_set; eauto.
      * rewrite PTree.gss; reflexivity.
      * econstructor; eauto.
        { rewrite 2!PTree.gso; try lia.
          rewrite PTree.gss; reflexivity. }
        { rewrite PTree.gso; try lia.
          rewrite PTree.gss; reflexivity. }

    (* Itailcall *)
    + unfold RTLgen.bind in Htransf'; simpl in Htransf'.
      repeat egen_case.
      unfold update_instr in *.
      repeat lr_case.
      simpl in *.
      apply maj_vote_regs_maj_vote_regsR in H.
      2: { clear Hiter; inv s0; unfold Ple in *; lia. }
      repeat state_incr_inv.
      simpl in *; unfold Ple in *.
      econstructor; eauto.
      * repeat apply maj_vote_regsR_ptree_set; eauto.
      * rewrite PTree.gss; reflexivity.

    (* Ibuiltin *)
    + unfold RTLgen.bind in Htransf'; simpl in Htransf'.
      destruct (reg_of_builtin_res b) eqn:Hb.
      * repeat egen_case.
        unfold update_instr in H2.
        repeat lr_case; simpl.
        destruct b; simpl in Hb; inv Hb.
        destruct (rm # r) eqn:Hr.
        eapply match_Ibuiltin_2.
        { eapply maj_vote_regsR_ptree_set; auto.
          eapply state_incr_maj_vote_regsR.
          2: { eapply maj_vote_regs_maj_vote_regsR.
               2: { eauto. }
               clear Hiter; inv s0; unfold Ple in *; lia. }
          intros; clear H0; inv s4; inv s5.
          specialize (H2 pc); specialize (H5 pc).
          destruct H2 as [H2 | H2]; auto. }
        2: { eauto. }
        rewrite PTree.gss; reflexivity.
        apply smoveR_ptree_set; auto.
        eapply copy_to_shadows_smoveR; eauto.
        simpl; lia.
      * repeat egen_case.
        unfold update_instr in H0.
        repeat lr_case; simpl.
        eapply match_Ibuiltin_1.
        { intro HC; inv HC; inv Hb. }
        { eapply maj_vote_regsR_ptree_set; auto.
          eapply state_incr_maj_vote_regsR.
          2: { eapply maj_vote_regs_maj_vote_regsR.
               2: { eauto. }
               clear Hiter; inv s0; unfold Ple in *; lia. }
          intros; inv s1; inv s3.
          specialize (H2 pc); specialize (H5 pc).
          destruct H2 as [H2 | H2]; auto. }
        rewrite PTree.gss; reflexivity.

    (* Icond *)
    + unfold RTLgen.bind in Htransf'; simpl in Htransf'.
      repeat egen_case.
      unfold update_instr in *.
      repeat lr_case.
      simpl in *.
      apply maj_vote_regs_maj_vote_regsR in H.
      2: { clear Hiter; inv s0; unfold Ple in *; lia. }
      repeat state_incr_inv.
      simpl in *; unfold Ple in *.
      econstructor; eauto.
      * repeat apply maj_vote_regsR_ptree_set; eauto.
      * rewrite PTree.gss; reflexivity.

    (* Ijumptable *)
    + unfold RTLgen.bind in Htransf'; simpl in Htransf'.
      destruct (rm # r) as [r2 r3] eqn:Hr.
      unfold RTLgen.bind in Htransf'; simpl in Htransf'.
      repeat egen_case.
      unfold update_instr in *.
      repeat lr_case.
      simpl in *.
      eapply maj_vote_maj_voteR in H1; eauto.
      2: { clear Hiter; inv s0; simpl in *; unfold Ple in *; lia. }
      repeat state_incr_inv.
      simpl in *; unfold Ple in *.
      econstructor; eauto.
      * repeat apply maj_voteR_ptree_set; eauto.
      * rewrite PTree.gss; reflexivity.

    (* Ireturn *)
    + destruct o; simpl in *.
      * unfold RTLgen.bind in Htransf'; simpl in Htransf'.
        destruct (rm # r) as [r2 r3] eqn:Hr.
        unfold RTLgen.bind in Htransf'; simpl in Htransf'.
        repeat egen_case.
        unfold update_instr in *.
        repeat lr_case.
        simpl in *.
        eapply maj_vote_maj_voteR in H1; eauto.
        2: { clear Hiter; inv s0; simpl in *; unfold Ple in *; lia. }
        repeat state_incr_inv.
        simpl in *; unfold Ple in *.
        econstructor; eauto.
        { repeat apply maj_voteR_ptree_set; eauto. }
        { rewrite PTree.gss; reflexivity. }
      * unfold RTLgen.bind in Htransf'; simpl in Htransf'.
        repeat egen_case.
        unfold update_instr in *.
        repeat lr_case; simpl.
        econstructor.
        rewrite PTree.gss; reflexivity.

  - unfold RTLgen.bind in Htransf'.
    destruct u, u0.
    assert (H: match_instr re rm (st_code s'0) p i).
    { eapply IHl; eauto. }
    eapply state_incr_match_instr; eauto.
Qed.

Lemma transf_code_code_matches (c : code) (re : regenv) rm s s' pf u :
  (forall p i, c ! p = Some i -> p < st_nextnode s) ->
  transf_code re rm c s = RTLgen.OK u s' pf ->
  match_code re rm c s'.(st_code).
Proof.
  intros Hlt Hc p i Hi.
  eapply iterM_match_instr; eauto.
  apply PTree.elements_correct; auto.
Qed.

Lemma bind_inversion :
  forall (A B: Type) (f: mon A) (g: A -> mon B) (y: B) s0 s2 pf,
    RTLgen.bind f g s0 = RTLgen.OK y s2 pf ->
  exists x s1 pf0 pf1, f s0 = RTLgen.OK x s1 pf0 /\ g x s1 = RTLgen.OK y s2 pf1.
Proof.
  intros A B f g u s s' pf Heq.
  unfold RTLgen.bind in Heq.
  destruct (f s) eqn:Hf; inv Heq.
  destruct (g a s'0) eqn:Hg; inv H0.
  eexists; eexists; eexists; eexists; split; eauto.
Qed.

Lemma transf_fun_code_matches
  rm uregs (f : function) (re : regenv) entrypoint s s1 s' s2 pf pf1 pf2 :
  transf_fun re f s = RTLgen.OK entrypoint s' pf ->
  replication_map f s = RTLgen.OK rm s1 pf1 ->
  uregs_function f s1 = RTLgen.OK uregs s2 pf2 ->
  (forall p i, (fn_code f) ! p = Some i -> p < st_nextnode s) ->
  match_code re rm f.(fn_code) s'.(st_code).
Proof.
  intros Hf Hrm Huregs Hlt.
  unfold transf_fun in Hf.
  apply bind_inversion in Hf.
  destruct Hf as (rm' & ?s & pf0 & pf1' & Hrm' & Hf).
  rewrite Hrm' in Hrm; inv Hrm; clear Hrm' pf0.
  apply bind_inversion in Hf.
  destruct Hf as (uregs' & ?s & pf0 & pf2' & Huregs' & Hf).
  rewrite Huregs' in Huregs; inv Huregs; clear Huregs' pf0.
  apply bind_inversion in Hf.
  destruct Hf as (?n & ?s & ?pf & ?pf & _ & Hf).
  apply bind_inversion in Hf.
  destruct Hf as ([] & ?s & ?pf & ?pf & Hf & Hret).
  inv Hret.
  apply transf_code_code_matches in Hf; auto. clear Hf.
  intros p i Hpi. specialize (Hlt _ _ Hpi).
  repeat lazymatch goal with H : state_incr _ _ |- _ => inv H end.
  unfold Ple in *. lia.
Qed.

Lemma lt_ptree_fold_max c p i :
  c ! p = Some i ->
  p < PTree.fold (fun m pc (_ : instruction) => Pos.max m pc) c 1 + 1.
Proof.
  revert p i.
  apply PTree_Properties.fold_ind; intros t Ht p i Htp.
  { specialize (Ht p); congruence. }
  intros Hcp HI p' i' Htp'.
  destruct (peq p p'); subst.
  { lia. }
  assert (H: (PTree.remove p t) ! p' = Some i').
  { rewrite PTree.gro; auto. }
  specialize (HI p' i' H); lia.
Qed.

Lemma lt_nextnode_init_state p i sig params stacksize c entrypoint :
  c ! p = Some i ->
  p < st_nextnode (init_state {| fn_sig := sig
                               ; fn_params := params
                               ; fn_stacksize := stacksize
                               ; fn_code := c
                               ; fn_entrypoint := entrypoint
                              |}).
Proof. intro Hget; eapply lt_ptree_fold_max; eauto. Qed.

Lemma lt_nextnode_init_state' p i f :
  (fn_code f) ! p = Some i ->
  p < st_nextnode (init_state f).
Proof. intro Hget; eapply lt_ptree_fold_max; eauto. Qed.

Lemma transf_fun'_code_matches rm uregs (f tf : function) (re : regenv) s1 s2 pf1 pf2 :
  transf_fun' re f = OK tf ->
  replication_map f (init_state f) = RTLgen.OK rm s1 pf1 ->
  uregs_function f s1 = RTLgen.OK uregs s2 pf2 ->
  match_code re rm f.(fn_code) tf.(fn_code).
Proof.
  unfold transf_fun'.
  destruct (transf_fun re f (init_state f)) eqn:Hf; intros H Hrm Huregs; inv H; simpl.
  eapply transf_fun_code_matches; eauto.
  intros; eapply lt_nextnode_init_state'; eauto.
Qed.

Lemma transf_function_code_matches rm uregs (f tf : function) s1 s2 pf1 pf2 :
  transf_function f = OK tf ->
  replication_map f (init_state f) = RTLgen.OK rm s1 pf1 ->
  uregs_function f s1 = RTLgen.OK uregs s2 pf2 ->
  exists re, match_code re rm f.(fn_code) tf.(fn_code).
Proof.
  intro H; monadInv H.
  exists x; eapply transf_fun'_code_matches; eauto.
Qed.

Lemma copy_allR_monotone re rm c1 c2 params n entrypoint :
  copy_allR re rm c1 params n entrypoint ->
  (forall p i, c1 ! p = Some i -> c2 ! p = Some i) ->
  copy_allR re rm c2 params n entrypoint.
Proof.
  revert n entrypoint; induction params;
    simpl; intros n entrypoint Hmatch Hle; inv Hmatch.
  { constructor. }
  econstructor; eauto.
  inv H5; econstructor; eauto.
Qed.

(* TODO: clean up this mess. Might be a good idea to define a
   relational specification of the algorithm and factor this into 1)
   proving the code satisfies the spec and 2) proving the spec implies
   rm_wf.  *)
Lemma replication_map_wf_aux regs (acc rm : replmap) s s' pf :
  Forall (fun r1 : reg => r1 < s.(st_nextreg)) regs ->
  foldM (fun rm (r1 : reg) =>
    do r2 <- new_reg;
    do r3 <- new_reg;
    ret rm # r1 <- (r2, r3)
  ) regs acc s = RTLgen.OK rm s' pf ->
  rm_wf rm regs /\
  Forall (fun r1 : reg =>
    s.(st_nextreg) <= fst (rm # r1) < s'.(st_nextreg) /\
    s.(st_nextreg) <= snd (rm # r1) < s'.(st_nextreg)
  ) regs.
Proof.
  revert acc s rm s' pf.
  induction regs as [|r1 regs IH]; simpl; intros acc s rm s' pf Hall H.
  { split.
    - apply rm_wf_nil.
    - constructor. }
  unfold new_reg in H.
  unfold RTLgen.bind in H.
  simpl in H.
  match goal with
  | [ _: match ?X with | RTLgen.Error _ => _ | RTLgen.OK _ _ _ => _ end = _ |- _ ] => destruct X eqn:HX
  end.
  { inv H. }
  inv H.
  rename t into rm.
  generalize (Forall_inv Hall). intros Hltr. apply Forall_inv_tail in Hall.
  assert (rm_wf rm regs).
  { eapply IH; eauto. }
  assert (
    Hrange : Forall (fun r1 : reg =>
      st_nextreg s <= fst (rm # r1) < st_nextreg s'0 /\
      st_nextreg s <= snd (rm # r1) < st_nextreg s'0
    ) regs
  ).
  { eapply IH; eauto. }
  clear HX IH.
  rewrite Forall_forall in Hrange.
  rewrite Forall_forall in Hall.
  split.
  - inv s0; simpl in *; unfold Ple in *.
    inv pf; simpl in *; unfold Ple in *.
    assert (NoDup_nil_iff : forall A, NoDup (A:=A) [] <-> True).
    { split. easy. constructor. }
    apply rm_wf_cons.
    + assumption.
    + rewrite !NoDup_cons_iff, NoDup_nil_iff. simpl. lia.
    + intros r1' NE Hin.
      specialize (Hall _ Hin).
      specialize (Hrange _ Hin).
      Local Ltac invert_In :=
        repeat match goal with
        | H : In _ _ |- _ => inv H; first [lia | congruence | idtac]
        end.
      constructor; [intros ?; now invert_In|].
      constructor; [intros ?; now invert_In|].
      constructor; [intros ?; now invert_In|].
      eapply rm_wf_nodup_1; eauto.
  - simpl.
    inv s0; simpl in *; unfold Ple in *.
    apply Forall_forall. intros r [->|Hin].
    { rewrite Regmap.gss. simpl. lia. }
    destruct (peq r r1) as [->|?].
    { rewrite Regmap.gss. simpl. lia. }
    rewrite Regmap.gso; [|easy].
    specialize (Hrange _ Hin). lia.
Qed.

Lemma in_elements p s :
  In p (Regset.elements s) <-> Regset.In p s.
Proof.
  split; intro Hin.
  - apply SetoidList.In_InA with (eqA := eq) in Hin.
    2: { apply Eqsth. }
    apply Regset.elements_2; assumption.
  - apply Regset.elements_1 in Hin.
    apply SetoidList.InA_alt in Hin.
    destruct Hin as [? [? Hin]]; subst; assumption.
Qed.

Lemma in_lt_max_reg r s :
  In r (Regset.elements s) ->
  r < max_reg s + 1.
Proof.
  unfold max_reg. simpl.
  intro Hin.
  apply in_elements in Hin.
  destruct (Regset.max_elt s) eqn:Hmax.
  { eapply Regset.max_elt_2 in Hmax; eauto.
    unfold Plt in Hmax; lia. }
  apply Regset.max_elt_3 in Hmax.
  apply Regset.is_empty_1 in Hmax.
  destruct s; simpl in *.
  compute in Hmax.
  destruct this.
  2: { congruence. }
  inv Hin.
Qed.

Lemma replication_map_wf f rm s pf :
  replication_map f (init_state f) = RTLgen.OK rm s pf ->
  rm_wf rm (fun_regs_list f).
Proof.
  intro H; eapply replication_map_wf_aux; eauto.
  apply Forall_forall. intros r.
  apply in_lt_max_reg.
Qed.

Lemma in_regset_of_list p l :
  In p l <-> Regset.In p (Regset_of_list l).
Proof.
  split.
  - revert p; induction l; simpl; intros p Hin; try contradiction.
    destruct Hin as [? | Hin]; subst.
    + apply Regset.add_1; reflexivity.
    + apply Regset.add_2, IHl, Hin.
  - revert p; induction l; simpl; intros p Hin.
    { inv Hin. }
    destruct (peq a p); subst; auto.
    right; apply Regset.add_3 in Hin; auto.
Qed.

Definition rm_inv_list (min : positive) (regs : list reg) (rm : replmap) : Prop :=
  forall r1 : reg,
    In r1 regs ->
    min <= (fst (rm # r1)) /\
    min <= (snd (rm # r1)).

Lemma reg_used_fold_right p i l r :
  In (p, i) l ->
  reg_used_in_instr r i ->
  Regset.In r
    (fold_right (fun (y : positive * instruction) (x : Regset.t) =>
                   Regset.union x (instr_regs (snd y))) Regset.empty
       l).
Proof.
  revert p i r.
  induction l; simpl; intros p i r Hin Hused; try contradiction.
  destruct Hin as [? | Hin]; subst.
  - inv Hused; simpl; try destruct fn; apply Regset.union_3;
      try solve [apply Regset.union_3, Regset.singleton_2; reflexivity];
      try solve [apply Regset.union_2, in_regset_of_list; auto];
      try solve [apply in_regset_of_list; assumption];
      try solve [apply Regset.singleton_2; reflexivity].
    + apply Regset.union_2, Regset.add_1; reflexivity.
    + apply Regset.union_2, Regset.add_2, in_regset_of_list; assumption.
    + apply Regset.add_1; reflexivity.
    + apply Regset.add_2, in_regset_of_list; assumption.
  - inv Hused; simpl;
      solve [apply Regset.union_2; eapply IHl; eauto; constructor; auto].
Qed.

Lemma reg_used_regset_in_all_regs params c r :
  reg_used params c r ->
  Regset.In r (all_regs params c).
Proof.
  intros [Hin | (p & i & Hget & Hused)].
  - apply Regset.union_2, in_regset_of_list; auto.
  - apply Regset.union_3.
    apply PTree.elements_correct in Hget.
    unfold code_regs.
    rewrite PTree.fold_spec.
    rewrite <- fold_left_rev_right.
    apply in_rev in Hget.
    eapply reg_used_fold_right; eauto.
Qed.

Lemma reg_used_in_all_regs_list params c r :
  reg_used params c r -> In r (all_regs_list params c).
Proof.
  intro Hused.
  apply in_elements.
  apply reg_used_regset_in_all_regs; auto.
Qed.
#[global] Hint Resolve reg_used_in_all_regs_list : rm_wf.

(**
TODO: If these are equivalent, consider either proving both directions
or eliminating one of them. If they are not equivalent, document why.
*)
Lemma reg_used_in_code_regset_in_code_regs c r :
  reg_used_in_code c r ->
  Regset.In r (code_regs c).
Proof.
  intros (p & i & Hget & Hused).
  apply PTree.elements_correct in Hget.
  unfold code_regs.
  rewrite PTree.fold_spec.
  rewrite <- fold_left_rev_right.
  apply in_rev in Hget.
  eapply reg_used_fold_right; eauto.
Qed.
Lemma reg_used_in_code_max_reg params c r :
  reg_used_in_code c r ->
  r < max_reg (all_regs params c) + 1.
Proof.
  intros. apply in_lt_max_reg, in_elements, Regset.union_3.
  apply reg_used_in_code_regset_in_code_regs; auto.
Qed.

Lemma reg_used_max_reg params c r :
  reg_used params c r ->
  r < max_reg (all_regs params c) + 1.
Proof.
  destruct 1.
  { apply in_lt_max_reg, in_elements, Regset.union_2, in_regset_of_list; auto. }
  { apply reg_used_in_code_max_reg; auto. }
Qed.

Lemma rm_inv_list_rm_inv params c rm :
  rm_inv_list (max_reg (all_regs params c) + 1) (all_regs_list params c) rm ->
  rm_inv (reg_used params c) rm.
Proof.
  intros Hrm. split; auto.
  all: intros r1 ?%reg_used_in_all_regs_list%Hrm ?%reg_used_max_reg.
  all: lia.
Qed.

Lemma foldM_rm_inv_list regs s s' pf (rm0 rm : replmap) :
  Forall (fun r : reg => r < s.(st_nextreg)) regs ->
  foldM (fun rm1 (r1 : reg) =>
    do r2 <- new_reg;
    do r3 <- new_reg;
    ret rm1 # r1 <- (r2, r3)
  ) regs rm0 s = RTLgen.OK rm s' pf ->
  rm_inv_list s.(st_nextreg) regs rm.
Proof.
  revert pf.
  revert s s' rm0 rm.
  induction regs as [|r regs IH]; simpl; intros s s' rm0 rm pf Hlt Hfold.
  { intros ? []. }
  inv Hlt.
  unfold RTLgen.bind in Hfold.
  repeat egen_case.
  rename H into Hinv.
  eapply IH in Hinv; auto. clear IH.
  inv H3; inv H5; inv H0.
  repeat state_incr_inv.
  unfold Ple in *; simpl in *.
  intros x1 Hin.
  destruct (peq r x1) as [->|?].
  { rewrite Regmap.gss. simpl. lia. }
  rewrite Regmap.gso; [|easy].
  destruct Hin as [?|Hin]; [contradiction|].
  specialize (Hinv _ Hin). lia.
Qed.

Lemma replication_map_rm_inv' sig params stacksize c entrypoint s pf rm :
  replication_map
    {|
      fn_sig := sig;
      fn_params := params;
      fn_stacksize := stacksize;
      fn_code := c;
      fn_entrypoint := entrypoint
    |}
    (init_state
       {|
         fn_sig := sig;
         fn_params := params;
         fn_stacksize := stacksize;
         fn_code := c;
         fn_entrypoint := entrypoint
       |}) = RTLgen.OK rm s pf ->
  rm_inv (reg_used params c) rm.
Proof.
  unfold replication_map.
  intro Hfold.
  apply rm_inv_list_rm_inv.
  set (s0 := init_state
         {|
           fn_sig := sig;
           fn_params := params;
           fn_stacksize := stacksize;
           fn_code := c;
           fn_entrypoint := entrypoint
         |}).
  assert (Hnextreg: s0.(st_nextreg) = max_reg (all_regs params c) + 1).
  { reflexivity. }
  rewrite <- Hnextreg.
  eapply foldM_rm_inv_list; eauto.
  apply Forall_forall; intros x Hin.
  apply in_elements in Hin.
  rewrite Hnextreg.
  unfold all_regs_list.
  apply in_lt_max_reg.
  apply in_elements; auto.
Qed.

(**
Everything we need to know about the dataflow analysis.
*)
Definition uregs_function_spec : Prop :=
  forall f uregs s s' pf,
  uregs_function f s = RTLgen.OK uregs s' pf ->
  uregs_ok f.(fn_code) f.(fn_params) uregs.

Module Type UREGS.
  Parameter uregs_function_ok : uregs_function_spec.
End UREGS.

Module URegs <: UREGS.

  Definition Forall {A} (P : A -> Prop) (m : PMap.t A) : Prop :=
    forall pc, P (m!!pc).

  Lemma reg_list_defined_mono r rs D :
    Regiset.In r D -> Regiset.In r (reg_list_defined rs D).
  Proof.
    revert D. induction rs; intros; simpl; auto.
    apply IHrs. rewrite Regiset.add_spec. now right.
  Qed.

  (** ** Proof of [uregs_ok_params] *)

  (**
  A function's parameters are included in the intermediate set <<D>>
  of registers that are well-defined.
  *)
  Definition included (params : list reg) (D : Regiset.t) : Prop :=
    forall r, In r params -> Regiset.In r D.

  Lemma included_invariant f def :
    analyze f = Some def ->
    Forall (included f.(fn_params)) def.
  Proof.
    intros Hf pc. revert Hf.
    apply DS.fixpoint_invariant; unfold included.
    { intros r _. unfold DS.L.bot. apply Regiset.top_spec. }
    { intros. unfold DS.L.lub. rewrite Regiset.inter_spec. auto. }
    { intros ?pc i ?D Hi Hinv ?r Hr. unfold transfer. rewrite Hi.
      destruct (instr_defs i) as [?r|]; auto.
      rewrite Regiset.add_spec. auto. }
    { unfold params_defined. generalize Regiset.empty.
      induction f.(fn_params); simpl; intros D ?r Hr; [easy|].
      destruct Hr; subst; auto.
      apply reg_list_defined_mono. rewrite Regiset.add_spec. now left. }
  Qed.

  (**
  A function's parameters are disjoint from the intermediate set <<U>>
  of registers that may be used before being defined.
  *)

  Definition disjoint (params : list reg) (U : Regset.t) : Prop :=
    forall r, In r params -> ~ Regset.In r U.

  Lemma disjoint_uregs_reg params D U r :
    included params D ->
    disjoint params U ->
    disjoint params (uregs_reg D U r).
  Proof.
    unfold included, disjoint, uregs_reg. intros HP HD.
    destruct (Regiset.mem _  _) eqn:Hr; [now auto|].
    rewrite <-Regiset.not_mem_iff in Hr. intros r' Hr1 Hr2.
    destruct (peq r' r); subst; auto.
    apply (HD _ Hr1). rewrite Regsetaux.Dec.F.add_iff in Hr2.
    destruct Hr2 as [->|?]; [exfalso|]; auto.
  Qed.

  Lemma disjoint_uregs_instr params def U pc i :
    Forall (included params) def ->
    disjoint params U ->
    disjoint params (uregs_instr def U pc i).
  Proof.
    unfold Forall, uregs_instr. intros ?. revert U.
    induction (instr_uses i); simpl; auto using disjoint_uregs_reg.
  Qed.

  Lemma disjoint_uregs_code params def U c :
    Forall (included params) def ->
    disjoint params U ->
    disjoint params (uregs_code def c U).
  Proof.
    unfold uregs_code. rewrite PTree.fold_spec. intros ?. revert U.
    induction (PTree.elements c); simpl; auto using disjoint_uregs_instr.
  Qed.

  Lemma disjoint_empty params : disjoint params Regset.empty.
  Proof. intros r _. apply Regset.empty_1. Qed.

  Lemma disjoint_uregs_function f uregs s s' pf :
    uregs_function f s = RTLgen.OK uregs s' pf ->
    list_disjoint f.(fn_params) uregs.
  Proof.
    unfold uregs_function. intros Hret.
    destruct (analyze f) as [def|] eqn:Hf; [|easy].
    apply included_invariant in Hf. inv Hret.
    intros r r' Hp Hu <-.
    rewrite Regsetaux.in_elements in Hu.
    eapply disjoint_uregs_code; eauto using disjoint_empty.
  Qed.
  Local Hint Resolve disjoint_uregs_function : core.

  (** ** Proof of [uregs_ok_code] *)

  Section used.
    Context (c : code).
    Notation used := (reg_used_in_code c).

    Lemma used_uregs_reg D U r :
      Regset.For_all used U ->
      used r ->
      Regset.For_all used (uregs_reg D U r).
    Proof.
      intros HU Hr. unfold uregs_reg.
      destruct (Regiset.mem _ _); auto. intros r' Hr'.
      destruct (peq r' r); subst; auto.
      eapply Regset.add_3 in Hr'; auto.
    Qed.

    Lemma used_uregs_instr def U pc i :
      c ! pc = Some i ->
      Regset.For_all used U ->
      Regset.For_all used (uregs_instr def U pc i).
    Proof.
      intros Hi%instr_uses_reg_used_in_code.
      unfold uregs_instr. revert U.
      induction (instr_uses i); simpl; intros U HU; auto.
      generalize (Forall_inv Hi). intros Hr.
      apply Forall_inv_tail in Hi. auto using used_uregs_reg.
    Qed.

    Lemma used_uregs_code def U :
      Regset.For_all used U ->
      Regset.For_all used (uregs_code def c U).
    Proof.
      unfold uregs_code. rewrite PTree.fold_spec. revert U.
      generalize (PTree.elements_complete c). intros Hget.
      induction (PTree.elements c) as [|[] ??]; simpl in *;
        auto using used_uregs_instr.
    Qed.

    Lemma used_empty : Regset.For_all used Regset.empty.
    Proof. now intros r ?%Regset.empty_1. Qed.
  End used.

  Lemma used_uregs_function f uregs s s' pf :
    uregs_function f s = RTLgen.OK uregs s' pf ->
    forall r, In r uregs -> reg_used_in_code f.(fn_code) r.
  Proof.
    unfold uregs_function. intros Hret.
    destruct (analyze f) as [def|]; [|easy].
    inv Hret. intros r Hr.
    rewrite Regsetaux.in_elements in Hr.
    eapply used_uregs_code; eauto using used_empty.
  Qed.
  Local Hint Resolve used_uregs_function : core.

  (** ** Proof of [uregs_ok_nodup] *)

  Lemma uregs_function_nodup f uregs s s' pf :
    uregs_function f s = RTLgen.OK uregs s' pf ->
    NoDup uregs.
  Proof.
    unfold uregs_function. intros H. destruct (analyze f); [|easy].
    inv H. apply Regsetaux.elements_NoDup.
  Qed.
  Local Hint Resolve uregs_function_nodup : core.

  Lemma uregs_function_ok : uregs_function_spec.
  Proof. repeat intro. repeat split; eauto. Qed.
End URegs.

Lemma transf_function_match_fundef (f tf : fundef) :
  transf_fundef f = OK tf ->
  match_fundef f tf.
Proof.
  intro Htransf.
  destruct f; simpl in Htransf.
  - monadInv Htransf.
    monadInv EQ.
    rename x0 into re.
    unfold transf_fun' in EQ1.
    egen_case; try congruence.
    inv EQ1.
    unfold transf_fun in H.
    unfold RTLgen.bind in H.
    repeat egen_case.
    lazymatch goal with
    | H : transf_code _ _ _ _ = RTLgen.OK _ _ _ |- _ =>
      apply transf_code_code_matches in H
    end.
    2:{
      intros p i Hpi.
      apply lt_nextnode_init_state' in Hpi.
      repeat lazymatch goal with
      | H : _ = RTLgen.OK _ _ _ |- _ => clear H
      end.
      repeat state_incr_inv.
      unfold Ple in *. simpl in *. lia. }
    lazymatch goal with
    | H : uregs_function _ _ = RTLgen.OK _ _ _ |- _ =>
      apply URegs.uregs_function_ok in H
    end.
    lazymatch goal with
    | H : ret _ _ = RTLgen.OK _ _ _ |- _ => inv H
    end.
    destruct f.
    simpl in *.
    econstructor.
    { apply type_function_correct; eauto. }
    econstructor; eauto.
    { eapply rm_wf_mono.
      2:{ eapply replication_map_wf; eauto. }
      auto. }
    { eapply replication_map_rm_inv'; eauto. }
    eapply copy_allR_monotone.
    { eapply copy_all_to_shadows_copy_allR; eauto. }
    repeat lazymatch goal with
    | H : _ = RTLgen.OK _ _ _ |- _ => clear H
    | H : match_code _ _ _ _ |- _ => clear H
    end.
    repeat state_incr_inv.
    unfold Ple in *.
    simpl in *.
    intros p i Hpi.
    destruct (H2 p); congruence.
  - inv Htransf; constructor.
Qed.

Inductive in_builtin_arg {A : Type} (a : A) : builtin_arg A -> Prop :=
| in_builtin_arg_BA : in_builtin_arg a (BA a)
| in_builtin_arg_splitlong_hi : forall hi lo,
    in_builtin_arg a hi ->
    in_builtin_arg a (BA_splitlong hi lo)
| in_builtin_arg_splitlong_lo : forall hi lo,
    in_builtin_arg a lo ->
    in_builtin_arg a (BA_splitlong hi lo)
| in_builtin_arg_addptr_a1 : forall a1 a2,
    in_builtin_arg a a1 ->
    in_builtin_arg a (BA_addptr a1 a2)
| in_builtin_arg_addptr_a2 : forall a1 a2,
    in_builtin_arg a a2 ->
    in_builtin_arg a (BA_addptr a1 a2).

Lemma in_regs_of_builtin_arg_in_builtin_arg r barg :
  In r (regs_of_builtin_arg barg) <-> in_builtin_arg r barg.
Proof.
  split.
  - induction barg; simpl; intro Hin; try contradiction;
      try (destruct Hin; subst; try contradiction; constructor);
      apply in_app_or in Hin; destruct Hin as [Hin | Hin];
      solve [constructor; auto].
  - induction barg; simpl; intro Hin; inv Hin; auto; apply in_or_app; auto.
Qed.

Lemma in_regs_of_builtin_args_exists_in_builtin_arg r bargs :
  In r (regs_of_builtin_args bargs) <-> Exists (in_builtin_arg r) bargs.
Proof.
  split.
  - induction bargs; simpl; intro Hin; try contradiction.
    apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + constructor; apply in_regs_of_builtin_arg_in_builtin_arg; auto.
    + right; auto.
  - induction bargs; simpl; intro Hin; inv Hin.
    + apply in_or_app; left.
      apply in_regs_of_builtin_arg_in_builtin_arg; auto.
    + apply in_or_app; right; auto.
Qed.
