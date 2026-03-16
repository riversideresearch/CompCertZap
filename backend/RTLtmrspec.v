(** * Relational specificaton of the TMR transformation. *)

Require Import
  AST
  Builtins
  FaultPolicy
  Coqlib
  Errors
  Globalenvs
  Integers
  Linking
  Maps
  Memory
  Op
  Registers
  RTLgen
  RTLtyping
  Smallstep
  Values
.
Require Import CompCertZapUtils RTL.
Require Import RTLtmr.
Require Export RTLreplicateSpecCommon.
Require Import Errors.
Import ListNotations.

Local Open Scope positive_scope.

Definition rm_wf (rm : PMap.t (reg * reg)) (l : list positive) : Prop :=
  forall r1 r2 r3,
    In r1 l ->
    PMap.get r1 rm = (r2, r3) ->
    NoDup [r1; r2; r3] /\
      forall r1' r2' r3',
        In r1' l ->
        r1 <> r1' ->
        PMap.get r1' rm = (r2', r3') ->
        NoDup [r1; r2; r3; r1'; r2'; r3'].

Inductive rm_l (rm : PMap.t (reg * reg))
  : list reg -> list reg -> list reg -> Prop :=
| match_nil : rm_l rm [] [] []
| match_cons : forall r1 r2 r3 rs1 rs2 rs3,
    rm !! r1 = (r2, r3) ->
    rm_l rm rs1 rs2 rs3 ->
    rm_l rm (r1 :: rs1) (r2 :: rs2) (r3 :: rs3).

Inductive rm_builtin_arg (rm : PMap.t (reg * reg))
  : builtin_arg reg -> builtin_arg reg -> builtin_arg reg -> Prop :=
| rm_BA : forall r1 r2 r3,
    rm !! r1 = (r2, r3) ->
    rm_builtin_arg rm (BA r1) (BA r2) (BA r3)
| rm_BA_int : forall n,
    rm_builtin_arg rm (BA_int n) (BA_int n) (BA_int n)
| rm_BA_long : forall n,
    rm_builtin_arg rm (BA_long n) (BA_long n) (BA_long n)
| rm_BA_float : forall n,
    rm_builtin_arg rm (BA_float n) (BA_float n) (BA_float n)
| rm_BA_single : forall n,
    rm_builtin_arg rm (BA_single n) (BA_single n) (BA_single n)
| rm_BA_loadstack : forall chunk ofs,
    rm_builtin_arg rm (BA_loadstack chunk ofs) (BA_loadstack chunk ofs) (BA_loadstack chunk ofs)
| rm_BA_addrstack : forall ofs,
    rm_builtin_arg rm (BA_addrstack ofs) (BA_addrstack ofs) (BA_addrstack ofs)
| rm_BA_loadglobal : forall chunk id ofs,
    rm_builtin_arg rm (BA_loadglobal chunk id ofs) (BA_loadglobal chunk id ofs) (BA_loadglobal chunk id ofs)
| rm_BA_addrglobal : forall id ofs,
    rm_builtin_arg rm (BA_addrglobal id ofs) (BA_addrglobal id ofs) (BA_addrglobal id ofs)
| rm_BA_splitlong : forall hi1 hi2 hi3 lo1 lo2 lo3,
    rm_builtin_arg rm hi1 hi2 hi3 ->
    rm_builtin_arg rm lo1 lo2 lo3 ->
    rm_builtin_arg rm (BA_splitlong hi1 lo1) (BA_splitlong hi2 lo2) (BA_splitlong hi3 lo3)
| rm_BA_addptr : forall a1 a2 a3 b1 b2 b3,
    rm_builtin_arg rm a1 a2 a3 ->
    rm_builtin_arg rm b1 b2 b3 ->
    rm_builtin_arg rm (BA_addptr a1 b1) (BA_addptr a2 b2) (BA_addptr a3 b3).

Inductive rm_builtin_args (rm : PMap.t (reg * reg))
  : list (builtin_arg reg) -> list (builtin_arg reg) -> list (builtin_arg reg) -> Prop :=
| rm_bargs_nil : rm_builtin_args rm nil nil nil
| rm_bargs_cons : forall ba1 ba2 ba3 bas1 bas2 bas3,
    rm_builtin_arg rm ba1 ba2 ba3 ->
    rm_builtin_args rm bas1 bas2 bas3 ->
    rm_builtin_args rm (ba1 :: bas1) (ba2 :: bas2) (ba3 :: bas3).

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
    green_smove ty src dst1 = Some mov1 ->
    blue_smove ty src dst2 = Some mov2 ->
    c ! pc = Some (mov1 n) ->
    c ! n = Some (mov2 succ) ->
    smoveR c ty src dst1 dst2 pc succ.

Ltac smoveR_inv :=
  try match goal with
  | [H: smoveR _ _ _ _ _ _ _ |- _ ] => inv H
  end.

Inductive copy_allR re rm c : list reg -> node -> node -> Prop :=
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
  (rm : Regmap.t (reg * reg)) (ty : typ) (r1 r2 r3 : reg) (pc succ : node)
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
  destruct (green_smove ty r1 r2) eqn:Hmov1; gen_contra.
  destruct (blue_smove ty r1 r3) eqn:Hmov2; gen_contra.
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

(** [match_instr re rm c pc i] means that the translated code [c]
    contains instructions starting at pc] that correspond to
    instruction [i] in the original program, wrt. register environment
    [regenv] and replication map [rm]. *)
Inductive match_instr
  (re : regenv) (rm : PMap.t (reg * reg)) (c : code) (pc : positive)
  : instruction -> Prop :=
| match_Inop :
  forall n,
    c ! pc = Some (Inop n) ->
    match_instr re rm c pc (Inop n)
| match_Iop_safe :
  forall op args1 args2 args3 res1 res2 res3 n1 n2 succ
    (NPROT: ~ is_protected op)
    (ARGS : rm_l rm args1 args2 args3)
    (RM_RES : rm !! res1 = (res2, res3))
    (PC : c ! pc = Some (Iop op args2 res2 n1))
    (N1 : c ! n1 = Some (Iop op args3 res3 n2))
    (N2 : c ! n2 = Some (Iop op args1 res1 succ)),
    match_instr re rm c pc (Iop op args1 res1 succ)
| match_Iop_protected :
  forall op args res1 res2 res3 n1 n2 succ
    (PROT: is_protected op)
    (VOTE_ARGS : maj_vote_regsR c re rm (dedup args) pc n1)
    (N1 : c ! n1 = Some (Iop op args res1 n2))
    (RM_RES : rm !! res1 = (res2, res3))
    (MOVE : smoveR c (re res1) res1 res2 res3 n2 succ),
    match_instr re rm c pc (Iop op args res1 succ)
| match_Iload :
  forall chunk addr args res1 res2 res3 n1 n2 succ
    (VOTE_ARGS : maj_vote_regsR c re rm (dedup args) pc n1)
    (N1 : c ! n1 = Some (Iload chunk addr args res1 n2))
    (RM_RES : rm !! res1 = (res2, res3))
    (MOVE : smoveR c (re res1) res1 res2 res3 n2 succ),
  match_instr re rm c pc (Iload chunk addr args res1 succ)
| match_Istore :
  forall chunk addr args src1 src2 src3 n succ
    (RM_SRC : rm !! src1 = (src2, src3))
    (VOTE_REGS : maj_vote_regsR c re rm (dedup (src1 :: args)) pc n)
    (N : c ! n = Some (Istore chunk addr args src1 succ)),
    match_instr re rm c pc (Istore chunk addr args src1 succ)
| match_Icall :
  forall sig fn args res1 res2 res3 succ n1 n2
    (VOTE_ARGS : maj_vote_regsR c re rm (dedup (regs_of_fn fn ++ args)) pc n1)
    (N1 : c ! n1 = Some (Icall sig fn args res1 n2))
    (RM_RES : rm !! res1 = (res2, res3))
    (MOVE : smoveR c (re res1) res1 res2 res3 n2 succ),
    match_instr re rm c pc (Icall sig fn args res1 succ)
| match_Itailcall :
  forall sig fn args n
    (VOTE_ARGS : maj_vote_regsR c re rm (dedup (regs_of_fn fn ++ args)) pc n)
    (N : c ! n = Some (Itailcall sig fn args)),
    match_instr re rm c pc (Itailcall sig fn args)
| match_Ibuiltin_safe :
  forall ef bargs1 bargs2 bargs3 res1 res2 res3 n1 n2 succ
    (CAN_REP : builtin_can_replicate ef = true)
    (BARGS : rm_builtin_args rm bargs1 bargs2 bargs3)
    (RM_RES : rm !! res1 = (res2, res3))
    (PC : c ! pc = Some (Ibuiltin ef bargs2 (BR res2) n1))
    (N1 : c ! n1 = Some (Ibuiltin ef bargs3 (BR res3) n2))
    (N2 : c ! n2 = Some (Ibuiltin ef bargs1 (BR res1) succ)),
    match_instr re rm c pc (Ibuiltin ef bargs1 (BR res1) succ)
| match_Ibuiltin_1 :
  forall ef bargs bres n succ
    (NORES : ~ is_BR bres) (* no result register *)
    (VOTE_ARGS : maj_vote_regsR c re rm (dedup (regs_of_builtin_args bargs)) pc n)
    (N : c ! n = Some (Ibuiltin ef bargs bres succ)),
    match_instr re rm c pc (Ibuiltin ef bargs bres succ)
| match_Ibuiltin_2 :
  forall ef bargs res1 res2 res3 n1 n2 succ
    (NOT_SAFE : builtin_can_replicate ef = false)
    (VOTE_ARGS : maj_vote_regsR c re rm (dedup (regs_of_builtin_args bargs)) pc n1)
    (N1 : c ! n1 = Some (Ibuiltin ef bargs (BR res1) n2))
    (RM_RES : rm # res1 = (res2, res3))
    (MOVE : smoveR c (re res1) res1 res2 res3 n2 succ),
    match_instr re rm c pc (Ibuiltin ef bargs (BR res1) succ)
| match_Icond :
  forall cond args ifso ifnot n
    (VOTE_ARGS : maj_vote_regsR c re rm (dedup args) pc n)
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
Definition match_code (re : regenv) (rm : PMap.t (reg * reg)) (c c': code) : Prop :=
  forall pc i, c ! pc = Some i -> match_instr re rm c' pc i.

(** Replication map invariant. Asserts that shadow registers in the
    translated function do not appear in the parameters or code of the
    original function. *)
Definition rm_inv
  (params : list reg) (c : code) (rm : PMap.t (reg * reg)) : Prop :=
  forall (r1 r2 r3 : reg),
    rm # r1 = (r2, r3) ->
    reg_used params c r1 ->
    ~ In r2 params /\
      ~ In r3 params /\
      ~ reg_used_in_code c r2 /\
      ~ reg_used_in_code c r3.

Lemma reg_used_cons p params c r :
  reg_used params c r ->
  reg_used (p :: params) c r.
Proof.
  intros [Hin | Hused].
  - left; right; auto.
  - right; auto.
Qed.

Lemma rm_inv_cons p params c rm :
  rm_inv (p :: params) c rm ->
  rm_inv params c rm.
Proof.
  unfold rm_inv.
  intros Hrm r1 r2 r3 Hr1 Hused.
  specialize (Hrm r1 r2 r3 Hr1 (reg_used_cons _ _ _ _ Hused)).
  firstorder.
Qed.

Inductive match_function re rm : function -> function -> Prop :=
| match_fun :
  forall sig params stacksize c c' entrypoint entrypoint' copy_regs
    (RM_WF: rm_wf rm (all_regs_list params c))
    (RM_INV: rm_inv params c rm)
    (CODE: match_code re rm c c')
    (COPY_REGS_OK: Forall (fun x => In x (all_regs_list params c)) copy_regs)
    (* (COPY: copy_allR re rm c' (copy_regs ++ params) entrypoint' entrypoint), *)
    (COPY: copy_allR re rm c' (app' copy_regs params) entrypoint' entrypoint),
    match_function re rm
      ({| fn_sig := sig
        ; fn_params := params
        ; fn_stacksize := stacksize
        ; fn_code := c
        ; fn_entrypoint := entrypoint
       |})
      ({| fn_sig := sig
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

Lemma rm_builtin_arg_map rm (ba : builtin_arg reg) :
  rm_builtin_arg rm ba
    (map_builtin_arg (fun r => fst (rm # r)) ba)
    (map_builtin_arg (fun r => snd (rm # r)) ba).
Proof.
  induction ba; simpl; try constructor; auto.
  destruct (rm # x); constructor; reflexivity.
Qed.

Lemma rm_builtin_args_map rm (bas : list (builtin_arg reg)) :
  rm_builtin_args rm bas
    (List.map (map_builtin_arg (fun r => fst (rm # r))) bas)
    (List.map (map_builtin_arg (fun r => snd (rm # r))) bas).
Proof.
  induction bas; constructor; auto.
  apply rm_builtin_arg_map.
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
    eapply match_Iop_safe; eauto.
    + rewrite Hs'; eauto.
    + rewrite Hs'1; eauto.
    + rewrite Hs'2; eauto.
  - inv MOVE.
    destruct (H1 n) as [?|Hn]; try congruence.
    destruct (H1 n1) as [?|Hn1]; try congruence.
    destruct (H1 n2) as [?|Hn2]; try congruence.
    eapply match_Iop_protected; eauto.
    + eapply state_incr_maj_vote_regsR; eauto.
    + rewrite Hn1; eauto.
    + econstructor; eauto.
      * rewrite Hn2; eauto.
      * rewrite Hn; auto.
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
  - (* match_Ibuiltin_safe *)
    destruct (H1 p) as [?|Hs']; try congruence.
    destruct (H1 n1) as [?|Hs'1]; try congruence.
    destruct (H1 n2) as [?|Hs'2]; try congruence.
    eapply match_Ibuiltin_safe; eauto.
    + rewrite Hs'; eauto.
    + rewrite Hs'1; eauto.
    + rewrite Hs'2; eauto.
  - eapply match_Ibuiltin_1; auto.
    + eapply state_incr_maj_vote_regsR; eauto.
    + destruct (H1 n); congruence.
  - destruct (H1 n1) as [?|Hn1]; try congruence.
    eapply match_Ibuiltin_2.
    + auto.
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

Lemma transf_instr_match_instr re rm p i u s s' pf :
  transf_instr re rm (p, i) s = RTLgen.OK u s' pf ->
  p < st_nextnode s ->
  match_instr re rm (st_code s') p i.
Proof.
  intros Htransf Hlt.
  simpl in Htransf.
  destruct i.

  (* Inop *)
  - unfold update_instr in Htransf.
    repeat lr_case.
    simpl; constructor; rewrite PTree.gss; reflexivity.

  (* Iop *)
  - destruct (is_protectedb o) eqn:Hprotected.
    { unfold RTLgen.bind in Htransf; simpl in Htransf.
      repeat egen_case.
      unfold update_instr in H2.
      repeat lr_case; simpl.
      destruct (rm # r) eqn:Hr.
      eapply copy_to_shadows_smoveR in H0; eauto.
      2: { simpl; lia. }
      eapply match_Iop_protected with (n1:=n0); eauto.
      destruct (is_protectedb_spec o); congruence.
      3: { apply smoveR_ptree_set; eauto. }
      2: { rewrite PTree.gss; auto. }
      eapply maj_vote_regsR_ptree_set; auto.
      eapply state_incr_maj_vote_regsR.
      2: { eapply maj_vote_regs_maj_vote_regsR.
           2: { eauto. }
           auto. }
      intro pc; inv s3; auto. }
    unfold RTLgen.bind in Htransf.
    repeat egen_case.
    unfold update_instr in *.
    repeat lr_case.
    inv H; inv H1.
    destruct (rm # r) eqn:Hrmr; simpl in *.
    (* assert (p < st_nextnode s). auto. *)
    (* { inv s1; simpl in *; unfold Ple in *; lia. } *)
    eapply match_Iop_safe with (pc := p)
                               (n1 := s.(st_nextnode))
                               (n2 := Pos.succ (s.(st_nextnode))); eauto.
    { intro HC; destruct (is_protectedb_spec o); auto; congruence. }
    { apply rm_l_map_rm. }
    + rewrite 2!PTree.gso; try lia.
      rewrite PTree.gss; reflexivity.
    + rewrite PTree.gso; try lia.
      rewrite PTree.gss; reflexivity.
    + rewrite PTree.gss; reflexivity.

  (* Iload *)
  - unfold RTLgen.bind in Htransf; simpl in Htransf.
    repeat egen_case.
    unfold update_instr in H2.
    repeat lr_case; simpl.
    destruct (rm # r) eqn:Hr.
    eapply copy_to_shadows_smoveR in H0; eauto.
    2: { simpl; lia. }
    eapply match_Iload with (n1:=n0); eauto.
    3: { apply smoveR_ptree_set; eauto. }
    2: { rewrite PTree.gss; auto. }
    eapply maj_vote_regsR_ptree_set; auto.
    eapply state_incr_maj_vote_regsR.
    2: { eapply maj_vote_regs_maj_vote_regsR.
         2: { eauto. }
         auto. }
    intro pc; inv s3; auto.

  (* Istore *)
  - unfold RTLgen.bind in Htransf.
    simpl in Htransf.
    gen_case Hmaj.
    gen_case Hupd.
    replace ((do succ <- maj_vote_regs re rm l p;
                 let (r2, r3) := rm # r in maj_vote re r r2 r3 succ) s)
      with (maj_vote_regs re rm (r :: l) p s) in Hmaj by auto.
    apply maj_vote_regs_maj_vote_regsR in Hmaj; auto.
    (* 2: { clear Hiter; inv s0; unfold Ple in *; lia. } *)
    unfold update_instr in Hupd.
    repeat lr_case.
    simpl in *.
    inv s1; inv pf; simpl in *; unfold Ple in *.
    destruct (rm # r) eqn:Hrmr; simpl in *.
    econstructor.
    { eauto. }
    2: { rewrite PTree.gss; reflexivity. }
    apply maj_vote_regsR_ptree_set; auto.

  (* Icall *)
  - simpl in Htransf; unfold RTLgen.bind in Htransf; simpl in Htransf.
    repeat egen_case.
    unfold copy_to_shadows in H0.
    destruct (rm # r) eqn:Hrmr.
    unfold RTLgen.bind in H0.
    unfold error in *.
    destruct (green_smove (re r) r r0) eqn:Hmov1; gen_contra.
    destruct (blue_smove (re r) r r1) eqn:Hmov2; gen_contra.
    repeat egen_case.
    unfold update_instr in *.
    repeat lr_case.
    simpl in *.
    assert (p < st_nextnode s'0).
    { clear H; inv s2; simpl in *; extlia. }
    assert (Hn0: n0 < s'0.(st_nextnode)).
    { eapply maj_vote_regs_succ_lt_nextnode.
      2: { eauto. }
      auto. }
    apply maj_vote_regs_maj_vote_regsR in H; auto.
    reserve_instr_inv.
    simpl in *.
    repeat state_incr_inv.
    simpl in *; unfold Ple in *.
    econstructor; eauto.
    + repeat apply maj_vote_regsR_ptree_set; eauto.
    + rewrite PTree.gss; reflexivity.
    + econstructor; eauto.
      { rewrite 2!PTree.gso; try lia.
        rewrite PTree.gss; reflexivity. }
      { rewrite PTree.gso; try lia.
        rewrite PTree.gss; reflexivity. }

  (* Itailcall *)
  - unfold RTLgen.bind in Htransf; simpl in Htransf.
    repeat egen_case.
    unfold update_instr in *.
    repeat lr_case.
    simpl in *.
    apply maj_vote_regs_maj_vote_regsR in H; auto.
    repeat state_incr_inv.
    simpl in *; unfold Ple in *.
    econstructor; eauto.
    + repeat apply maj_vote_regsR_ptree_set; eauto.
    + rewrite PTree.gss; reflexivity.

    (* Ibuiltin *)
  - simpl in Htransf.
    destruct (builtin_can_replicate e) eqn:Hrep.
    + (* Safe builtin *)
      destruct b as [r | | b1 b2] eqn:Hbres.
      * (* BR res -- safe triplication *)
        destruct (rm # r) eqn:Hrmr.
        unfold RTLgen.bind in Htransf.
        repeat egen_case.
        unfold update_instr in *.
        repeat lr_case.
        repeat reserve_instr_inv.
        simpl in *.
        eapply match_Ibuiltin_safe with (pc := p)
                                 (n1 := s.(st_nextnode))
                                 (n2 := Pos.succ (s.(st_nextnode))); eauto.
        { apply rm_builtin_args_map. }
        { rewrite 2!PTree.gso; try lia.
          rewrite PTree.gss; reflexivity. }
        { rewrite PTree.gso; try lia.
          rewrite PTree.gss; reflexivity. }
        { rewrite PTree.gss; reflexivity. }
      * (* BR_none -- fall through to generic *)
        unfold RTLgen.bind in Htransf; simpl in Htransf.
        repeat egen_case.
        unfold update_instr in *.
        repeat lr_case; simpl.
        eapply match_Ibuiltin_1.
        { intro HC; inv HC. }
        { eapply maj_vote_regsR_ptree_set; auto.
          eapply state_incr_maj_vote_regsR.
          2: { eapply maj_vote_regs_maj_vote_regsR; eauto. }
          intros pc0; inv s1; auto. }
        rewrite PTree.gss; reflexivity.
      * (* BR_splitlong -- fall through to generic *)
        unfold RTLgen.bind in Htransf; simpl in Htransf.
        repeat egen_case.
        unfold update_instr in *.
        repeat lr_case; simpl.
        eapply match_Ibuiltin_1.
        { intro HC; inv HC. }
        { eapply maj_vote_regsR_ptree_set; auto.
          eapply state_incr_maj_vote_regsR.
          2: { eapply maj_vote_regs_maj_vote_regsR; eauto. }
          intros pc0; inv s1; auto. }
        rewrite PTree.gss; reflexivity.
    + (* Non-safe builtin *)
      unfold RTLgen.bind in Htransf; simpl in Htransf.
      destruct (reg_of_builtin_res b) eqn:Hb.
      * repeat egen_case.
        unfold update_instr in *.
        repeat lr_case; simpl.
        destruct b; simpl in Hb; inv Hb.
        destruct (rm # r) eqn:Hr.
        eapply match_Ibuiltin_2.
        { auto. }
        { eapply maj_vote_regsR_ptree_set; auto.
          eapply state_incr_maj_vote_regsR.
          2: { eapply maj_vote_regs_maj_vote_regsR; eauto. }
          intros pc0; clear H0; inv s3; inv s4.
          specialize (H2 pc0); specialize (H5 pc0).
          destruct H2 as [H2 | H2]; auto. }
        2: { eauto. }
        rewrite PTree.gss; reflexivity.
        apply smoveR_ptree_set; auto.
        eapply copy_to_shadows_smoveR; eauto.
        simpl; lia.
      * repeat egen_case.
        unfold update_instr in *.
        repeat lr_case; simpl.
        eapply match_Ibuiltin_1.
        { intro HC; inv HC; inv Hb. }
        { eapply maj_vote_regsR_ptree_set; auto.
          eapply state_incr_maj_vote_regsR.
          2: { eapply maj_vote_regs_maj_vote_regsR; eauto. }
          intros pc0; inv s1; auto. }
        rewrite PTree.gss; reflexivity.

  (* Icond *)
  - unfold RTLgen.bind in Htransf; simpl in Htransf.
    repeat egen_case.
    unfold update_instr in *.
    repeat lr_case.
    simpl in *.
    apply maj_vote_regs_maj_vote_regsR in H; auto.
    repeat state_incr_inv.
    simpl in *; unfold Ple in *.
    econstructor; eauto.
    + repeat apply maj_vote_regsR_ptree_set; eauto.
    + rewrite PTree.gss; reflexivity.

  (* Ijumptable *)
  - unfold RTLgen.bind in Htransf; simpl in Htransf.
    destruct (rm # r) as [r2 r3] eqn:Hr.
    unfold RTLgen.bind in Htransf; simpl in Htransf.
    repeat egen_case.
    unfold update_instr in *.
    repeat lr_case.
    simpl in *.
    eapply maj_vote_maj_voteR in H1; eauto.
    repeat state_incr_inv.
    simpl in *; unfold Ple in *.
    econstructor; eauto.
    + repeat apply maj_voteR_ptree_set; eauto.
    + rewrite PTree.gss; reflexivity.

  (* Ireturn *)
  - destruct o; simpl in *.
    + unfold RTLgen.bind in Htransf; simpl in Htransf.
      destruct (rm # r) as [r2 r3] eqn:Hr.
      unfold RTLgen.bind in Htransf; simpl in Htransf.
      repeat egen_case.
      unfold update_instr in *.
      repeat lr_case.
      simpl in *.
      eapply maj_vote_maj_voteR in H1; eauto.
      repeat state_incr_inv.
      simpl in *; unfold Ple in *.
      econstructor; eauto.
      { repeat apply maj_voteR_ptree_set; eauto. }
      { rewrite PTree.gss; reflexivity. }
    + unfold RTLgen.bind in Htransf; simpl in Htransf.
      repeat egen_case.
      unfold update_instr in *.
      repeat lr_case; simpl.
      econstructor.
      rewrite PTree.gss; reflexivity.
Qed.

Lemma iterM_match_instr
  (l : list (positive * instruction)) re rm s s' pf u :
  iterM (transf_instr re rm) l s = RTLgen.OK u s' pf ->
  forall p i,
    p < s.(st_nextnode) ->
    In (p, i) l ->
    match_instr re rm (st_code s') p i.
Proof.
  revert s s' pf.
  induction l; simpl; intros s s' pf Htransf p i Hlt Hin.
  { contradiction. }
  unfold RTLgen.bind in Htransf.
  gen_case Hiter.
  gen_case Htransf'.
  destruct Hin as [?|Hin]; subst.
  2: { unfold RTLgen.bind in Htransf'.
       destruct u, u0.
       assert (H: match_instr re rm (st_code s'0) p i).
       { eapply IHl; eauto. }
       eapply state_incr_match_instr; eauto. }
  eapply transf_instr_match_instr; eauto.
  clear Hiter; inv s0; extlia.
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
  rm (f : function) (re : regenv) entrypoint s s1 s' pf pf1 :
  transf_fun re f s = RTLgen.OK entrypoint s' pf ->
  replication_map f s = RTLgen.OK rm s1 pf1 ->
  (forall p i, (fn_code f) ! p = Some i -> p < st_nextnode s) ->
  match_code re rm f.(fn_code) s'.(st_code).
Proof.
  intros Hf Hrm Hlt.
  unfold transf_fun in Hf.
  apply bind_inversion in Hf.
  destruct Hf as (rm' & s1' & pf0 & pf1' & Hrm' & Hf).
  rewrite Hrm' in Hrm; inv Hrm.
  apply bind_inversion in Hf.
  destruct Hf as (regs & s2 & pf2 & pf3 & Hlive & Hf).
  apply bind_inversion in Hf.
  destruct Hf as (n0 & s3 & pf4 & pf5 & Hparams & Hf).
  apply bind_inversion in Hf.
  destruct Hf as ([] & s4 & pf6 & pf7 & Hf & Hret).
  inv Hret.
  apply transf_code_code_matches in Hf; auto.
  intros p i Hpi.
  clear Hparams.
  clear Hlive.
  inv pf1; inv pf2; inv pf4.
  unfold Ple in *.
  specialize (Hlt p i Hpi); lia.
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

Lemma transf_fun'_code_matches rm (f tf : function) (re : regenv) s pf :
  transf_fun' re f = OK tf ->
  replication_map f (init_state f) = RTLgen.OK rm s pf ->
  match_code re rm f.(fn_code) tf.(fn_code).
Proof.
  unfold transf_fun'.
  destruct (transf_fun re f (init_state f)) eqn:Hf; intros H Hrm; inv H; simpl.
  eapply transf_fun_code_matches; eauto.
  intros; eapply lt_nextnode_init_state'; eauto.
Qed.

Lemma transf_function_code_matches rm (f tf : function) s pf :
  transf_function f = OK tf ->
  replication_map f (init_state f) = RTLgen.OK rm s pf ->
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

(** Relational specification of the TMR replication map construction.
    [replication_map_rel regs rm lo hi] holds when [rm] maps each
    register in [regs] to a pair of distinct shadows in [lo, hi).
    Each original register consumes two positions: r2 at mid, r3 at mid+1.
    The foldM processes the tail first, so the tail occupies [lo, mid)
    and the head register gets shadows at [mid] and [mid+1]. *)
Inductive replication_map_rel
  : list reg -> PMap.t (reg * reg) -> positive -> positive -> Prop :=
| rmr_nil :
  forall rm lo,
    replication_map_rel [] rm lo lo
| rmr_cons :
  forall r regs rm lo mid,
    replication_map_rel regs rm lo mid ->
    rm # r = (mid, Pos.succ mid) ->
    replication_map_rel (r :: regs) rm lo (Pos.succ (Pos.succ mid)).

Lemma replication_map_rel_lo_le_hi regs rm lo hi :
  replication_map_rel regs rm lo hi ->
  lo <= hi.
Proof. intro H; induction H; lia. Qed.

(** Derived range lemma: all shadow pairs lie in [lo, hi). *)
Lemma replication_map_rel_range regs rm lo hi :
  replication_map_rel regs rm lo hi ->
  Forall (fun r => let '(r2, r3) := rm # r in
                   lo <= r2 /\ r2 < hi /\ lo <= r3 /\ r3 < hi) regs.
Proof.
  intro H; induction H.
  - constructor.
  - constructor.
    + pose proof (replication_map_rel_lo_le_hi _ _ _ _ H).
      rewrite H0. lia.
    + eapply Forall_impl; [ | eauto ].
      simpl. intros a Ha. destruct (rm # a) as [a2 a3]. lia.
Qed.

(** Shadows within a single register are distinct. *)
Lemma replication_map_rel_shadow_distinct regs rm lo hi :
  replication_map_rel regs rm lo hi ->
  Forall (fun r => let '(r2, r3) := rm # r in r2 <> r3) regs.
Proof.
  intro H; induction H.
  - constructor.
  - constructor.
    + rewrite H0. lia.
    + eapply Forall_impl; [ | eauto ].
      simpl. intros a Ha. destruct (rm # a) as [a2 a3]. auto.
Qed.

(** Stability of [replication_map_rel] under [PMap.set] for keys
    outside the register list. *)
Lemma replication_map_rel_set regs rm lo hi a v :
  replication_map_rel regs rm lo hi ->
  ~ In a regs ->
  replication_map_rel regs (PMap.set a v rm) lo hi.
Proof.
  intros H Hnotin; induction H.
  - constructor.
  - constructor.
    + apply IHreplication_map_rel. intro Hin; apply Hnotin; right; auto.
    + rewrite PMap.gso; auto. intro; subst; apply Hnotin; left; auto.
Qed.

(** The [foldM] computation that builds the TMR replication map
    satisfies the relational specification. *)
Lemma foldM_satisfies_rel regs acc s rm s' pf :
  NoDup regs ->
  foldM
    (fun rm r1 => do r2 <- new_reg; do r3 <- new_reg; ret rm # r1 <- (r2, r3))
    regs acc s = RTLgen.OK rm s' pf ->
  replication_map_rel regs rm s.(st_nextreg) s'.(st_nextreg).
Proof.
  revert acc s rm s' pf.
  induction regs; simpl; intros acc s rm s' pf Hnd Hfold.
  - inv Hfold. constructor.
  - unfold RTLgen.bind in Hfold. simpl in Hfold.
    destruct (foldM _ regs acc s) eqn:Hrec; try discriminate.
    unfold new_reg in Hfold. simpl in Hfold.
    inv Hfold. inv Hnd. simpl.
    econstructor.
    + apply replication_map_rel_set; auto.
      eapply IHregs; eauto.
    + rewrite PMap.gss. reflexivity.
Qed.

(** Shadow-pair injectivity: distinct original registers get distinct
    shadow pairs. *)
Lemma replication_map_rel_injective regs rm lo hi :
  replication_map_rel regs rm lo hi ->
  NoDup regs ->
  forall r r', In r regs -> In r' regs -> r <> r' -> rm # r <> rm # r'.
Proof.
  induction 1; intros Hnd r0 r0' Hr0 Hr0' Hneq.
  - destruct Hr0.
  - inv Hnd.
    destruct Hr0 as [-> | Hr0]; destruct Hr0' as [-> | Hr0'].
    + congruence.
    + subst.
      pose proof (replication_map_rel_range _ _ _ _ H) as Hrng.
      rewrite Forall_forall in Hrng. specialize (Hrng _ Hr0').
      destruct (rm # r0') as [a2 a3].
      rewrite H0. intros [= Ha Hb]. subst. lia.
    + subst.
      pose proof (replication_map_rel_range _ _ _ _ H) as Hrng.
      rewrite Forall_forall in Hrng. specialize (Hrng _ Hr0).
      destruct (rm # r0) as [a2 a3].
      rewrite H0. intros [= Ha Hb]. subst. lia.
    + eapply IHreplication_map_rel; eauto.
Qed.

(** Each shadow pair is consecutive: r3 = Pos.succ r2. *)
Lemma replication_map_rel_consecutive regs rm lo hi :
  replication_map_rel regs rm lo hi ->
  Forall (fun r => let '(r2, r3) := rm # r in r3 = Pos.succ r2) regs.
Proof.
  intro H; induction H.
  - constructor.
  - constructor.
    + rewrite H0. reflexivity.
    + eapply Forall_impl; [ | eauto ].
      simpl. intros a Ha. destruct (rm # a) as [a2 a3]. auto.
Qed.

(** The relational spec implies shadow intervals don't overlap for
    distinct registers: both shadow components differ by at least 2. *)
Lemma replication_map_rel_disjoint_shadows regs rm lo hi :
  replication_map_rel regs rm lo hi ->
  NoDup regs ->
  forall r r', In r regs -> In r' regs -> r <> r' ->
    let '(r2, r3) := rm # r in
    let '(r2', r3') := rm # r' in
    (r3 < r2' \/ r3' < r2).
Proof.
  induction 1; intros Hnd r0 r0' Hr0 Hr0' Hneq.
  - destruct Hr0.
  - inv Hnd.
    destruct Hr0 as [-> | Hr0]; destruct Hr0' as [-> | Hr0'].
    + congruence.
    + rewrite H0.
      pose proof (replication_map_rel_range _ _ _ _ H) as Hrng.
      rewrite Forall_forall in Hrng. specialize (Hrng _ Hr0').
      destruct (rm # r0') as [a2 a3]. right; lia.
    + rewrite H0.
      pose proof (replication_map_rel_range _ _ _ _ H) as Hrng.
      rewrite Forall_forall in Hrng. specialize (Hrng _ Hr0).
      destruct (rm # r0) as [a2 a3]. left; lia.
    + eapply IHreplication_map_rel; eauto.
Qed.

(** The relational spec implies [rm_wf]: separate algorithmic
    correctness from invariant consequences. *)
Lemma rel_implies_rm_wf regs rm lo hi :
  replication_map_rel regs rm lo hi ->
  Forall (fun r => r < lo) regs ->
  NoDup regs ->
  rm_wf rm regs.
Proof.
  intros Hrel Hlt Hnd.
  pose proof (replication_map_rel_range _ _ _ _ Hrel) as Hrange.
  pose proof (replication_map_rel_consecutive _ _ _ _ Hrel) as Hcons.
  rewrite Forall_forall in Hlt.
  rewrite Forall_forall in Hrange.
  rewrite Forall_forall in Hcons.
  intros r1 r2 r3 Hin Hr1.
  specialize (Hlt _ Hin) as Hlt1.
  specialize (Hrange _ Hin) as Hrange1. rewrite Hr1 in Hrange1.
  destruct Hrange1 as [Hr2lo [Hr2hi [Hr3lo Hr3hi]]].
  specialize (Hcons _ Hin) as Hcons1. rewrite Hr1 in Hcons1.
  (* r3 = Pos.succ r2, so r2 < r3 *)
  split.
  - (* NoDup [r1; r2; r3] *)
    constructor.
    { simpl. intros [?|[?|[]]]; subst; lia. }
    constructor.
    { simpl. intros [?|[]]; subst; lia. }
    constructor; [ simpl; intros [] | constructor ].
  - (* Cross-register NoDup *)
    intros r1' r2' r3' Hin' Hneq Hr1'.
    specialize (Hlt _ Hin') as Hlt1'.
    specialize (Hrange _ Hin') as Hrange1'. rewrite Hr1' in Hrange1'.
    destruct Hrange1' as [Hr2'lo [Hr2'hi [Hr3'lo Hr3'hi]]].
    specialize (Hcons _ Hin') as Hcons1'. rewrite Hr1' in Hcons1'.
    pose proof (replication_map_rel_disjoint_shadows _ _ _ _ Hrel Hnd
                  r1 r1' Hin Hin' Hneq) as Hdisjoint.
    rewrite Hr1, Hr1' in Hdisjoint.
    (* Now we know: r3 = r2+1, r3' = r2'+1, and shadows don't overlap *)
    destruct Hdisjoint as [Hdisjoint | Hdisjoint];
      (constructor;
       [ simpl; intros [?|[?|[?|[?|[?|[]]]]]]; subst; lia
       | constructor;
         [ simpl; intros [?|[?|[?|[?|[]]]]]; subst; lia
         | constructor;
           [ simpl; intros [?|[?|[?|[]]]]; subst; lia
           | constructor;
             [ simpl; intros [?|[?|[]]]; subst; lia
             | constructor;
               [ simpl; intros [?|[]]; subst; lia
               | constructor; [ simpl; intros [] | constructor ]]]]]]).
Qed.

(** [NoDup] for [Regset.elements], derived from [NoDupA]. *)
Lemma elements_NoDup s : NoDup (Regset.elements s).
Proof.
  pose proof (Regset.elements_3w s) as H.
  induction H.
  - constructor.
  - constructor; auto.
    intro Hin. apply H.
    apply SetoidList.In_InA with (eqA := eq); auto. apply Eqsth.
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
  { eapply Regset.max_elt_2 in Hmax; eauto; extlia. }
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
  intro H.
  eapply rel_implies_rm_wf.
  - eapply foldM_satisfies_rel; eauto.
    apply elements_NoDup.
  - apply Forall_forall; intros r Hin.
    apply in_lt_max_reg; auto.
  - apply elements_NoDup.
Qed.

Lemma rm_wf_antimonotone rm rs1 rs2 :
  rm_wf rm rs1 ->
  (forall r, In r rs2 -> In r rs1) ->
  rm_wf rm rs2.
Proof.
  intros Hwf Hle r1 r2 r3 Hin Hr1.
  specialize (Hwf r1 r2 r3 (Hle _ Hin) Hr1); intuition.
Qed.

Lemma in_pset_of_list p l :
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

Definition rm_inv_list n (regs : list reg) (rm : PMap.t (reg * reg)) : Prop :=
  forall r1 r2 r3,
    rm # r1 = (r2, r3) ->
    In r1 regs ->
    n <= r2 /\ n <= r3.

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
      try solve [apply Regset.union_2, in_pset_of_list; auto];
      try solve [apply in_pset_of_list; assumption];
      try solve [apply Regset.singleton_2; reflexivity].
    + apply Regset.union_2, Regset.add_1; reflexivity.
    + apply Regset.union_2, Regset.add_2, in_pset_of_list; assumption.
    + apply Regset.add_1; reflexivity.
    + apply Regset.add_2, in_pset_of_list; assumption.
  - inv Hused; simpl;
      solve [apply Regset.union_2; eapply IHl; eauto; constructor; auto].
Qed.

Lemma reg_used_pset_in_all_regs params c r :
  reg_used params c r ->
  Regset.In r (all_regs params c).
Proof.
  intros [Hin | (p & i & Hget & Hused)].
  - apply Regset.union_2, in_pset_of_list; auto.
  - apply Regset.union_3.
    apply PTree.elements_correct in Hget.
    unfold code_regs.
    rewrite PTree.fold_spec.
    rewrite <- fold_left_rev_right.
    apply in_rev in Hget.
    eapply reg_used_fold_right; eauto.
Qed.

Lemma reg_used_in_all_regs_list params c r :
  reg_used params c r ->
  In r (all_regs_list params c).
Proof.
  intro Hused.
  apply in_elements.
  apply reg_used_pset_in_all_regs; auto.
Qed.

Lemma reg_used_in_code_pset_in_code_regs c r :
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

Lemma rm_inv_list_rm_inv params c rm :
  rm_inv_list (max_reg (all_regs params c) + 1) (all_regs_list params c) rm ->
  rm_inv params c rm.
Proof.
  intros Hrm r1 r2 r3 Hr1 Hused.
  specialize (Hrm r1 r2 r3 Hr1 (reg_used_in_all_regs_list _ _ _ Hused)).
  destruct Hrm as [Hr2 Hr3].
  repeat split.
  - intro Hin.
    assert (r2 < max_reg (all_regs params c) + 1).
    { apply in_lt_max_reg, in_elements, Regset.union_2, in_pset_of_list; auto. }
    lia.
  - intro Hin.
    assert (r3 < max_reg (all_regs params c) + 1).
    { apply in_lt_max_reg, in_elements, Regset.union_2, in_pset_of_list; auto. }
    lia.
  - intro Hin.
    assert (r2 < max_reg (all_regs params c) + 1).
    { apply in_lt_max_reg, in_elements, Regset.union_3.
      apply reg_used_in_code_pset_in_code_regs; auto. }
    lia.
  - intro Hin.
    assert (r3 < max_reg (all_regs params c) + 1).
    { apply in_lt_max_reg, in_elements, Regset.union_3.
      apply reg_used_in_code_pset_in_code_regs; auto. }
    lia.
Qed.

Lemma foldM_rm_inv_list regs s s' pf rm0 rm :
  Forall (fun r => r < s.(st_nextreg)) regs ->
  foldM
    (fun rm1 r1 =>
       do r2 <- new_reg; do r3 <- new_reg; ret rm1 # r1 <- (r2, r3))
    regs rm0 s = RTLgen.OK rm s' pf ->
  rm_inv_list s.(st_nextreg) regs rm.
Proof.
  revert pf.
  revert s s' rm0 rm.
  induction regs; simpl; intros s s' rm0 rm pf Hlt Hfold.
  { intros _ _ _ _ []. }
  inv Hlt.
  unfold RTLgen.bind in Hfold.
  repeat egen_case.
  eapply IHregs in H; auto.
  inv H3; inv H5; inv H0.
  repeat state_incr_inv.
  unfold Ple in *; simpl in *.
  intros x1 x2 x3 Hx1 Hin.
  destruct (peq a x1); subst.
  - rewrite PMap.gss in Hx1; inv Hx1; split; lia.
  - destruct Hin as [?|Hin]; try congruence.
    rewrite PMap.gso in Hx1; auto.
    specialize (H x1 x2 x3 Hx1 Hin); lia.
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
  rm_inv params c rm.
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

Theorem transf_function_match_fundef (f tf : fundef) :
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
    apply transf_code_code_matches in H2.
    inv H4.
    2: { intros p i Hpi.
         apply lt_nextnode_init_state' in Hpi.
         clear H0 H H1.
         repeat state_incr_inv.
         extlia. }
    destruct f.
    simpl in *.
    econstructor.
    { apply type_function_correct; eauto. }
    eapply match_fun.
    { eapply rm_wf_antimonotone.
      { eapply replication_map_wf; eauto. }
      auto. }
    { eapply replication_map_rm_inv'; eauto. }
    { auto. }
    2: { eapply copy_allR_monotone.
         { eapply copy_all_to_shadows_copy_allR; eauto. }
         clear H0 H H1.
         repeat state_incr_inv.
         unfold Ple in *; simpl in *.
         intros p i Hpi; destruct (H8 p); congruence. }
    apply Forall_forall; intros x Hin.
    unfold live_regs_to_copy in H; simpl in H.
    unfold live_regs in H; simpl in H.
    destruct (Liveness.analyze _).
    inv H.
    2: { inv H. }
    apply in_elements, Regset.diff_1, Regset.inter_2 in Hin.
    apply in_elements, Regset.union_3; auto.
  - inv Htransf; constructor.
Qed.
