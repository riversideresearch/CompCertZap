(** * Relational specificaton of the DMR transformation. *)

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
  RTLgen
  RTLtyping
  Smallstep
  Values
.
Require Import RTL.
Require Import RTLdmr.
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

Definition rm_wf (rm : PMap.t reg) (l : list positive) : Prop :=
  forall r,
    In r l ->
    r <> rm # r /\
      forall r',
        In r' l ->
        r <> r' ->
        NoDup [r; rm # r; r'; rm # r'].

Inductive rm_l (rm : PMap.t reg)
  : list reg -> list reg -> Prop :=
| match_nil : rm_l rm [] []
| match_cons : forall r1 rs1 rs2,
    rm_l rm rs1 rs2 ->
    rm_l rm (r1 :: rs1) (rm # r1 :: rs2).

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

Inductive checkR
  (c : code) (ty : typ) (r1 r2 : reg) (pc succ : node) : Prop :=
| check_1 :
  forall chk,
    is_actual_type ty ->
    check_of_typ ty r1 r2 = Some chk ->
    c ! pc = Some (chk succ) ->
    checkR c ty r1 r2 pc succ.

Inductive check_regsR c re rm : list reg -> node -> node -> Prop :=
| check_regs_nil :
  forall pc,
    check_regsR c re rm [] pc pc
| check_regs_cons :
  forall arg args pc succ n,
    checkR c (re arg) arg (rm # arg) pc n ->
    check_regsR c re rm args n succ ->
    check_regsR c re rm (arg :: args) pc succ.

Inductive smoveR
  (c : code) (ty : typ) (src dst : reg) (pc succ : node): Prop :=
| smove_1 :
  forall mov,
    smove ty src dst = Some mov ->
    c ! pc = Some (mov succ) ->
    smoveR c ty src dst pc succ.

Ltac smoveR_inv :=
  try match goal with
  | [H: smoveR _ _ _ _ _ _ |- _ ] => inv H
  end.

Inductive copy_allR re rm c : list reg -> node -> node -> Prop :=
| copy_all_nil :
  forall n,
    copy_allR re rm c [] n n
| copy_all_cons :
  forall r rs succ n p,
    smoveR c (re r) r (rm # r) n p ->
    copy_allR re rm c rs p succ ->
    copy_allR re rm c (r :: rs) n succ.

Lemma copy_to_shadows_smoveR
  (rm : Regmap.t reg) (ty : typ) (r : reg) (pc succ : node)
  (u : unit) (s0 s1 : RTLgen.state) pf (c : code) :
  pc < s0.(st_nextnode) ->
  copy_to_shadows rm ty r pc succ s0 = RTLgen.OK u s1 pf ->
  (forall p i, s1.(st_code) ! p = Some i -> c ! p = Some i) ->
  smoveR c ty r (rm # r) pc succ.
Proof.
  intros Hpc Hcopy Hc.
  unfold copy_to_shadows in Hcopy.
  unfold error in Hcopy.
  simpl in *.
  destruct (smove ty r (rm # r)) eqn:Hmov; gen_contra.
  unfold update_instr in Hcopy.
  repeat lr_case.
  simpl in *.
  repeat state_incr_inv.
  simpl in *; unfold Ple in *.
  econstructor; eauto.
  apply Hc.
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
  econstructor; eauto.
  2: { eapply IHparams; eauto.
       intros p i Hpi; apply Hc.
       repeat state_incr_inv; simpl in *.
       destruct (H3 p); congruence. }
  eapply copy_to_shadows_smoveR; eauto; simpl; try lia.
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
    contains instructions starting at [pc] that correspond to
    instruction [i] in the original program, wrt. register environment
    [regenv] and replication map [rm]. *)
Inductive match_instr
  (re : regenv) (rm : PMap.t reg) (c : code) (pc : positive)
  : instruction -> Prop :=
| match_Inop :
  forall n,
    PTree.get pc c = Some (Inop n) ->
    match_instr re rm c pc (Inop n)
| match_Iop :
  forall op args1 args2 res1 n succ
    (ARGS : rm_l rm args1 args2)
    (PC : c ! pc = Some (Iop op args2 (rm # res1) n))
    (N2 : c ! n = Some (Iop op args1 res1 succ)),
    match_instr re rm c pc (Iop op args1 res1 succ)
| match_iload :
  forall chunk addr args res n1 n2 succ
    (CHK_ARGS : check_regsR c re rm (dedup args) pc n1)
    (N1 : c ! n1 = Some (Iload chunk addr args res n2))
    (MOVE : smoveR c (re res) res (rm # res) n2 succ),
  match_instr re rm c pc (Iload chunk addr args res succ)
| match_Istore :
  forall chunk addr args src n succ
    (CHK_REGS : check_regsR c re rm (dedup (src :: args)) pc n)
    (N : c ! n = Some (Istore chunk addr args src succ)),
    match_instr re rm c pc (Istore chunk addr args src succ)
| match_Icall :
  forall sig fn args res succ n1 n2
    (CHK_ARGS : check_regsR c re rm (dedup (regs_of_fn fn ++ args)) pc n1)
    (N1 : c ! n1 = Some (Icall sig fn args res n2))
    (MOVE : smoveR c (re res) res (rm # res) n2 succ),
    match_instr re rm c pc (Icall sig fn args res succ)
| match_Itailcall :
  forall sig fn args n
    (CHK_ARGS : check_regsR c re rm (dedup (regs_of_fn fn ++ args)) pc n)
    (N : c ! n = Some (Itailcall sig fn args)),
    match_instr re rm c pc (Itailcall sig fn args)
| match_Ibuiltin_1 :
  forall ef bargs bres n succ
    (NORES : ~ is_BR bres) (* no result register *)
    (CHK_ARGS : check_regsR c re rm (dedup (regs_of_builtin_args bargs)) pc n)
    (N : c ! n = Some (Ibuiltin ef bargs bres succ)),
    match_instr re rm c pc (Ibuiltin ef bargs bres succ)
| match_Ibuiltin_2 :
  forall ef bargs res n1 n2 succ
    (CHK_ARGS : check_regsR c re rm (dedup (regs_of_builtin_args bargs)) pc n1)
    (N1 : c ! n1 = Some (Ibuiltin ef bargs (BR res) n2))
    (MOVE : smoveR c (re res) res (rm # res) n2 succ),
    match_instr re rm c pc (Ibuiltin ef bargs (BR res) succ)
| match_Icond :
  forall cond args ifso ifnot n
    (CHK_ARGS : check_regsR c re rm (dedup args) pc n)
    (N : c ! n = Some (Icond cond args ifso ifnot)),
    match_instr re rm c pc (Icond cond args ifso ifnot)
| match_Ijumptable :
  forall arg tbl n
    (CHK : checkR c (re arg) arg (rm # arg) pc n)
    (N : c ! n = Some (Ijumptable arg tbl)),
    match_instr re rm c pc (Ijumptable arg tbl)
| match_Ireturn_1 :
  forall (PC : c ! pc = Some (Ireturn None)),
  match_instr re rm c pc (Ireturn None)
| match_Ireturn_2 :
  forall arg n
    (CHK : checkR c (re arg) arg (rm # arg) pc n)
    (N : c ! n = Some (Ireturn (Some arg))),
    match_instr re rm c pc (Ireturn (Some arg)).

(** [match_code re rm c c'] when for every instruction [i] at location
    [pc] in the original code [c], there is a matching code sequence
    at [pc] in the translated code [c']. *)
Definition match_code (re : regenv) (rm : PMap.t reg) (c c': code) : Prop :=
  forall p i, c ! p = Some i -> match_instr re rm c' p i.

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

Definition reg_used_in_code (c : code) (r : reg) : Prop :=
  exists pc instr,
    c! pc = Some instr /\ reg_used_in_instr r instr.

(** A register is 'used' in a function whenever it either appears in
    the function's parameter list or is used somewhere in its code. *)
Definition reg_used (params : list reg) (c : code) (r : reg) : Prop :=
  In r params \/ reg_used_in_code c r.

(** Replication map invariant. Asserts that shadow registers in the
    translated function do not appear in the parameters or code of the
    original function. *)
Definition rm_inv
  (params : list reg) (c : code) (rm : PMap.t reg) : Prop :=
  forall (r : reg),
    reg_used params c r ->
    ~ In (rm # r) params /\ ~ reg_used_in_code c (rm # r).

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
  intros Hrm r Hused.
  specialize (Hrm r (reg_used_cons _ _ _ _ Hused)).
  firstorder.
Qed.

Inductive match_function re rm : function -> function -> Prop :=
| match_fun :
  forall sig params stacksize c c' entrypoint entrypoint' copy_regs
    (RM_WF: rm_wf rm (all_regs_list params c))
    (RM_INV: rm_inv params c rm)
    (CODE: match_code re rm c c')
    (COPY_REGS_OK: Forall (fun x => In x (all_regs_list params c)) copy_regs)
    (COPY: copy_allR re rm c' (app' params copy_regs) entrypoint' entrypoint),
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
  rm_l rm l (map (fun r => rm # r) l).
Proof. induction l; constructor; auto. Qed.

Lemma state_incr_checkR s s' ty r1 r2 pc succ :
  (forall pc : positive, (st_code s) ! pc = None \/
                      (st_code s') ! pc = (st_code s) ! pc) ->
  checkR (st_code s) ty r1 r2 pc succ ->
  checkR (st_code s') ty r1 r2 pc succ.
Proof.
  intros Hle Hchk; inv Hchk.
  destruct (Hle pc) as [?|Hpc]; try congruence.
  econstructor; eauto.
  rewrite Hpc; eauto.
Qed.

Lemma state_incr_check_regsR re rm p s s' rs n :
  (forall pc : positive, (st_code s) ! pc = None \/
                      (st_code s') ! pc = (st_code s) ! pc) ->
  check_regsR (st_code s) re rm rs p n ->
  check_regsR (st_code s') re rm rs p n.
Proof.
  revert p n s s'.
  induction rs; intros p n s s' Hle Hchk; inv Hchk.
  { constructor. }
  econstructor; eauto.
  eapply state_incr_checkR; eauto.
Qed.

Lemma state_incr_smoveR s s' ty r1 r2 pc succ :
  (forall pc : positive, (st_code s) ! pc = None \/
                      (st_code s') ! pc = (st_code s) ! pc) ->
  smoveR (st_code s) ty r1 r2 pc succ ->
  smoveR (st_code s') ty r1 r2 pc succ.
Proof.
  intros Hle Hchk; inv Hchk.
  destruct (Hle pc) as [?|Hpc]; try congruence.
  econstructor; eauto.
  rewrite Hpc; eauto.
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
    destruct (H1 n) as [?|Hs'1]; try congruence.
    econstructor; eauto.
    + rewrite Hs'; eauto.
    + rewrite Hs'1; eauto.
  - inv MOVE.
    destruct (H1 n1) as [?|Hn1]; try congruence.
    destruct (H1 n2) as [?|Hn2]; try congruence.
    econstructor; eauto.
    + eapply state_incr_check_regsR; eauto.
    + rewrite Hn1; eauto.
    + econstructor; eauto; rewrite Hn2; eauto.
  - destruct (H1 n) as [?|Hs']; try congruence.
    econstructor; eauto.
    2: { rewrite Hs'; auto. }
    eapply state_incr_check_regsR; eauto.
  - inv MOVE.
    destruct (H1 n1) as [?|Hn1]; try congruence.
    destruct (H1 n2) as [?|Hn2]; try congruence.
    econstructor; eauto.
    + eapply state_incr_check_regsR; eauto.
    + rewrite Hn1; eauto.
    + econstructor; eauto; rewrite Hn2; eauto.
  - destruct (H1 n) as [?|Hn]; try congruence.
    econstructor; eauto.
    + eapply state_incr_check_regsR; eauto.
    + rewrite Hn; eauto.
  - econstructor; auto.
    + eapply state_incr_check_regsR; eauto.
    + destruct (H1 n); congruence.
  - destruct (H1 n1) as [?|Hn1]; try congruence.
    eapply match_Ibuiltin_2.
    + eapply state_incr_check_regsR; eauto.
    + rewrite Hn1; eauto.
    + eapply state_incr_smoveR; eauto.
  - destruct (H1 n) as [?|Hn]; try congruence.
    econstructor; eauto.
    + eapply state_incr_check_regsR; eauto.
    + rewrite Hn; eauto.
  - destruct (H1 n) as [?|Hn]; try congruence.
    econstructor; eauto.
    + eapply state_incr_checkR; eauto.
    + rewrite Hn; eauto.
  - destruct (H1 p) as [?|Hp]; try congruence.
    constructor; rewrite Hp; auto.
  - destruct (H1 n) as [?|Hn]; try congruence.
    econstructor; eauto.
    + eapply state_incr_checkR; eauto.
    + rewrite Hn; auto.
Qed.

Lemma check_of_typ_is_actual_type ty r1 r2 i :
  check_of_typ ty r1 r2 = Some i ->
  is_actual_type ty.
Proof. destruct ty; simpl; intro Hchk; auto; inv Hchk. Qed.

Lemma check_checkR re r1 r2 pc succ s s' pf :
  pc < s.(st_nextnode) ->
  check re r1 r2 pc s = RTLgen.OK succ s' pf ->
  checkR s'.(st_code) (re r1) r1 r2 pc succ.
Proof.
  unfold check, RTLgen.bind; simpl; intros Hlt Hchk.
  destruct (check_of_typ (re r1) r1 r2) eqn:Hty.
  2: { inv Hchk. }
  repeat egen_case.
  unfold update_instr in *; simpl in *.
  lr_case; try congruence; lr_case.
  simpl in *.
  econstructor; eauto.
  2: { rewrite PTree.gss; reflexivity. }
  eapply check_of_typ_is_actual_type; eauto.
Qed.

Lemma check_succ_lt_nextnode re r1 r2 pc succ s s' pf :
  pc < s.(st_nextnode) ->
  check re r1 r2 pc s = RTLgen.OK succ s' pf ->
  succ < s'.(st_nextnode).
Proof.
  unfold check, RTLgen.bind; simpl; intros Hlt Hchk.
  destruct (check_of_typ (re r1) r1 r2) eqn:Hty.
  2: { inv Hchk. }
  repeat egen_case.
  unfold update_instr in *; simpl in *.
  lr_case; try congruence; lr_case.
  simpl in *; lia.
Qed.

Lemma check_regs_succ_lt_nextnode re rm regs pc succ s s' pf :
  pc < s.(st_nextnode) ->
  check_regs re rm regs pc s = RTLgen.OK succ s' pf ->
  succ < s'.(st_nextnode).
Proof.
  revert pc succ s s' pf.
  induction regs; intros pc n s s' pf Hlt Hchk; inv Hchk; auto.
  unfold RTLgen.bind in H0.
  gen_case Hchk.
  egen_case.
  apply IHregs in H; auto.
  eapply check_succ_lt_nextnode; eauto.
Qed.

Lemma check_regs_check_regsR re rm regs pc succ s s' pf :
  pc < s.(st_nextnode) ->
  check_regs re rm regs pc s = RTLgen.OK succ s' pf ->
  check_regsR s'.(st_code) re rm regs pc succ.
Proof.
  revert pc succ s s' pf.
  induction regs; simpl; intros pc succ s s' pf Hlt Hchk.
  { inv Hchk; constructor. }
  unfold RTLgen.bind in Hchk.
  gen_case H0.
  gen_case H1.
  pose proof H0 as H0'.
  apply check_succ_lt_nextnode in H0'; auto.
  apply IHregs in H1; auto.
  econstructor; eauto.
  eapply state_incr_checkR.
  2: { eapply check_checkR; eauto. }
  intro m; inv s1; auto.
Qed.

Lemma checkR_ptree_set c ty r1 r2 pc succ n i :
  c ! n = None ->
  checkR c ty r1 r2 pc succ ->
  checkR (PTree.set n i c) ty r1 r2 pc succ.
Proof.
  intros Hc Hchk; inv Hchk.
  econstructor; eauto.
  destruct (peq n pc);
    subst; try congruence.
  rewrite PTree.gso; eauto.
Qed.

Lemma check_regsR_ptree_set c re rm rs pc succ n i :
  c ! n = None ->
  check_regsR c re rm rs pc succ ->
  check_regsR (PTree.set n i c) re rm rs pc succ.
Proof.
  revert pc succ.
  induction rs; intros pc succ Hc Hchk; inv Hchk.
  { constructor. }
  econstructor; eauto.
  apply checkR_ptree_set; auto.
Qed.

Lemma smoveR_ptree_set c ty r1 r2 pc succ n i :
  c ! n = None ->
  smoveR c ty r1 r2 pc succ ->
  smoveR (PTree.set n i c) ty r1 r2 pc succ.
Proof.
  intros Hc Hmove; inv Hmove.
  econstructor; eauto.
  destruct (peq n pc);
    subst; try congruence; rewrite PTree.gso; eauto.
Qed.

Lemma copy_allR_ptree_set re rm c rs pc succ n i :
  c ! n = None ->
  copy_allR re rm c rs pc succ ->
  copy_allR re rm (PTree.set n i c) rs pc succ.
Proof.
  revert pc succ.
  induction rs; intros pc succ Hc Hchk; inv Hchk.
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
  - unfold RTLgen.bind in Htransf.
    repeat egen_case.
    unfold update_instr in *.
    repeat lr_case.
    inv H.
    eapply match_Iop with (pc := p)
                          (n := s.(st_nextnode)); simpl; eauto.
    { apply rm_l_map_rm. }
    + rewrite PTree.gso; try lia.
      rewrite PTree.gss; reflexivity.
    + rewrite PTree.gss; reflexivity.

  (* Iload *)
  - unfold RTLgen.bind in Htransf; simpl in Htransf.
    repeat egen_case.
    unfold update_instr in H2.
    repeat lr_case; simpl.
    eapply copy_to_shadows_smoveR in H0; eauto.
    2: { simpl; lia. }
    eapply match_iload with (n1:=n0); eauto.
    3: { apply smoveR_ptree_set; eauto. }
    2: { rewrite PTree.gss; auto. }
    eapply check_regsR_ptree_set; auto.
    eapply state_incr_check_regsR.
    2: { eapply check_regs_check_regsR; eauto. }
    intro pc; inv s3; auto.

  (* Istore *)
  - unfold RTLgen.bind in Htransf.
    simpl in Htransf.
    gen_case Hchk.
    gen_case Hupd.
    replace ((do succ <- check re r rm # r p; check_regs re rm l succ) s)
      with (check_regs re rm (r :: l) p s) in Hchk by auto.
    apply check_regs_check_regsR in Hchk; auto.
    unfold update_instr in Hupd.
    repeat lr_case.
    simpl in *.
    inv s1; inv pf; simpl in *; unfold Ple in *.
    econstructor.
    2: { rewrite PTree.gss; reflexivity. }
    apply check_regsR_ptree_set; auto.

  (* Icall *)
  - simpl in Htransf; unfold RTLgen.bind in Htransf; simpl in Htransf.
    repeat egen_case.
    unfold copy_to_shadows in H0.
    unfold RTLgen.bind in H0.
    unfold error in *.
    destruct (smove (re r) r (rm # r)) eqn:Hmov; gen_contra.
    repeat egen_case.
    unfold update_instr in *.
    repeat lr_case.
    simpl in *.
    assert (Hn0: n0 < s'0.(st_nextnode)).
    { eapply check_regs_succ_lt_nextnode.
      2: { eauto. }
      auto. }
    apply check_regs_check_regsR in H; auto.
    simpl in *.
    repeat state_incr_inv.
    simpl in *; unfold Ple in *.
    econstructor; eauto.
    + repeat apply check_regsR_ptree_set; eauto.
    + rewrite PTree.gss; reflexivity.
    + econstructor; eauto.
      rewrite PTree.gso; try lia.
      rewrite PTree.gss; reflexivity.

  (* Itailcall *)
  - unfold RTLgen.bind in Htransf; simpl in Htransf.
    repeat egen_case.
    unfold update_instr in *.
    repeat lr_case.
    simpl in *.
    apply check_regs_check_regsR in H; auto.
    repeat state_incr_inv.
    simpl in *; unfold Ple in *.
    econstructor; eauto.
    + repeat apply check_regsR_ptree_set; eauto.
    + rewrite PTree.gss; reflexivity.

  (* Ibuiltin *)
  - unfold RTLgen.bind in Htransf; simpl in Htransf.
    destruct (reg_of_builtin_res b) eqn:Hb.
    + repeat egen_case.
      unfold update_instr in H2.
      repeat lr_case; simpl.
      destruct b; simpl in Hb; inv Hb.
      eapply match_Ibuiltin_2.
      { eapply check_regsR_ptree_set; auto.
        eapply state_incr_check_regsR.
        2: { eapply check_regs_check_regsR; eauto. }
        intros; clear H0; inv s3.
        specialize (H2 pc).
        destruct H2 as [H2 | H2]; auto. }
      rewrite PTree.gss; reflexivity.
      apply smoveR_ptree_set; auto.
      eapply copy_to_shadows_smoveR; eauto.
      simpl; lia.
    + repeat egen_case.
      unfold update_instr in H0.
      repeat lr_case; simpl.
      eapply match_Ibuiltin_1.
      { intro HC; inv HC; inv Hb. }
      { eapply check_regsR_ptree_set; auto.
        eapply state_incr_check_regsR.
        2: { eapply check_regs_check_regsR; eauto. }
        intros; inv s1.
        specialize (H2 pc).
        destruct H2 as [H2 | H2]; auto. }
      rewrite PTree.gss; reflexivity.

  (* Icond *)
  - unfold RTLgen.bind in Htransf; simpl in Htransf.
    repeat egen_case.
    unfold update_instr in *.
    repeat lr_case.
    simpl in *.
    apply check_regs_check_regsR in H; auto.
    repeat state_incr_inv.
    simpl in *; unfold Ple in *.
    econstructor; eauto.
    + repeat apply check_regsR_ptree_set; eauto.
    + rewrite PTree.gss; reflexivity.

  (* Ijumptable *)
  - unfold RTLgen.bind in Htransf; simpl in Htransf.
    unfold RTLgen.bind in Htransf; simpl in Htransf.
    repeat egen_case.
    unfold update_instr in *.
    repeat lr_case.
    simpl in *.
    eapply check_checkR in H1; eauto.
    repeat state_incr_inv.
    simpl in *; unfold Ple in *.
    econstructor; eauto.
    + repeat apply checkR_ptree_set; eauto.
    + rewrite PTree.gss; reflexivity.

  (* Ireturn *)
  - destruct o; simpl in *.
    + unfold RTLgen.bind in Htransf; simpl in Htransf.
      unfold RTLgen.bind in Htransf; simpl in Htransf.
      repeat egen_case.
      unfold update_instr in *.
      repeat lr_case.
      simpl in *.
      eapply check_checkR in H1; eauto.
      repeat state_incr_inv.
      simpl in *; unfold Ple in *.
      econstructor; eauto.
      { repeat apply checkR_ptree_set; eauto. }
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
  clear Hiter; inv s0; unfold Ple in *; lia.
Qed.

Lemma transf_code_code_matches (c : code) (re : regenv) rm s s' pf u :
  (forall p i, c ! p = Some i -> p < st_nextnode s) ->
  transf_code re rm c s = RTLgen.OK u s' pf ->
  match_code re rm c s'.(st_code).
Proof.
  intros Hlt Hc p i Hi.
  eapply iterM_match_instr; eauto.
  apply PTree.elements_correct; eauto.
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
  inv H1; econstructor; eauto.
Qed.

(* TODO: This is a bit of a mess. Might be a good idea to define a
   relational specification of the algorithm and factor this into 1)
   proving the code satisfies the spec and 2) proving the spec implies
   rm_wf. However, it isn't as bad here for DMR as it is for TMR in
   Replicatespec.v. *)
Lemma replication_map_wf_aux regs acc s rm s' pf :
  Forall (fun r => r < s.(st_nextreg)) regs ->
  foldM
    (fun rm r1 => do r2 <- new_reg; ret rm # r1 <- r2)
    regs acc s = RTLgen.OK rm s' pf ->
  rm_wf rm regs /\
    Forall (fun r1 => forall r2, PMap.get r1 rm = r2 ->
                         s.(st_nextreg) <= r2 < s'.(st_nextreg)) regs.
Proof.
  revert acc s rm s' pf.
  induction regs; simpl; intros acc s rm s' pf Hall H.
  { split.
    - intros r1 [].
    - constructor. }
  unfold new_reg in H.
  unfold RTLgen.bind in H.
  simpl in H.
  match goal with
  | [ _: match ?X with | RTLgen.Error _ => _ | RTLgen.OK _ _ _ => _ end = _ |- _ ] =>
      destruct X eqn:HX
  end.
  { inv H. }
  inv H.
  inv Hall.
  rename t into rm.
  assert (rm_wf rm regs).
  { eapply IHregs; eauto. }
  assert (Forall
            (fun r1 : positive =>
               forall r2 : reg,
                 rm # r1 = r2 -> st_nextreg s <= r2 < st_nextreg s'0) regs).
  { eapply IHregs; eauto. }
  clear HX IHregs.
  rewrite Forall_forall in H0.
  rewrite Forall_forall in H2.
  split.
  - intros r1 Hin.
    inv s0; simpl in *; unfold Ple in *.
    destruct (peq a r1); subst.
    + clear Hin.
      rewrite PMap.gss.
      split.
      * lia.
      * intros r1' Hin Hneq.
        inv Hin.
        { congruence. }
        rewrite PMap.gso; auto.
        specialize (H0 r1' H6).
        constructor.
        { intro Hin; inv Hin; try lia.
          inv H7; try lia.
          inv H8.
          2: { inv H7. }
          specialize (H0 (rm # r1') (eq_refl _)); lia. }
        constructor.
        { intro Hin; inv Hin; try lia.
          apply H2 in H6; lia.
          inv pf; simpl in *; unfold Ple in *.
          inv H7; auto.
          apply H0 in H11; lia. }
        constructor.
        { intro Hin; inv Hin.
          - apply H2 in H6.
            apply H0 in H7; lia.
          - inv H7. }
        constructor; intuition; constructor.
    + destruct Hin as [? | Hin]; try congruence.
      rewrite PMap.gso; auto.
      specialize (H2 r1 Hin).
      split.
      * apply H in Hin; intuition.
      * specialize (H r1 Hin); destruct H as [H H'].
        intros r1' Hin' Hneq; try congruence.
        destruct (peq a r1'); subst.
        { rewrite PMap.gss.
          clear Hin' n.
          constructor.
          { intro HC; inv HC; auto.
            inv H6; auto.
            inv H7; try lia.
            inv H6. }
          constructor.
          { intro HC; inv HC.
            { eapply H0 in Hin; eauto; lia. }
            inv H6.
            { eapply H0 in Hin; eauto; lia. }
            inv H7. }
          constructor.
          { intro HC; inv HC; auto; lia. }
          constructor.
          { intro HC; inv HC. }
          constructor. }
        destruct Hin' as [? | Hin']; try contradiction.
        rewrite PMap.gso; auto.
  - simpl.
    apply Forall_forall; intros r1 Hin r2 Hr1.
    inv s0; simpl in *; unfold Ple in *.
    destruct (peq a r1); subst.
    { rewrite PMap.gss; lia. }
    inv Hin; try congruence.
    rewrite PMap.gso; auto.
    eapply H0 in H6; eauto; lia.
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
  apply Forall_forall; intros r Hin.
  apply in_lt_max_reg; auto.
Qed.

Lemma rm_wf_antimonotone rm rs1 rs2 :
  rm_wf rm rs1 ->
  (forall r, In r rs2 -> In r rs1) ->
  rm_wf rm rs2.
Proof.
  intros Hwf Hle r1 Hin.
  specialize (Hwf r1 (Hle _ Hin)); intuition.
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

Definition rm_inv_list n (regs : list reg) (rm : PMap.t reg) : Prop :=
  forall r1,
    In r1 regs ->
    n <= rm # r1.

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

Lemma reg_used_pset_in_all_regs params c r :
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
  reg_used params c r ->
  In r (all_regs_list params c).
Proof.
  intro Hused.
  apply in_elements.
  apply reg_used_pset_in_all_regs; auto.
Qed.

Lemma reg_used_in_code_in_code_regs c r :
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
  intros Hrm r1 Hused.
  specialize (Hrm r1 (reg_used_in_all_regs_list _ _ _ Hused)).
  split; intro Hin.
  - assert (rm # r1 < max_reg (all_regs params c) + 1).
    { apply in_lt_max_reg, in_elements, Regset.union_2, in_regset_of_list; auto. }
    lia.
  - assert (rm # r1 < max_reg (all_regs params c) + 1).
    { apply in_lt_max_reg, in_elements, Regset.union_3.
      apply reg_used_in_code_in_code_regs; auto. }
    lia.
Qed.

Lemma foldM_rm_inv_list regs s s' pf rm0 rm :
  Forall (fun r => r < s.(st_nextreg)) regs ->
  foldM
    (fun rm1 r1 =>
       do r2 <- new_reg; ret rm1 # r1 <- r2)
    regs rm0 s = RTLgen.OK rm s' pf ->
  rm_inv_list s.(st_nextreg) regs rm.
Proof.
  revert pf.
  revert s s' rm0 rm.
  induction regs; simpl; intros s s' rm0 rm pf Hlt Hfold.
  { intros _ []. }
  inv Hlt.
  unfold RTLgen.bind in Hfold.
  repeat egen_case.
  eapply IHregs in H; auto.
  inv H3; inv H4.
  repeat state_incr_inv.
  unfold Ple in *; simpl in *.
  intros x1 Hin.
  destruct (peq a x1); subst.
  - rewrite PMap.gss; lia.
  - destruct Hin as [?|Hin]; try congruence.
    rewrite PMap.gso; auto.
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
    apply transf_code_code_matches in H2.
    inv H4.
    2: { intros p i Hpi.
         apply lt_nextnode_init_state' in Hpi.
         clear H0 H H1.
         repeat state_incr_inv.
         unfold Ple in *; simpl in *; lia. }
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
