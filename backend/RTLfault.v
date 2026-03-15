Require Import
  AST
  Builtins2
  Coqlib
  Events
  Globalenvs
  Integers
  Maps
  Memory
  Op
  Registers
  RTL
  Smallstep
  Values
.

Record fstate : Type :=
  mkfstate { fs_state : RTL.state
           ; fault : bool }.

Inductive val_compat : val -> val -> Prop :=
| val_compat_undef : forall v, val_compat Vundef v
| val_compat_int : forall i j, val_compat (Vint i) (Vint j)
| val_compat_long : forall i j, val_compat (Vlong i) (Vlong j)
| val_compat_float : forall x y, val_compat (Vfloat x) (Vfloat y)
| val_compat_single : forall x y, val_compat (Vsingle x) (Vsingle y)
| val_compat_ptr : forall b1 b2 ofs1 ofs2, val_compat (Vptr b1 ofs1) (Vptr b2 ofs2).

Lemma val_compat_refl (v : val) :
  val_compat v v.
Proof. destruct v; constructor. Qed.

Lemma val_compat_trans (v1 v2 v3 : val) :
  val_compat v1 v2 ->
  val_compat v2 v3 ->
  val_compat v1 v3.
Proof.
  intros H1 H2.
  inversion H1; inversion H2; subst; try solve [constructor]; congruence.
Qed.

Lemma val_lessdef_compat (v1 v2 : val) :
  Val.lessdef v1 v2 ->
  val_compat v1 v2.
Proof.
  intro H; inversion H; subst; try constructor.
  apply val_compat_refl.
Qed.

(* Technically we could/should allow faults (and not vote on) on most
   builtins, just not external function calls or votes themselves. *)
Definition zap_allowed (i : instruction) : Prop :=
  match i with
  | Iop op _ _ _ => ~ is_protected op
  | Iload _ _ _ _ _ => False
  | Istore _ _ _ _ _ => False
  | Icall _ _ _ _ _ => False
  | Itailcall _ _ _ => False
  | Ibuiltin _ _ _ _ => False
  | _ => True
  end.

Inductive maybe_zap (f : function) (pc : node)
  : RTL.state -> bool -> RTL.state -> bool -> Prop :=
| maybe_zap_refl : forall s b, maybe_zap f pc s b s b
| maybe_zap_reg : forall stk sp pc' rs m i r v,
    val_compat (rs # r) v ->
    f.(fn_code) ! pc = Some i ->
    zap_allowed i ->
    res_of_instruction i = Some r ->
    maybe_zap f pc
      (State stk f sp pc' rs m) false
      (State stk f sp pc' (rs # r <- v) m) true.

Section RELSEM.
Variable ge: genv.

Inductive not_regular_state : RTL.state -> Prop :=
| not_regular_state_Callstate : forall stk f args m,
    not_regular_state (Callstate stk f args m)
| not_regular_state_Returnstate : forall stk v m,
    not_regular_state (Returnstate stk v m).

Inductive fstep : fstate -> trace -> fstate -> Prop :=
| fstep_step_State : forall stk f sp pc rs m t s' s'' b b'
    (STEP: @RTL.step Builtins2.Two Builtins2.VoteSemantics_Two ge
             (State stk f sp pc rs m) t s')
    (ZAP: maybe_zap f pc s' b s'' b'),
    fstep
      {| fs_state := State stk f sp pc rs m; fault := b |}
      t
      {| fs_state := s''; fault := b' |}
| fstep_step_other : forall s t s' b
    (HS: not_regular_state s)
    (STEP: @RTL.step Builtins2.Two Builtins2.VoteSemantics_Two ge s t s'),
    fstep {| fs_state := s; fault := b |} t {| fs_state := s'; fault := b |}.

Inductive initial_state (p : program) : fstate -> Prop :=
| initial_state_intro : forall s,
    RTL.initial_state p s ->
    initial_state p {| fs_state := s; fault := false |}.

Definition final_state (s : fstate) (r : int) : Prop :=
  RTL.final_state s.(fs_state) r.

End RELSEM.

Definition faulty_semantics (p : program) :=
  Semantics fstep (initial_state p) final_state (Genv.globalenv p).

Definition rs_compat (rs1 rs2 : regset) : Prop :=
  forall r, val_compat (rs1 # r) (rs2 # r).

(** Pure val_compat lemmas (no global environment dependency) *)

Lemma val_compat_shrx v1 v2 vres n :
  val_compat v1 v2 ->
  Val.shrx v1 (Vint n) = Some vres ->
  exists vres' : val, Val.shrx v2 (Vint n) = Some vres'.
Proof.
  intros Hcompat Hshrx.
  inv Hcompat; simpl in *; try congruence.
  destruct (Integers.Int.ltu _ _); inv Hshrx.
  eexists; reflexivity.
Qed.

Lemma val_compat_shrxl v1 v2 vres n :
  val_compat v1 v2 ->
  Val.shrxl v1 (Vint n) = Some vres ->
  exists vres' : val, Val.shrxl v2 (Vint n) = Some vres'.
Proof.
  intros Hcompat Hshrxl.
  inv Hcompat; simpl in *; try congruence.
  destruct (Integers.Int.ltu _ _); inv Hshrxl.
  eexists; reflexivity.
Qed.

Lemma val_compat_floatofint_exists v1 v2 vres :
  val_compat v1 v2 ->
  Val.floatofint v1 = Some vres ->
  exists vres' : val, Val.floatofint v2 = Some vres'.
Proof.
  intros Hcompat Hfoi.
  inv Hcompat; simpl in *; try congruence.
  eexists; reflexivity.
Qed.

Lemma val_compat_singleofint_exists v1 v2 vres :
  val_compat v1 v2 ->
  Val.singleofint v1 = Some vres ->
  exists vres' : val, Val.singleofint v2 = Some vres'.
Proof.
  intros Hcompat Hsoi.
  inv Hcompat; simpl in *; try congruence.
  eexists; reflexivity.
Qed.

Lemma val_compat_floatoflong_exists v1 v2 vres :
  val_compat v1 v2 ->
  Val.floatoflong v1 = Some vres ->
  exists vres' : val, Val.floatoflong v2 = Some vres'.
Proof.
  intros Hcompat Hfol.
  inv Hcompat; simpl in *; try congruence.
  eexists; reflexivity.
Qed.

Lemma val_compat_singleoflong_exists v1 v2 vres :
  val_compat v1 v2 ->
  Val.singleoflong v1 = Some vres ->
  exists vres' : val, Val.singleoflong v2 = Some vres'.
Proof.
  intros Hcompat Hsol.
  inv Hcompat; simpl in *; try congruence.
  eexists; reflexivity.
Qed.

Lemma val_compat_divs n1 n2 d1 d2 v1 v2 :
  val_compat n1 n2 ->
  val_compat d1 d2 ->
  Val.divs n1 d1 = Some v1 ->
  Val.divs n2 d2 = Some v2 ->
  val_compat v1 v2.
Proof.
  intros Hn Hd Hdiv1 Hdiv2.
  inv Hn; inv Hd; simpl in *; try congruence.
  destruct (Integers.Int.eq _ _); simpl in *; try congruence.
  destruct (Integers.Int.eq _ _); simpl in *; try congruence.
  - destruct (Integers.Int.eq _ _); simpl in *; try congruence.
    inv Hdiv1.
    destruct (Integers.Int.eq _ _); simpl in *; try congruence.
    destruct (Integers.Int.eq _ _); simpl in *; try congruence.
    + destruct (Integers.Int.eq _ _); simpl in *; try congruence.
      inv Hdiv2; constructor.
    + inv Hdiv2; constructor.
  - inv Hdiv1.
    destruct (Integers.Int.eq _ _); simpl in *; try congruence.
    destruct (Integers.Int.eq _ _); simpl in *; try congruence.
    + destruct (Integers.Int.eq _ _); simpl in *; try congruence.
      inv Hdiv2; constructor.
    + inv Hdiv2; constructor.
Qed.

Lemma val_compat_divu n1 n2 d1 d2 v1 v2 :
  val_compat n1 n2 ->
  val_compat d1 d2 ->
  Val.divu n1 d1 = Some v1 ->
  Val.divu n2 d2 = Some v2 ->
  val_compat v1 v2.
Proof.
  intros Hn Hd Hdiv1 Hdiv2.
  inv Hn; inv Hd; simpl in *; try congruence.
  repeat destruct (Integers.Int.eq _ _); simpl in *; try congruence.
  inv Hdiv1; inv Hdiv2; constructor.
Qed.

Lemma val_compat_mods n1 n2 d1 d2 v1 v2 :
  val_compat n1 n2 ->
  val_compat d1 d2 ->
  Val.mods n1 d1 = Some v1 ->
  Val.mods n2 d2 = Some v2 ->
  val_compat v1 v2.
Proof.
  intros Hn Hd Hmod1 Hmod2.
  inv Hn; inv Hd; simpl in *; try congruence.
  destruct (Integers.Int.eq _ _); simpl in *; try congruence.
  destruct (Integers.Int.eq _ _); simpl in *; try congruence.
  - destruct (Integers.Int.eq _ _); simpl in *; try congruence.
    inv Hmod1.
    destruct (Integers.Int.eq _ _); simpl in *; try congruence.
    destruct (Integers.Int.eq _ _); simpl in *; try congruence.
    + destruct (Integers.Int.eq _ _); simpl in *; try congruence.
      inv Hmod2; constructor.
    + inv Hmod2; constructor.
  - inv Hmod1.
    destruct (Integers.Int.eq _ _); simpl in *; try congruence.
    destruct (Integers.Int.eq _ _); simpl in *; try congruence.
    + destruct (Integers.Int.eq _ _); simpl in *; try congruence.
      inv Hmod2; constructor.
    + inv Hmod2; constructor.
Qed.

Lemma val_compat_modu n1 n2 d1 d2 v1 v2 :
  val_compat n1 n2 ->
  val_compat d1 d2 ->
  Val.modu n1 d1 = Some v1 ->
  Val.modu n2 d2 = Some v2 ->
  val_compat v1 v2.
Proof.
  intros Hn Hd Hmod1 Hmod2.
  inv Hn; inv Hd; simpl in *; try congruence.
  repeat destruct (Integers.Int.eq _ _); simpl in *; try congruence.
  inv Hmod1; inv Hmod2; constructor.
Qed.

Lemma val_compat_shl_imm v v' n :
  val_compat v v' ->
  val_compat (Val.shl v (Vint n)) (Val.shl v' (Vint n)).
Proof.
  intros Hcompat; inv Hcompat; simpl; try constructor.
  destruct (Integers.Int.ltu _ _); constructor.
Qed.

Lemma val_compat_shr_imm v v' n :
  val_compat v v' ->
  val_compat (Val.shr v (Vint n)) (Val.shr v' (Vint n)).
Proof.
  intros Hcompat; inv Hcompat; simpl; try constructor.
  destruct (Integers.Int.ltu _ _); constructor.
Qed.

Lemma val_compat_shll_imm v v' n :
  val_compat v v' ->
  val_compat (Val.shll v (Vint n)) (Val.shll v' (Vint n)).
Proof.
  intros Hcompat; inv Hcompat; simpl; try constructor.
  destruct (Integers.Int.ltu _ _); constructor.
Qed.

Lemma val_compat_shrl_imm v v' n :
  val_compat v v' ->
  val_compat (Val.shrl v (Vint n)) (Val.shrl v' (Vint n)).
Proof.
  intros Hcompat; inv Hcompat; simpl; try constructor.
  destruct (Integers.Int.ltu _ _); constructor.
Qed.

Lemma val_compat_shrlu_imm v v' n :
  val_compat v v' ->
  val_compat (Val.shrlu v (Vint n)) (Val.shrlu v' (Vint n)).
Proof.
  intros Hcompat; inv Hcompat; simpl; try constructor.
  destruct (Integers.Int.ltu _ _); constructor.
Qed.

Lemma val_compat_shrx_imm v v' vres vres' n :
  val_compat v v' ->
  Val.shrx v (Vint n) = Some vres ->
  Val.shrx v' (Vint n) = Some vres' ->
  val_compat vres vres'.
Proof.
  intros Hcompat H0 H1; inv Hcompat; simpl in *; try congruence.
  destruct (Integers.Int.ltu _ _); inv H0; inv H1; constructor.
Qed.

Lemma val_compat_shrxl_imm v v' vres vres' n :
  val_compat v v' ->
  Val.shrxl v (Vint n) = Some vres ->
  Val.shrxl v' (Vint n) = Some vres' ->
  val_compat vres vres'.
Proof.
  intros Hcompat H0 H1; inv Hcompat; simpl in *; try congruence.
  destruct (Integers.Int.ltu _ _); inv H0; inv H1; constructor.
Qed.

Lemma val_compat_shru_imm v v' n :
  val_compat v v' ->
  val_compat (Val.shru v (Vint n)) (Val.shru v' (Vint n)).
Proof.
  intros Hcompat; inv Hcompat; simpl; try constructor.
  destruct (Integers.Int.ltu _ _); constructor.
Qed.

Lemma val_compat_shru_dimm v1 v1' v2 v2' n :
  val_compat v1 v1' ->
  val_compat v2 v2' ->
  val_compat
    (Val.or (Val.shl v1 (Vint n))
       (Val.shru v2 (Vint (Integers.Int.sub Integers.Int.iwordsize n))))
    (Val.or (Val.shl v1' (Vint n))
       (Val.shru v2' (Vint (Integers.Int.sub Integers.Int.iwordsize n)))).
Proof.
  intros H0 H1; inv H0; inv H1; simpl; try constructor;
    repeat destruct (Integers.Int.ltu _ _); constructor.
Qed.

Lemma val_compat_add v1 v1' v2 v2' :
  val_compat v1 v1' ->
  val_compat v2 v2' ->
  val_compat (Val.add v1 v2) (Val.add v1' v2').
Proof. intros H0 H1; inv H0; inv H1; constructor. Qed.

Lemma val_compat_addl v1 v1' v2 v2' :
  val_compat v1 v1' ->
  val_compat v2 v2' ->
  val_compat (Val.addl v1 v2) (Val.addl v1' v2').
Proof. intros H0 H1; inv H0; inv H1; constructor. Qed.

Lemma val_compat_mul v1 v1' v2 v2' :
  val_compat v1 v1' ->
  val_compat v2 v2' ->
  val_compat (Val.mul v1 v2) (Val.mul v1' v2').
Proof. intros H0 H1; inv H0; inv H1; constructor. Qed.

Lemma val_compat_mull v1 v1' v2 v2' :
  val_compat v1 v1' ->
  val_compat v2 v2' ->
  val_compat (Val.mull v1 v2) (Val.mull v1' v2').
Proof. intros H0 H1; inv H0; inv H1; constructor. Qed.

Lemma val_compat_floatofint v v' vres vres' :
  val_compat v v' ->
  Val.floatofint v = Some vres ->
  Val.floatofint v' = Some vres' ->
  val_compat vres vres'.
Proof.
  intros Hcompat H0 H1; inv Hcompat; inv H0; inv H1; constructor.
Qed.

Lemma val_compat_singleofint v v' vres vres' :
  val_compat v v' ->
  Val.singleofint v = Some vres ->
  Val.singleofint v' = Some vres' ->
  val_compat vres vres'.
Proof.
  intros Hcompat H0 H1; inv Hcompat; inv H0; inv H1; constructor.
Qed.

Lemma val_compat_floatoflong v v' vres vres' :
  val_compat v v' ->
  Val.floatoflong v = Some vres ->
  Val.floatoflong v' = Some vres' ->
  val_compat vres vres'.
Proof.
  intros Hcompat H0 H1; inv Hcompat; inv H0; inv H1; constructor.
Qed.

Lemma val_compat_singleoflong v v' vres vres' :
  val_compat v v' ->
  Val.singleoflong v = Some vres ->
  Val.singleoflong v' = Some vres' ->
  val_compat vres vres'.
Proof.
  intros Hcompat H0 H1; inv Hcompat; inv H0; inv H1; constructor.
Qed.

Lemma val_compat_cmp_bool c v1 v1' v2 v2' b :
  val_compat v1 v1' ->
  val_compat v2 v2' ->
  Val.cmp_bool c v1 v2 = Some b ->
  exists b' : bool, Val.cmp_bool c v1' v2' = Some b'.
Proof.
  intros H0 H1 Hcmp; inv H0; inv H1; simpl in *; try congruence.
  inv Hcmp; eexists; reflexivity.
Qed.

Lemma val_compat_cmpl_bool c v1 v1' v2 v2' b :
  val_compat v1 v1' ->
  val_compat v2 v2' ->
  Val.cmpl_bool c v1 v2 = Some b ->
  exists b' : bool, Val.cmpl_bool c v1' v2' = Some b'.
Proof.
  intros H0 H1 Hcmp; inv H0; inv H1; simpl in *; try congruence.
  inv Hcmp; eexists; reflexivity.
Qed.

Lemma val_compat_cmpf_bool c v1 v1' v2 v2' b :
  val_compat v1 v1' ->
  val_compat v2 v2' ->
  Val.cmpf_bool c v1 v2 = Some b ->
  exists b' : bool, Val.cmpf_bool c v1' v2' = Some b'.
Proof.
  intros H0 H1 Hcmp; inv H0; inv H1; simpl in *; try congruence.
  inv Hcmp; eexists; reflexivity.
Qed.

Lemma val_compat_cmpfs_bool c v1 v1' v2 v2' b :
  val_compat v1 v1' ->
  val_compat v2 v2' ->
  Val.cmpfs_bool c v1 v2 = Some b ->
  exists b' : bool, Val.cmpfs_bool c v1' v2' = Some b'.
Proof.
  intros H0 H1 Hcmp; inv H0; inv H1; simpl in *; try congruence.
  inv Hcmp; eexists; reflexivity.
Qed.

Lemma val_compat_cmpu_bool c v1 v1' v2 v2' b m1 m2 :
  Archi.ptr64 = true ->
  val_compat v1 v1' ->
  val_compat v2 v2' ->
  Val.cmpu_bool (Memory.Mem.valid_pointer m1) c v1 v2 = Some b ->
  exists b' : bool, Val.cmpu_bool (Memory.Mem.valid_pointer m2) c v1' v2' = Some b'.
Proof.
  intros Harchi H0 H1 Hcmp; inv H0; inv H1; simpl in *; try congruence;
    try (rewrite Harchi in *; discriminate).
  inv Hcmp; eexists; reflexivity.
Qed.

Lemma val_compat_cmplu_bool c v1 v1' v2 v2' b m1 m2 :
  Archi.ptr64 = false ->
  val_compat v1 v1' ->
  val_compat v2 v2' ->
  Val.cmplu_bool (Memory.Mem.valid_pointer m1) c v1 v2 = Some b ->
  exists b' : bool, Val.cmplu_bool (Memory.Mem.valid_pointer m2) c v1' v2' = Some b'.
Proof.
  intros Harchi H0 H1 Hcmp; inv H0; inv H1; simpl in *; try congruence;
    try (rewrite Harchi in *; discriminate).
  inv Hcmp; eexists; reflexivity.
Qed.

Lemma val_compat_cmpu_bool_imm c v v' b m1 m2 n :
  Archi.ptr64 = true ->
  val_compat v v' ->
  Val.cmpu_bool (Memory.Mem.valid_pointer m1) c v (Vint n) = Some b ->
  exists b' : bool, Val.cmpu_bool (Memory.Mem.valid_pointer m2) c v' (Vint n) = Some b'.
Proof.
  intros Harchi H Hcmp; inv H; simpl in *; try congruence;
    try (rewrite Harchi in *; discriminate).
  inv Hcmp; eexists; reflexivity.
Qed.

Lemma val_compat_maskzero_bool v v' n b :
  val_compat v v' ->
  Val.maskzero_bool v n = Some b ->
  exists b', Val.maskzero_bool v' n = Some b'.
Proof.
  intros H Hmask; inv H; simpl in *; try congruence.
  inv Hmask; eexists; reflexivity.
Qed.

Lemma option_map_some {A B : Type} (f : A -> B) o y :
  option_map f o = Some y ->
  exists x, o = Some x /\ y = f x.
Proof.
  intro Hf.
  destruct o; simpl in *; inv Hf.
  eexists; split; reflexivity.
Qed.

Lemma val_compat_normalize v v' t :
  val_compat v v' ->
  val_compat (Val.normalize v t) (Val.normalize v' t).
Proof.
  intro H; inv H; simpl; try constructor; destruct t; constructor.
Qed.

Lemma val_compat_subl v1 v1' v2 v2' :
  Archi.ptr64 = false ->
  val_compat v1 v1' ->
  val_compat v2 v2' ->
  val_compat (Val.subl v1 v2) (Val.subl v1' v2').
Proof.
  intros Harchi H0 H1; inv H0; inv H1; simpl; try constructor.
  rewrite Harchi; constructor.
Qed.

(** Lemmas depending on a global environment *)

Section VAL_COMPAT_OPS.
Variable ge : genv.

Local Ltac inv_Forall2 :=
  repeat match goal with
    | [H : Forall2 _ nil _ |- _] => inv H
    | [H : Forall2 _ _ nil |- _] => inv H
    | [H : Forall2 _ (_ :: _) _ |- _] => inv H
    | [H : Forall2 _ _ (_ :: _) |- _] => inv H
    end.

Lemma val_compat_eval_addressing32 args1 args2 sp a v :
  Forall2 val_compat args1 args2 ->
  Op.eval_addressing32 ge sp a args1 = Some v ->
  exists v', Op.eval_addressing32 ge sp a args2 = Some v'.
Proof.
  intros Hforall Hop.
  destruct a; simpl in *; try congruence;
    try solve [repeat (destruct args1; try congruence);
               destruct Archi.ptr64; inv_Forall2; eexists; eauto].
Qed.

Lemma val_compat_eval_addressing64 args1 args2 sp a v :
  Forall2 val_compat args1 args2 ->
  Op.eval_addressing64 ge sp a args1 = Some v ->
  exists v', Op.eval_addressing64 ge sp a args2 = Some v'.
Proof.
  intros Hforall Hop.
  destruct a; simpl in *; try congruence;
    try solve [repeat (destruct args1; try congruence);
               destruct Archi.ptr64; inv_Forall2; eexists; eauto].
Qed.

Lemma rs_compat_eval_operation rs1 rs2 sp op args m v :
  ~ is_protected op ->
  rs_compat rs1 rs2 ->
  Op.eval_operation ge sp op rs1 ## args m = Some v ->
  exists v', Op.eval_operation ge sp op rs2 ## args m = Some v'.
Proof.
  intros Hnodiv Hcompat Hop.
  destruct op; simpl in *;
    try (destruct args; simpl in *; try congruence);
    try (destruct args; simpl in *; try congruence);
    try (destruct args; simpl in *; try congruence);
    inv Hop; try solve [eexists; eauto];
    try solve [exfalso; apply Hnodiv; constructor].
  - eapply val_compat_shrx; eauto.
  - eapply val_compat_eval_addressing32; eauto.
  - eapply val_compat_eval_addressing32; eauto.
  - eapply val_compat_shrxl; eauto.
  - eapply val_compat_eval_addressing64; eauto.
  - eapply val_compat_eval_addressing64; eauto.
  - eapply val_compat_floatofint_exists; eauto.
  - eapply val_compat_singleofint_exists; eauto.
  - eapply val_compat_floatoflong_exists; eauto.
  - eapply val_compat_singleoflong_exists; eauto.
Qed.

Lemma rs_compat_eval_addressing32 rs1 rs2 args sp a v v' :
  rs_compat rs1 rs2 ->
  Op.eval_addressing32 ge sp a rs1 ## args = Some v ->
  Op.eval_addressing32 ge sp a rs2 ## args = Some v' ->
  val_compat v v'.
Proof.
  intros Hcompat H0 H1.
  unfold Op.eval_addressing32 in *.
  destruct a; simpl in *.
  - do 2 (destruct args; simpl in *; try congruence).
    inv H0; inv H1; apply val_compat_add; auto; constructor.
  - do 3 (destruct args; simpl in *; try congruence).
    inv H0; inv H1; apply val_compat_add; try constructor.
    apply val_compat_add; auto.
  - do 2 (destruct args; simpl in *; try congruence).
    inv H0; inv H1; apply val_compat_add; try constructor.
    apply val_compat_mul; auto; constructor.
  - do 3 (destruct args; simpl in *; try congruence).
    inv H0; inv H1; apply val_compat_add; auto.
    apply val_compat_add; try constructor.
    apply val_compat_mul; auto; constructor.
  - do 1 (destruct args; simpl in *; try congruence).
    destruct Archi.ptr64; try congruence.
    inv H0; inv H1; apply val_compat_refl.
  - do 2 (destruct args; simpl in *; try congruence).
    destruct Archi.ptr64; try congruence.
    inv H0; inv H1; apply val_compat_add; auto; apply val_compat_refl.
  - do 2 (destruct args; simpl in *; try congruence).
    destruct Archi.ptr64; try congruence.
    inv H0; inv H1.
    apply val_compat_add; try apply val_compat_refl.
    apply val_compat_mul; auto; constructor.
  - do 1 (destruct args; simpl in *; try congruence).
    destruct Archi.ptr64; try congruence.
    inv H0; inv H1; apply val_compat_refl.
Qed.

Lemma rs_compat_eval_addressing64 rs1 rs2 args sp a v v' :
  rs_compat rs1 rs2 ->
  Op.eval_addressing64 ge sp a rs1 ## args = Some v ->
  Op.eval_addressing64 ge sp a rs2 ## args = Some v' ->
  val_compat v v'.
Proof.
  intros Hcompat H0 H1.
  unfold Op.eval_addressing32 in *.
  destruct a; simpl in *; try congruence.
  - do 2 (destruct args; simpl in *; try congruence).
    inv H0; inv H1; apply val_compat_addl; auto; constructor.
  - do 3 (destruct args; simpl in *; try congruence).
    inv H0; inv H1; apply val_compat_addl; try constructor.
    apply val_compat_addl; auto.
  - do 2 (destruct args; simpl in *; try congruence).
    inv H0; inv H1; apply val_compat_addl; try constructor.
    apply val_compat_mull; auto; constructor.
  - do 3 (destruct args; simpl in *; try congruence).
    inv H0; inv H1; apply val_compat_addl; auto.
    apply val_compat_addl; try constructor.
    apply val_compat_mull; auto; constructor.
  - do 1 (destruct args; simpl in *; try congruence).
    destruct Archi.ptr64; try congruence.
    inv H0; inv H1; apply val_compat_refl.
  - do 1 (destruct args; simpl in *; try congruence).
    destruct Archi.ptr64; try congruence.
    inv H0; inv H1; apply val_compat_refl.
Qed.

Lemma rs_compat_eval_condition cond rs1 rs2 args m1 m2 v :
  (Archi.ptr64 = false -> ~ is_compu cond) ->
  (Archi.ptr64 = true -> ~ is_complu cond) ->
  rs_compat rs1 rs2 ->
  Op.eval_condition cond rs1 ## args m1 = Some v ->
  exists v', Op.eval_condition cond rs2 ## args m2 = Some v'.
Proof.
  intros Hnotcompu Hnotcomplu Hcompat Hcond.
  destruct cond eqn:Hc; simpl in *.
  - do 3 (destruct args; simpl in *; try congruence).
    eapply val_compat_cmp_bool; eauto.
  - do 3 (destruct args; simpl in *; try congruence).
    destruct Archi.ptr64 eqn:Harchi.
    + eapply val_compat_cmpu_bool; eauto.
    + exfalso; eapply Hnotcompu; constructor.
  - do 2 (destruct args; simpl in *; try congruence).
    eapply val_compat_cmp_bool; eauto; constructor.
  - do 2 (destruct args; simpl in *; try congruence).
    destruct Archi.ptr64 eqn:Harchi.
    + eapply val_compat_cmpu_bool; eauto; constructor.
    + exfalso; eapply Hnotcompu; constructor.
  - do 3 (destruct args; simpl in *; try congruence).
    eapply val_compat_cmpl_bool; eauto.
  - do 3 (destruct args; simpl in *; try congruence).
    destruct Archi.ptr64 eqn:Harchi.
    + exfalso; apply Hnotcomplu; auto; constructor.
    + eapply val_compat_cmplu_bool; eauto; constructor.
  - do 2 (destruct args; simpl in *; try congruence).
    eapply val_compat_cmpl_bool; eauto; constructor.
  - do 2 (destruct args; simpl in *; try congruence).
    destruct Archi.ptr64 eqn:Harchi.
    + exfalso; apply Hnotcomplu; auto; constructor.
    + eapply val_compat_cmplu_bool; eauto; constructor.
  - do 3 (destruct args; simpl in *; try congruence).
    eapply val_compat_cmpf_bool; eauto.
  - do 3 (destruct args; simpl in *; try congruence).
    apply option_map_some in Hcond.
    destruct Hcond as (b & Hcmp & Hb); subst.
    eapply val_compat_cmpf_bool in Hcmp; eauto.
    destruct Hcmp as [b' Hcmp].
    exists (negb b'); rewrite Hcmp; reflexivity.
  - do 3 (destruct args; simpl in *; try congruence).
    eapply val_compat_cmpfs_bool; eauto.
  - do 3 (destruct args; simpl in *; try congruence).
    apply option_map_some in Hcond.
    destruct Hcond as (b & Hcmp & Hb); subst.
    eapply val_compat_cmpfs_bool in Hcmp; eauto.
    destruct Hcmp as [b' Hcmp].
    exists (negb b'); rewrite Hcmp; reflexivity.
  - do 2 (destruct args; simpl in *; try congruence).
    eapply val_compat_maskzero_bool; eauto.
  - do 2 (destruct args; simpl in *; try congruence).
    apply option_map_some in Hcond.
    destruct Hcond as (b & Hcmp & Hb); subst.
    eapply val_compat_maskzero_bool in Hcmp; eauto.
    destruct Hcmp as [b' Hcmp].
    exists (negb b'); rewrite Hcmp; reflexivity.
Qed.

Lemma eval_operation_val_compat rs1 rs2 sp op args m1 m2 v v' :
  ~ is_protected op ->
  rs_compat rs1 rs2 ->
  Op.eval_operation ge sp op rs1 ## args m1 = Some v ->
  Op.eval_operation ge sp op rs2 ## args m2 = Some v' ->
  val_compat v v'.
Proof.
  intros Hop Hcompat H0 H1.
  destruct op; simpl in *;
    try solve [exfalso; apply Hop; constructor];
    try solve [destruct args; simpl in *; try congruence;
               try solve [inv H0; inv H1; constructor];
               try solve [inv H0; inv H1; apply val_compat_refl];
               destruct args; simpl in *; try congruence;
               inv H0; inv H1; auto];
    try solve [do 2 (destruct args; simpl in *; try congruence);
               inv H0; inv H1;
               specialize (Hcompat p); inv Hcompat; simpl;
               try apply val_compat_refl; constructor];
    try solve [do 3 (destruct args; simpl in *; try congruence);
               inv H0; inv H1;
               pose proof (Hcompat p0) as Hp0; specialize (Hcompat p);
               inv Hp0; inv Hcompat; constructor].
  - do 2 (destruct args; simpl in *; try congruence).
    inv H0; inv H1; apply val_compat_shl_imm; auto.
  - do 2 (destruct args; simpl in *; try congruence).
    inv H0; inv H1; apply val_compat_shr_imm; auto.
  - do 2 (destruct args; simpl in *; try congruence).
    eapply val_compat_shrx_imm; eauto.
  - do 2 (destruct args; simpl in *; try congruence).
    inv H0; inv H1; apply val_compat_shru_imm; auto.
  - do 3 (destruct args; simpl in *; try congruence).
    inv H0; inv H1; apply val_compat_shru_dimm; auto.
  - eapply rs_compat_eval_addressing32; eauto.
  - do 3 (destruct args; simpl in *; try congruence).
    inv H0; inv H1.
    apply val_compat_subl; auto.
    apply is_protected_subl_archi_ptr64_false; assumption.
  - do 2 (destruct args; simpl in *; try congruence).
    inv H0; inv H1; apply val_compat_shll_imm; auto.
  - do 2 (destruct args; simpl in *; try congruence).
    inv H0; inv H1; apply val_compat_shrl_imm; auto.
  - do 2 (destruct args; simpl in *; try congruence).
    eapply val_compat_shrxl_imm; eauto.
  - do 2 (destruct args; simpl in *; try congruence).
    inv H0; inv H1; apply val_compat_shrlu_imm; auto.
  - eapply rs_compat_eval_addressing64; eauto.
  - do 2 (destruct args; simpl in *; try congruence).
    eapply val_compat_floatofint; eauto.
  - do 2 (destruct args; simpl in *; try congruence).
    eapply val_compat_singleofint; eauto.
  - do 2 (destruct args; simpl in *; try congruence).
    eapply val_compat_floatoflong; eauto.
  - do 2 (destruct args; simpl in *; try congruence).
    eapply val_compat_singleoflong; eauto.
  - inv H0; inv H1.
    destruct (Op.eval_condition cond rs1 ## args m1) eqn:Hcond.
    + eapply rs_compat_eval_condition in Hcond; eauto.
      * destruct Hcond as [b' Hcond].
        rewrite Hcond; simpl.
        destruct b, b'; constructor.
      * intros Harchi HC; inv HC; apply Hop; constructor; assumption.
      * intros Harchi HC; inv HC; apply Hop; constructor; assumption.
    + constructor.
Qed.

End VAL_COMPAT_OPS.
