Require Import
  AST
  Builtins
  SharedFaultPolicy
  FaultPolicy
  CompCertZapUtils
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
  | Ibuiltin ef _ _ _ => builtin_can_fault ef = true
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

(* Tojo@riverside *)
Lemma val_compat_floatofintu_exists v1 v2 vres :
  val_compat v1 v2 ->
  Val.floatofintu v1 = Some vres ->
  exists vres' : val, Val.floatofintu v2 = Some vres'.
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

(* Tojo@riverside *)
Lemma val_compat_singleofintu_exists v1 v2 vres :
  val_compat v1 v2 ->
  Val.singleofintu v1 = Some vres ->
  exists vres' : val, Val.singleofintu v2 = Some vres'.
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

(* Tojo@riverside *)
Lemma val_compat_floatoflongu_exists v1 v2 vres :
  val_compat v1 v2 ->
  Val.floatoflongu v1 = Some vres ->
  exists vres' : val, Val.floatoflongu v2 = Some vres'.
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

(* Tojo@riverside *)
Lemma val_compat_singleoflongu_exists v1 v2 vres :
  val_compat v1 v2 ->
  Val.singleoflongu v1 = Some vres ->
  exists vres' : val, Val.singleoflongu v2 = Some vres'.
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
Proof. intros H0 H1; inv H0; inv H1; try constructor; try simpl;
 repeat destruct Archi.ptr64 eqn:Harchi; repeat constructor; simpl.
Qed.

Lemma val_compat_addl v1 v1' v2 v2' :
  val_compat v1 v1' ->
  val_compat v2 v2' ->
  val_compat (Val.addl v1 v2) (Val.addl v1' v2').
Proof. intros H0 H1; inv H0; inv H1; try constructor; try simpl; repeat destruct Archi.ptr64 eqn:Harchi; repeat constructor; simpl.
Qed.


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

(* Tojo@riverside *)
Lemma val_compat_floatofintu v v' vres vres' :
  val_compat v v' ->
  Val.floatofintu v = Some vres ->
  Val.floatofintu v' = Some vres' ->
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

(* Tojo@riverside *)
Lemma val_compat_singleofintu v v' vres vres' :
  val_compat v v' ->
  Val.singleofintu v = Some vres ->
  Val.singleofintu v' = Some vres' ->
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

(* Tojo@riverside *)
Lemma val_compat_floatoflongu v v' vres vres' :
  val_compat v v' ->
  Val.floatoflongu v = Some vres ->
  Val.floatoflongu v' = Some vres' ->
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

(* Tojo@riverside *)
Lemma val_compat_singleoflongu v v' vres vres' :
  val_compat v v' ->
  Val.singleoflongu v = Some vres ->
  Val.singleoflongu v' = Some vres' ->
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

(* Tojo@riverside *)
Lemma val_compat_offset_ptr :
  forall v1 v2 delta,
    val_compat v1 v2 ->
    val_compat (Val.offset_ptr v1 delta) (Val.offset_ptr v2 delta).
Proof.
  intros; inv H; simpl in *; try congruence; constructor.
Qed.

Lemma val_compat_normalize v v' t :
  val_compat v v' ->
  val_compat (Val.normalize v t) (Val.normalize v' t).
Proof.
  intro H; inv H; simpl; try constructor; try destruct t; try constructor; try simpl; repeat destruct Archi.ptr64 eqn:Harchi; repeat constructor.
Qed.

(* vals are compatible when Archi.ptr64 = false. Val.subl does not
perform pointer subtraction; it returns Vundef for pointer cases
   that is when Archi.ptr64 = false *)
Lemma val_compat_subl v1 v1' v2 v2' :
  Archi.ptr64 = false ->
  val_compat v1 v1' ->
  val_compat v2 v2' ->
  val_compat (Val.subl v1 v2) (Val.subl v1' v2').
Proof.
  intros Harchi H0 H1; inv H0; inv H1; simpl; try constructor; try simpl;
  rewrite Harchi; constructor. 
Qed.


(* vals are compatible when Archi.ptr64 = true. Val.sub does not
perform pointer subtraction; it return Vundef for pointer cases
   that is when Archi.ptr64 = true *)
Lemma val_compat_sub v1 v1' v2 v2' :
  Archi.ptr64 = true ->
  val_compat v1 v1' ->
  val_compat v2 v2' ->
  val_compat (Val.sub v1 v2) (Val.sub v1' v2').
Proof.
  intros Harchi H0 H1; inv H0; inv H1; simpl; try constructor;
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

(* Lemma val_compat_eval_addressing32 args1 args2 sp a v : *)
(*   Forall2 val_compat args1 args2 -> *)
(*   Op.eval_addressing32 ge sp a args1 = Some v -> *)
(*   exists v', Op.eval_addressing32 ge sp a args2 = Some v'. *)
(* Proof. *)
(*   intros Hforall Hop. *)
(*   destruct a; simpl in *; try congruence; *)
(*     try solve [repeat (destruct args1; try congruence); *)
(*                destruct Archi.ptr64; inv_Forall2; eexists; eauto]. *)
(* Qed. *)

Lemma val_compat_eval_addressing args1 args2 sp a v :
  Forall2 val_compat args1 args2 ->
  Op.eval_addressing ge sp a args1 = Some v ->
  exists v', Op.eval_addressing ge sp a args2 = Some v'.
Proof.
  intros Hforall Hop.
  destruct a; simpl in *; try congruence;
    try solve [repeat (destruct args1; try congruence);
               destruct Archi.ptr64; inv_Forall2; eexists; eauto].
Qed.

(* Lemma val_compat_eval_addressing64 args1 args2 sp a v : *)
(*   Forall2 val_compat args1 args2 -> *)
(*                destruct Archi.ptr64; inv_Forall2; eexists; eauto]. *)
(* Qed. *)

(* Lemma rs_compat_eval_operation rs1 rs2 sp op args m v : *)
(*   ~ is_protected op -> *)
(*   rs_compat rs1 rs2 -> *)
(*   Op.eval_operation ge sp op rs1 ## args m = Some v -> *)
(*   exists v', Op.eval_operation ge sp op rs2 ## args m = Some v'. *)
(* Proof. *)
(*   intros Hnodiv Hcompat Hop. *)
(*   destruct op; simpl in *; *)
(*     try (destruct args; simpl in *; try congruence); *)
(*     try (destruct args; simpl in *; try congruence); *)
(*     try (destruct args; simpl in *; try congruence); *)
(*     inv Hop; try solve [eexists; eauto]; *)
(*     try solve [exfalso; apply Hnodiv; constructor]. *)
(*   - eapply val_compat_shrx; eauto. *)
(*   - eapply val_compat_eval_addressing32; eauto. *)
(*   - eapply val_compat_eval_addressing32; eauto. *)
(*   - eapply val_compat_shrxl; eauto. *)
(*   - eapply val_compat_eval_addressing64; eauto. *)
(*   - eapply val_compat_eval_addressing64; eauto. *)
(*   - eapply val_compat_floatofint_exists; eauto. *)
(*   - eapply val_compat_singleofint_exists; eauto. *)
(*   - eapply val_compat_floatoflong_exists; eauto. *)
(*   - eapply val_compat_singleoflong_exists; eauto. *)
(* Qed. *)

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
  - eapply val_compat_shrxl; eauto.
  - eapply val_compat_floatofint_exists; eauto.
  - eapply val_compat_floatofintu_exists; eauto.
  - eapply val_compat_singleofint_exists; eauto.
  - eapply val_compat_singleofintu_exists; eauto.
  - eapply val_compat_floatoflong_exists; eauto.
  - eapply val_compat_floatoflongu_exists; eauto.
  - eapply val_compat_singleoflong_exists; eauto.
  - eapply val_compat_singleoflongu_exists; eauto.
Qed.


(* Lemma rs_compat_eval_addressing32 rs1 rs2 args sp a v v' : *)
(*   rs_compat rs1 rs2 -> *)
(*   Op.eval_addressing32 ge sp a rs1 ## args = Some v -> *)
(*   Op.eval_addressing32 ge sp a rs2 ## args = Some v' -> *)
(*   val_compat v v'. *)
(* Proof. *)
(*   intros Hcompat H0 H1. *)
(*   unfold Op.eval_addressing32 in *. *)
(*   destruct a; simpl in *. *)
(*   - do 2 (destruct args; simpl in *; try congruence). *)
(*     inv H0; inv H1; apply val_compat_add; auto; constructor. *)
(*   - do 3 (destruct args; simpl in *; try congruence). *)
(*     inv H0; inv H1; apply val_compat_add; try constructor. *)
(*     apply val_compat_add; auto. *)
(*   - do 2 (destruct args; simpl in *; try congruence). *)
(*     inv H0; inv H1; apply val_compat_add; try constructor. *)
(*     apply val_compat_mul; auto; constructor. *)
(*   - do 3 (destruct args; simpl in *; try congruence). *)
(*     inv H0; inv H1; apply val_compat_add; auto. *)
(*     apply val_compat_add; try constructor. *)
(*     apply val_compat_mul; auto; constructor. *)
(*   - do 1 (destruct args; simpl in *; try congruence). *)
(*     destruct Archi.ptr64; try congruence. *)
(*     inv H0; inv H1; apply val_compat_refl. *)
(*   - do 2 (destruct args; simpl in *; try congruence). *)
(*     destruct Archi.ptr64; try congruence. *)
(*     inv H0; inv H1; apply val_compat_add; auto; apply val_compat_refl. *)
(*   - do 2 (destruct args; simpl in *; try congruence). *)
(*     destruct Archi.ptr64; try congruence. *)
(*     inv H0; inv H1. *)
(*     apply val_compat_add; try apply val_compat_refl. *)
(*     apply val_compat_mul; auto; constructor. *)
(*   - do 1 (destruct args; simpl in *; try congruence). *)
(*     destruct Archi.ptr64; try congruence. *)
(*     inv H0; inv H1; apply val_compat_refl. *)
(* Qed. *)

(* Lemma rs_compat_eval_addressing32 rs1 rs2 args sp a v v' : *)
(*   rs_compat rs1 rs2 -> *)
(*   Op.eval_addressing ge sp a rs1 ## args = Some v -> *)
(*   Op.eval_addressing ge sp a rs2 ## args = Some v' -> *)
(*   val_compat v v'. *)
(* Proof. *)
(*   intros Hcompat H0 H1. *)
(*   unfold Op.eval_addressing in *. *)
(*   destruct a; simpl in *. *)
(*   - do 2 (destruct args; simpl in *; try congruence). *)
(*     inv H0; inv H1; apply val_compat_add; auto; constructor. *)
(*   - do 3 (destruct args; simpl in *; try congruence). *)
(*     inv H0; inv H1; apply val_compat_add; auto. *)
(*   - do 1 (destruct args; simpl in *; try congruence). *)
(*     inv H0; inv H1. admit. *)
(*     (1* inv H0; inv H1; apply val_compat_add; try constructor. *1) *)
(*     (1* apply val_compat_mul; auto; constructor. *1) *)
(*   - do 2 (destruct args; simpl in *; try congruence). *)
(*     admit. *)
(*     (1* inv H0; inv H1; apply val_compat_add; auto. *1) *)
(*     (1* apply val_compat_add; try constructor. *1) *)
(*     (1* apply val_compat_mul; auto; constructor. *1) *)
(*   - do 1 (destruct args; simpl in *; try congruence). *)
(*     destruct Archi.ptr64; try congruence. *)
(*     inv H0; inv H1; apply val_compat_refl. *)
(*     admit. *)
(*   - do 2 (destruct args; simpl in *; try congruence). *)
(*     destruct Archi.ptr64; try congruence. *)
(*     inv H0; inv H1; apply val_compat_add; auto; apply val_compat_refl. *)
(*   - do 2 (destruct args; simpl in *; try congruence). *)
(*     destruct Archi.ptr64; try congruence. *)
(*     inv H0; inv H1. *)
(*     apply val_compat_add; try apply val_compat_refl. *)
(*     apply val_compat_mul; auto; constructor. *)
(*   - do 1 (destruct args; simpl in *; try congruence). *)
(*     destruct Archi.ptr64; try congruence. *)
(*     inv H0; inv H1; apply val_compat_refl. *)
(* Qed. *)

(* Lemma rs_compat_eval_addressing64 rs1 rs2 args sp a v v' : *)
(*   rs_compat rs1 rs2 -> *)
(*   Op.eval_addressing64 ge sp a rs1 ## args = Some v -> *)
(*   Op.eval_addressing64 ge sp a rs2 ## args = Some v' -> *)
(*   val_compat v v'. *)
(* Proof. *)
(*   intros Hcompat H0 H1. *)
(*   unfold Op.eval_addressing32 in *. *)
(*   destruct a; simpl in *; try congruence. *)
(*   - do 2 (destruct args; simpl in *; try congruence). *)
(*     inv H0; inv H1; apply val_compat_addl; auto; constructor. *)
(*   - do 3 (destruct args; simpl in *; try congruence). *)
(*     inv H0; inv H1; apply val_compat_addl; try constructor. *)
(*     apply val_compat_addl; auto. *)
(*   - do 2 (destruct args; simpl in *; try congruence). *)
(*     inv H0; inv H1; apply val_compat_addl; try constructor. *)
(*     apply val_compat_mull; auto; constructor. *)
(*   - do 3 (destruct args; simpl in *; try congruence). *)
(*     inv H0; inv H1; apply val_compat_addl; auto. *)
(*     apply val_compat_addl; try constructor. *)
(*     apply val_compat_mull; auto; constructor. *)
(*   - do 1 (destruct args; simpl in *; try congruence). *)
(*     destruct Archi.ptr64; try congruence. *)
(*     inv H0; inv H1; apply val_compat_refl. *)
(*   - do 1 (destruct args; simpl in *; try congruence). *)
(*     destruct Archi.ptr64; try congruence. *)
(*     inv H0; inv H1; apply val_compat_refl. *)
(* Qed. *)

 (* PPC *) 
Lemma rs_compat_eval_addressing rs1 rs2 args sp a v v' :
  rs_compat rs1 rs2 ->
  Op.eval_addressing ge sp a rs1 ## args = Some v ->
  Op.eval_addressing ge sp a rs2 ## args = Some v' ->
  val_compat v v'.
Proof.
  intros Hcompat H0 H1.
  unfold Op.eval_addressing in *.
  destruct a; simpl in *; try congruence.
  - do 2 (destruct args; simpl in *; try congruence).
    inv H0; inv H1; apply val_compat_offset_ptr; try constructor; auto.
  - do 1 (destruct args; simpl in *; try congruence).
    inv H0; inv H1. apply val_compat_refl; try constructor; auto.
  - do 1 (destruct args; simpl in *; try congruence).
    inv H0; inv H1; try constructor; apply val_compat_refl.
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
    eapply val_compat_cmplu_bool; eauto.
    inv Hcond.
    destruct Archi.ptr64.
    + exfalso. apply Hnotcomplu.
       ++ reflexivity.
       ++ constructor.
    + reflexivity.
  - do 2 (destruct args; simpl in *; try congruence).
    eapply val_compat_cmpl_bool; eauto; constructor.
  - do 2 (destruct args; simpl in *; try congruence).
    eapply val_compat_cmplu_bool; eauto; try constructor.
    + destruct Archi.ptr64.
      ++ exfalso. apply Hnotcomplu.
         +++ reflexivity.
         +++ constructor.
      ++ reflexivity.
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
Qed.


(* Lemma rs_compat_eval_condition cond rs1 rs2 args m1 m2 v : *)
(*   (Archi.ptr64 = false -> ~ is_compu cond) -> *)
(*   (Archi.ptr64 = true -> ~ is_complu cond) -> *)
(*   rs_compat rs1 rs2 -> *)
(*   Op.eval_condition cond rs1 ## args m1 = Some v -> *)
(*   exists v', Op.eval_condition cond rs2 ## args m2 = Some v'. *)
(* Proof. *)
(*   intros Hnotcompu Hnotcomplu Hcompat Hcond. *)
(*   destruct cond eqn:Hc; simpl in *. *)
(*   - do 3 (destruct args; simpl in *; try congruence). *)
(*     eapply val_compat_cmp_bool; eauto. *)
(*   - do 3 (destruct args; simpl in *; try congruence). *)
(*     destruct Archi.ptr64 eqn:Harchi. *)
(*     + eapply val_compat_cmpu_bool; eauto. *)
(*     + exfalso; eapply Hnotcompu; constructor. *)
(*   - do 2 (destruct args; simpl in *; try congruence). *)
(*     eapply val_compat_cmp_bool; eauto; constructor. *)
(*   - do 2 (destruct args; simpl in *; try congruence). *)
(*     destruct Archi.ptr64 eqn:Harchi. *)
(*     + eapply val_compat_cmpu_bool; eauto; constructor. *)
(*     + exfalso; eapply Hnotcompu; constructor. *)
(*   - do 3 (destruct args; simpl in *; try congruence). *)
(*     eapply val_compat_cmpl_bool; eauto. *)
(*   - do 3 (destruct args; simpl in *; try congruence). *)
(*     destruct Archi.ptr64 eqn:Harchi. *)
(*     + exfalso; apply Hnotcomplu; auto; constructor. *)
(*     + eapply val_compat_cmplu_bool; eauto; constructor. *)
(*   - do 2 (destruct args; simpl in *; try congruence). *)
(*     eapply val_compat_cmpl_bool; eauto; constructor. *)
(*   - do 2 (destruct args; simpl in *; try congruence). *)
(*     destruct Archi.ptr64 eqn:Harchi. *)
(*     + exfalso; apply Hnotcomplu; auto; constructor. *)
(*     + eapply val_compat_cmplu_bool; eauto; constructor. *)
(*   - do 3 (destruct args; simpl in *; try congruence). *)
(*     eapply val_compat_cmpf_bool; eauto. *)
(*   - do 3 (destruct args; simpl in *; try congruence). *)
(*     apply option_map_some in Hcond. *)
(*     destruct Hcond as (b & Hcmp & Hb); subst. *)
(*     eapply val_compat_cmpf_bool in Hcmp; eauto. *)
(*     destruct Hcmp as [b' Hcmp]. *)
(*     exists (negb b'); rewrite Hcmp; reflexivity. *)
(*   - do 3 (destruct args; simpl in *; try congruence). *)
(*     eapply val_compat_cmpfs_bool; eauto. *)
(*   - do 3 (destruct args; simpl in *; try congruence). *)
(*     apply option_map_some in Hcond. *)
(*     destruct Hcond as (b & Hcmp & Hb); subst. *)
(*     eapply val_compat_cmpfs_bool in Hcmp; eauto. *)
(*     destruct Hcmp as [b' Hcmp]. *)
(*     exists (negb b'); rewrite Hcmp; reflexivity. *)
(*   - do 2 (destruct args; simpl in *; try congruence). *)
(*     eapply val_compat_maskzero_bool; eauto. *)
(*   - do 2 (destruct args; simpl in *; try congruence). *)
(*     apply option_map_some in Hcond. *)
(*     destruct Hcond as (b & Hcmp & Hb); subst. *)
(*     eapply val_compat_maskzero_bool in Hcmp; eauto. *)
(*     destruct Hcmp as [b' Hcmp]. *)
(*     exists (negb b'); rewrite Hcmp; reflexivity. *)
(* Qed. *)

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
     - do 3 (destruct args; simpl in *; try congruence).
       inv H0; inv H1; eapply val_compat_add; eauto.
     - do 2 (destruct args; simpl in *; try congruence).
       inv H0; inv H1; apply val_compat_add; auto. apply val_compat_refl.
     - do 3 (destruct args; simpl in *; try congruence).
       inv H0; inv H1; apply val_compat_sub; auto. 
       apply is_protected_sub_archi_ptr64_true. assumption.
     - do 2 (destruct args; simpl in *; try congruence).
       inv H0; inv H1; apply val_compat_shl_imm; auto.
     - do 2 (destruct args; simpl in *; try congruence).
       inv H0; inv H1; apply val_compat_shr_imm; auto.
     - do 2 (destruct args; simpl in *; try congruence).
       inv H0; inv H1; apply val_compat_shru_imm; auto.
     - do 2 (destruct args; simpl in *; try congruence).
       inv H0; inv H1; eapply val_compat_shrx_imm; eauto.
     - do 3 (destruct args; simpl in *; try congruence).
       inv H0; inv H1; eapply val_compat_addl; eauto.
     - do 2 (destruct args; simpl in *; try congruence).
       inv H0; inv H1; eapply val_compat_addl; eauto.
       apply val_compat_refl.
     - do 3 (destruct args; simpl in *; try congruence).
       inv H0; inv H1; eapply val_compat_subl; eauto.
       apply is_protected_subl_archi_ptr64_false; assumption.
     - do 2 (destruct args; simpl in *; try congruence).
       inv H0; inv H1; eapply val_compat_shll_imm; eauto.
     - do 2 (destruct args; simpl in *; try congruence).
       inv H0; inv H1; eapply val_compat_shrl_imm; eauto.
     - do 2 (destruct args; simpl in *; try congruence).
       inv H0; inv H1; eapply val_compat_shrlu_imm; eauto.
     - do 2 (destruct args; simpl in *; try congruence).
       inv H0; inv H1; eapply val_compat_shrxl_imm; eauto.
     - do 2 (destruct args; simpl in *; try congruence).
       inv H0; inv H1; eapply val_compat_floatofint; eauto.
     - do 2 (destruct args; simpl in *; try congruence).
       inv H0; inv H1; eapply val_compat_floatofintu; eauto.
     - do 2 (destruct args; simpl in *; try congruence).
       inv H0; inv H1; eapply val_compat_singleofint; eauto.
     - do 2 (destruct args; simpl in *; try congruence).
       inv H0; inv H1; eapply val_compat_singleofintu; eauto.
     - do 2 (destruct args; simpl in *; try congruence).
       inv H0; inv H1; eapply val_compat_floatoflong; eauto.
     - do 2 (destruct args; simpl in *; try congruence).
       inv H0; inv H1; eapply val_compat_floatoflongu; eauto.
     - do 2 (destruct args; simpl in *; try congruence).
       inv H0; inv H1; eapply val_compat_singleoflong; eauto.
     - do 2 (destruct args; simpl in *; try congruence).
       inv H0; inv H1; eapply val_compat_singleoflongu; eauto.
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
          
       (* inv H0; inv H1; *)
       (* apply val_compat_add; auto. apply val_compat_refl. *)
       (* (1* apply val_compat_sub; auto. *1) *) 
       (* (1* apply is_protected_sub_archi_ptr64_false; assumption. *1) *)
     (* - do 3 (destruct args; simpl in *; try congruence). *)
       (* inv H0; inv H1; apply val_compat_sub; auto. exfalso. apply Hop. *)
       (* constructor. *)
       (* (1* inv H0; inv H1; apply val_compat_shr_imm; auto. *1) *)
     (* - do 2 (destruct args; simpl in *; try congruence). *)
       (* inv H0; inv H1. eapply val_compat_shrx_imm; eauto. *)
     (* - do 2 (destruct args; simpl in *; try congruence). *)
       (* inv H0; inv H1; apply val_compat_shrl_imm; auto. *)
     (* - do 2 (destruct args; simpl in *; try congruence). *)
       (* inv H0; inv H1; eapply val_compat_shrxl_imm; eauto. *)
     (* - do 2 (destruct args; simpl in *; try congruence). *)
       (* inv H0; inv H1; eapply val_compat_floatoflong; eauto. *)
     (* - inv H0; inv H1. *)
       (* destruct (Op.eval_condition c rs1 ## args m1) eqn:Hcond. *)
       (* + eapply rs_compat_eval_condition in Hcond; eauto. *)
       (*   * destruct Hcond as [b' Hcond]. *)
       (*     rewrite Hcond; simpl. *)
       (*     destruct b, b'; constructor. *)
       (*   * intros Harchi HC; inv HC; apply Hop; constructor; assumption. *)
       (*   * intros Harchi HC; inv HC; apply Hop; constructor; assumption. *)
       (* + constructor. *)
(* Qed. *)

(* Lemma eval_operation_val_compat rs1 rs2 sp op args m1 m2 v v' : *)
(*   ~ is_protected op -> *)
(*   rs_compat rs1 rs2 -> *)
(*   Op.eval_operation ge sp op rs1 ## args m1 = Some v -> *)
(*   Op.eval_operation ge sp op rs2 ## args m2 = Some v' -> *)
(*   val_compat v v'. *)
(* Proof. *)
(*   intros Hop Hcompat H0 H1. *)
(*   destruct op; simpl in *; *)
(*     try solve [exfalso; apply Hop; constructor]; *)
(*     try solve [destruct args; simpl in *; try congruence; *)
(*                try solve [inv H0; inv H1; constructor]; *)
(*                try solve [inv H0; inv H1; apply val_compat_refl]; *)
(*                destruct args; simpl in *; try congruence; *)
(*                inv H0; inv H1; auto]; *)
(*     try solve [do 2 (destruct args; simpl in *; try congruence); *)
(*                inv H0; inv H1; *)
(*                specialize (Hcompat p); inv Hcompat; simpl; *)
(*                try apply val_compat_refl; constructor]; *)
(*     try solve [do 3 (destruct args; simpl in *; try congruence); *)
(*                inv H0; inv H1; *)
(*                pose proof (Hcompat p0) as Hp0; specialize (Hcompat p); *)
(*                inv Hp0; inv Hcompat; constructor]. *)
  (* - do 2 (destruct args; simpl in *; try congruence). *)
  (*   inv H0; inv H1; apply val_compat_shl_imm; auto. *)
  (* - do 2 (destruct args; simpl in *; try congruence). *)
  (*   inv H0; inv H1; apply val_compat_shr_imm; auto. *)
  (* - do 2 (destruct args; simpl in *; try congruence). *)
  (*   eapply val_compat_shrx_imm; eauto. *)
  (* - do 2 (destruct args; simpl in *; try congruence). *)
  (*   inv H0; inv H1; apply val_compat_shru_imm; auto. *)
  (* - do 3 (destruct args; simpl in *; try congruence). *)
  (*   inv H0; inv H1; apply val_compat_shru_dimm; auto. *)
  (* - eapply rs_compat_eval_addressing32; eauto. *)
  (* - do 3 (destruct args; simpl in *; try congruence). *)
  (*   inv H0; inv H1. *)
  (*   apply val_compat_subl; auto. *)
  (*   apply is_protected_subl_archi_ptr64_false; assumption. *)
  (* - do 2 (destruct args; simpl in *; try congruence). *)
  (*   inv H0; inv H1; apply val_compat_shll_imm; auto. *)
  (* - do 2 (destruct args; simpl in *; try congruence). *)
  (*   inv H0; inv H1; apply val_compat_shrl_imm; auto. *)
  (* - do 2 (destruct args; simpl in *; try congruence). *)
  (*   eapply val_compat_shrxl_imm; eauto. *)
  (* - do 2 (destruct args; simpl in *; try congruence). *)
  (*   inv H0; inv H1; apply val_compat_shrlu_imm; auto. *)
  (* - eapply rs_compat_eval_addressing64; eauto. *)
  (* - do 2 (destruct args; simpl in *; try congruence). *)
  (*   eapply val_compat_floatofint; eauto. *)
  (* - do 2 (destruct args; simpl in *; try congruence). *)
  (*   eapply val_compat_singleofint; eauto. *)
  (* - do 2 (destruct args; simpl in *; try congruence). *)
  (*   eapply val_compat_floatoflong; eauto. *)
  (* - do 2 (destruct args; simpl in *; try congruence). *)
  (*   eapply val_compat_singleoflong; eauto. *)
  (* - inv H0; inv H1. *)
  (*   destruct (Op.eval_condition cond rs1 ## args m1) eqn:Hcond. *)
  (*   + eapply rs_compat_eval_condition in Hcond; eauto. *)
  (*     * destruct Hcond as [b' Hcond]. *)
  (*       rewrite Hcond; simpl. *)
  (*       destruct b, b'; constructor. *)
  (*     * intros Harchi HC; inv HC; apply Hop; constructor; assumption. *)
  (*     * intros Harchi HC; inv HC; apply Hop; constructor; assumption. *)
  (*   + constructor. *)
(* Qed. *)

End VAL_COMPAT_OPS.

(** * val_compat monotonicity for safe builtins *)

(** Helper: [val_compat] is preserved through [proj_num] and [inj_num].
    For a [mkbuiltin_nNt] builtin, arguments are extracted via [proj_num]
    (which returns a default when the value constructor doesn't match the
    expected type), a pure function is applied, and the result is wrapped
    via [inj_num].  Under [val_compat], inputs of the same constructor
    produce same-constructor outputs. *)

Lemma val_compat_proj_num_inj (targ: typ) (tres: xtype)
      (f1 f2: valty targ -> valxty tres) (v1 v2: val) :
  val_compat v1 v2 ->
  val_compat
    (proj_num targ Vundef v1 (fun x => inj_num tres (f1 x)))
    (proj_num targ Vundef v2 (fun x => inj_num tres (f2 x))).
Proof.
  intros Hcompat; inv Hcompat; destruct targ; simpl; try constructor;
    destruct tres; simpl; try constructor.
Qed.

(** ** Per-class lemmas for mkbuiltin_n1t builtins *)

Lemma val_compat_mkbuiltin_n1t
      (targ: typ) (tres: xtype) (f: valty targ -> valxty tres)
      (vargs1 vargs2: list val) (vres1: val) :
  Forall2 val_compat vargs1 vargs2 ->
  mkbuiltin_n1t targ tres f vargs1 = Some vres1 ->
  exists vres2,
    mkbuiltin_n1t targ tres f vargs2 = Some vres2 /\
    val_compat vres1 vres2.
Proof.
  intros Hcompat Hsem.
  simpl in *.
  destruct vargs1 as [|v1 [|]]; try discriminate.
  inv Hcompat. inv H3. inv Hsem.
  eexists; split; [reflexivity|].
  apply val_compat_proj_num_inj; auto.
Qed.

(** Helper: [val_compat] through nested [proj_num]/[inj_num] for 2-arg
    numerical builtins. *)

Lemma val_compat_proj_num_inj2 (targ1 targ2: typ) (tres: xtype)
      (f1 f2: valty targ1 -> valty targ2 -> valxty tres) (v1 v2 w1 w2: val) :
  val_compat v1 v2 ->
  val_compat w1 w2 ->
  val_compat
    (proj_num targ1 Vundef v1 (fun x1 =>
     proj_num targ2 Vundef w1 (fun x2 => inj_num tres (f1 x1 x2))))
    (proj_num targ1 Vundef v2 (fun x1 =>
     proj_num targ2 Vundef w2 (fun x2 => inj_num tres (f2 x1 x2)))).
Proof.
  intros Hv Hw; inv Hv; destruct targ1; simpl; try constructor;
    apply val_compat_proj_num_inj; auto.
Qed.

Lemma val_compat_proj_num_inj3 (targ1 targ2 targ3: typ) (tres: xtype)
  (f1 f2: valty targ1 -> valty targ2 -> valty targ3 -> valxty tres) (v1 v2 a1 w1 w2 a2: val) :
  val_compat v1 v2 ->
  val_compat w1 w2 ->
  val_compat a1 a2 ->
  val_compat
    (proj_num targ1 Vundef v1 
      (fun x1 =>
      proj_num targ2 Vundef w1 
        (fun x2 => 
        proj_num targ3 Vundef a1
          (fun x3 =>
            inj_num tres (f1 x1 x2 x3)))))

    (proj_num targ1 Vundef v2 
      (fun x1 =>
      proj_num targ2 Vundef w2 
        (fun x2 => 
        proj_num targ3 Vundef a2
          (fun x3 =>
          inj_num tres (f2 x1 x2 x3))))).
Proof.
  intros Hv Hw Ha; inv Hv; inv Hw; destruct targ1; destruct targ2; simpl; try constructor;
  apply val_compat_proj_num_inj; auto.
Qed.


(*
   mk...buitltin2t -> numeric funcs of 2 args
*)
Lemma val_compat_mkbuiltin_n2t
      (targ1 targ2: typ) (tres: xtype)
      (f: valty targ1 -> valty targ2 -> valxty tres)
      (vargs1 vargs2: list val) (vres1: val) :
  Forall2 val_compat vargs1 vargs2 ->
  mkbuiltin_n2t targ1 targ2 tres f vargs1 = Some vres1 ->
  exists vres2,
    mkbuiltin_n2t targ1 targ2 tres f vargs2 = Some vres2 /\
    val_compat vres1 vres2.
Proof.
  intros Hcompat Hsem.
  simpl in *.
  destruct vargs1 as [|v1 [|w1 [|]]]; try discriminate.
  inv Hcompat. inv H3.
  match goal with H : Forall2 _ nil _ |- _ => inv H end.
  inv Hsem.
  eexists; split; [reflexivity|].
  apply val_compat_proj_num_inj2; auto.
Qed.


Lemma val_compat_mkbuiltin_n3t
      (targ1 targ2 targ3: typ) (tres: xtype)
      (f: valty targ1 -> valty targ2 -> valty targ3 -> valxty tres)
      (vargs1 vargs2: list val) (vres1: val) :
  Forall2 val_compat vargs1 vargs2 ->
  mkbuiltin_n3t targ1 targ2 targ3 tres f vargs1 = Some vres1 ->
  exists vres2,
    mkbuiltin_n3t targ1 targ2 targ3 tres f vargs2 = Some vres2 /\
    val_compat vres1 vres2.
Proof.
  intros Hcompat Hsem.
  simpl in *.
  destruct vargs1 as [|v1 [|w1 [|a1 [| ]]]]; try discriminate.
  inv Hcompat. inv H3. inv H5. inv H6.
  (* match goal with H : Forall2 _ nil _ |- _ => inv H end. *)
  inv Hsem.
  eexists; split; [reflexivity|].
  apply val_compat_proj_num_inj3; auto.
Qed.


(** ** val_compat lemmas for mkbuiltin_v2t builtins *)

(** [Val.mull'] takes [Vint * Vint -> Vlong], otherwise [Vundef].
    Under [val_compat], both sides either produce [Vlong] or [Vundef]. *)

Lemma val_compat_mull' v1 v1' v2 v2' :
  val_compat v1 v1' ->
  val_compat v2 v2' ->
  val_compat (Val.mull' v1 v2) (Val.mull' v1' v2').
Proof.
  intros H0 H1; inv H0; inv H1; simpl; constructor.
Qed.

(** Generic tactic for 2-arg v2t builtin val_compat proofs *)

Local Ltac solve_v2t_builtin vc_lemma :=
  let Hcompat := fresh "Hcompat" in
  let Hsem := fresh "Hsem" in
  intros Hcompat Hsem;
  simpl in *;
  destruct Hcompat as [| ? ? ? ? ? Hcompat]; [discriminate|];
  destruct Hcompat as [| ? ? ? ? ? Hcompat]; [discriminate|];
  destruct Hcompat; [|discriminate];
  inv Hsem;
  eexists; split; [reflexivity|];
  eapply vc_lemma; eassumption.

(** Lifting [val_compat_addl] to the builtin semantics wrapper. *)

Lemma builtin_sem_val_compat_addl vargs1 vargs2 vres1 :
  Forall2 val_compat vargs1 vargs2 ->
  standard_builtin_sem BI_addl vargs1 = Some vres1 ->
  exists vres2,
    standard_builtin_sem BI_addl vargs2 = Some vres2 /\
    val_compat vres1 vres2.
Proof. solve_v2t_builtin val_compat_addl. Qed.

(** Lifting [val_compat_mull'] to the builtin semantics wrapper. *)

Lemma builtin_sem_val_compat_mull vargs1 vargs2 vres1 :
  Forall2 val_compat vargs1 vargs2 ->
  standard_builtin_sem BI_mull vargs1 = Some vres1 ->
  exists vres2,
    standard_builtin_sem BI_mull vargs2 = Some vres2 /\
    val_compat vres1 vres2.
Proof. solve_v2t_builtin val_compat_mull'. Qed.

(** Lifting [val_compat_subl] to the builtin semantics wrapper.
    Requires [Archi.ptr64 = false] because [BI_subl] is only
    classified as replicable when [negb Archi.ptr64 = true]. *)

Lemma builtin_sem_val_compat_subl vargs1 vargs2 vres1 :
  Archi.ptr64 = false ->
  Forall2 val_compat vargs1 vargs2 ->
  standard_builtin_sem BI_subl vargs1 = Some vres1 ->
  exists vres2,
    standard_builtin_sem BI_subl vargs2 = Some vres2 /\
    val_compat vres1 vres2.
Proof.
  intros Harchi. solve_v2t_builtin val_compat_subl.
Qed.

(** ** [builtin_sem_val_compat] for replicable builtins *)

(** The [builtin_sem_val_compat] lemma tries to prove result compatibility
    from only pointwise [val_compat] of the builtin arguments.  That
    assumption is not strong enough for the i64 shift builtins:
    [val_compat] relates
    any two [Vint] shift amounts, so the source amount can be in range
    while the faulted amount is out of range.  The builtin can then
    return [Vlong _] on the source side and [Vundef] on the faulted
    side, and [val_compat (Vlong _) Vundef] is not provable.

    [builtin_sem_val_compat] therefore handles only non-shift builtins.
    In the current fault policy, the i64 shift builtins are also
    classified as non-replicable, so the non-shift side condition follows
    from the replication gate. *)

Section BUILTIN_VAL_COMPAT.

Context {VT: vote_type} {vsem: VoteSemantics VT}.

(** Per-standard-builtin val_compat property for non-shift builtins.
    The gate uses [builtin_can_replicate_bf] uniformly.  Shift builtins
    are excluded via the separate hypothesis.  For [BI_subl], the gate
    reduces to [negb Archi.ptr64 = true]; on ptr64 architectures this
    is discriminated, on 32-bit architectures the proof uses
    [val_compat_subl] with the derived [Archi.ptr64 = false]. *)

Lemma standard_builtin_sem_val_compat (sb: standard_builtin) vargs1 vargs2 vres1 :
  match sb with
  | BI_i64_shl | BI_i64_shr | BI_i64_sar => False
  | _ => builtin_can_replicate_bf (BI_standard sb) = true
  end ->
  Forall2 val_compat vargs1 vargs2 ->
  standard_builtin_sem sb vargs1 = Some vres1 ->
  exists vres2,
    standard_builtin_sem sb vargs2 = Some vres2 /\
    val_compat vres1 vres2.
Proof.
  intros Hgate Hcompat Hsem.
  destruct sb; simpl in Hgate; try discriminate; try contradiction;
    try solve [eapply val_compat_mkbuiltin_n1t; eauto];
    try solve [eapply val_compat_mkbuiltin_n2t; eauto];
    try solve [eapply builtin_sem_val_compat_addl; eauto];
    try solve [eapply builtin_sem_val_compat_mull; eauto];
    try solve [eapply builtin_sem_val_compat_subl; eauto;
               destruct Archi.ptr64; simpl in Hgate; congruence].
Qed.

(** Platform builtin val_compat property. *)

Lemma platform_builtin_sem_val_compat (pb: platform_builtin) vargs1 vargs2 vres1 :
  Forall2 val_compat vargs1 vargs2 ->
  platform_builtin_sem pb vargs1 = Some vres1 ->
  exists vres2,
    platform_builtin_sem pb vargs2 = Some vres2 /\
    val_compat vres1 vres2.
Proof.
  intros Hcompat Hsem.
  destruct pb; 
   try eapply val_compat_mkbuiltin_n3t; eauto;
  eapply val_compat_mkbuiltin_n2t; eauto.
Qed.

(** [builtin_sem_val_compat] lifts the per-builtin lemmas to
    [builtin_function_sem].  It assumes both the replication gate and the
    explicit non-shift side condition.  [BI_replicate] is ruled out by
    the gate, and standard i64 shifts are ruled out by the side condition
    (which is derivable from the current gate because they are
    non-replicable). *)

Lemma builtin_sem_val_compat (bf: builtin_function)
      (vargs1 vargs2: list val) (vres1: val) :
  builtin_can_replicate_bf bf = true ->
  (match bf with
   | BI_standard BI_i64_shl
   | BI_standard BI_i64_shr
   | BI_standard BI_i64_sar => False
   | _ => True
   end) ->
  Forall2 val_compat vargs1 vargs2 ->
  builtin_function_sem bf vargs1 = Some vres1 ->
  exists vres2,
    builtin_function_sem bf vargs2 = Some vres2 /\
    val_compat vres1 vres2.
Proof.
  intros Hgate Hnoshift Hcompat Hsem.
  destruct bf as [sb|pb|rb].
  - (* BI_standard *)
    simpl in Hsem.
    eapply standard_builtin_sem_val_compat; eauto.
    destruct sb; simpl in *; try exact Hgate; try contradiction.
  - (* BI_platform *)
    simpl in Hsem.
    eapply platform_builtin_sem_val_compat; eauto.
  - (* BI_replicate -- contradictory *)
    simpl in Hgate. discriminate.
Qed.

End BUILTIN_VAL_COMPAT.
