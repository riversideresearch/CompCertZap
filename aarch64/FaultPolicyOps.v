Require Import Coqlib.
Require Import AST Builtins CompCertZapUtils Globalenvs Memory Op Registers Values.

(** * Operation classification *)

Inductive is_protected : operation -> Prop :=
| is_protected_Odiv : is_protected Odiv
| is_protected_Odivu : is_protected Odivu
| is_protected_Odivl : is_protected Odivl
| is_protected_Odivlu : is_protected Odivlu
| is_protected_Ointofsingle : is_protected Ointofsingle
| is_protected_Ointuofsingle : is_protected Ointuofsingle
| is_protected_Ointoffloat : is_protected Ointoffloat
| is_protected_Ointuoffloat : is_protected Ointuoffloat
| is_protected_Olongofsingle : is_protected Olongofsingle
| is_protected_Olonguofsingle : is_protected Olonguofsingle
| is_protected_Olongoffloat : is_protected Olongoffloat
| is_protected_Olonguoffloat : is_protected Olonguoffloat
| is_protected_Oshl : is_protected Oshl
| is_protected_Oshr : is_protected Oshr
| is_protected_Oshru : is_protected Oshru
| is_protected_Oshll : is_protected Oshll
| is_protected_Oshrl : is_protected Oshrl
| is_protected_Oshrlu : is_protected Oshrlu
| is_protected_Osubl : Archi.ptr64 = true -> is_protected Osubl
| is_protected_Osel : forall cond ty, is_protected (Osel cond ty)
| is_protected_Ocmp_Ccompu : forall c, Archi.ptr64 = false ->
    is_protected (Ocmp (Ccompu c))
| is_protected_Ocmp_Ccompuimm : forall c n, Archi.ptr64 = false ->
    is_protected (Ocmp (Ccompuimm c n))
| is_protected_Ocmp_Ccompushift : forall c s a, Archi.ptr64 = false ->
    is_protected (Ocmp (Ccompushift c s a))
| is_protected_Ocmp_Ccomplu : forall c, Archi.ptr64 = true ->
    is_protected (Ocmp (Ccomplu c))
| is_protected_Ocmp_Ccompluimm : forall c n, Archi.ptr64 = true ->
    is_protected (Ocmp (Ccompluimm c n))
| is_protected_Ocmp_Ccomplushift : forall c s a, Archi.ptr64 = true ->
    is_protected (Ocmp (Ccomplushift c s a)).

Definition is_protectedb (op : operation) : bool :=
  match op with
  | Odiv | Odivu | Odivl | Odivlu
  | Ointofsingle | Ointuofsingle | Ointoffloat | Ointuoffloat
  | Olongofsingle | Olonguofsingle | Olongoffloat | Olonguoffloat
  | Oshl | Oshr | Oshru | Oshll | Oshrl | Oshrlu
  | Osel _ _ => true
  | Osubl => Archi.ptr64
  | Ocmp (Ccompu _) | Ocmp (Ccompuimm _ _) | Ocmp (Ccompushift _ _ _) =>
      negb Archi.ptr64
  | Ocmp (Ccomplu _) | Ocmp (Ccompluimm _ _) | Ocmp (Ccomplushift _ _ _) =>
      Archi.ptr64
  | _ => false
  end.

Lemma is_protectedb_spec (op : operation) :
  reflect (is_protected op) (is_protectedb op).
Proof.
  destruct op; simpl;
    try solve [right; intro HC; inversion HC];
    try solve [left; constructor].
  - destruct Archi.ptr64 eqn:Harchi; simpl.
    + left; constructor; exact Harchi.
    + right; intro HC; inversion HC; congruence.
  - destruct cond; simpl; try solve [right; intro HC; inversion HC].
    + destruct Archi.ptr64 eqn:Harchi; simpl.
      * right; intro HC; inversion HC; congruence.
      * left; constructor; exact Harchi.
    + destruct Archi.ptr64 eqn:Harchi; simpl.
      * right; intro HC; inversion HC; congruence.
      * left; constructor; exact Harchi.
    + destruct Archi.ptr64 eqn:Harchi; simpl.
      * right; intro HC; inversion HC; congruence.
      * left; constructor; exact Harchi.
    + destruct Archi.ptr64 eqn:Harchi; simpl.
      * left; constructor; exact Harchi.
      * right; intro HC; inversion HC; congruence.
    + destruct Archi.ptr64 eqn:Harchi; simpl.
      * left; constructor; exact Harchi.
      * right; intro HC; inversion HC; congruence.
    + destruct Archi.ptr64 eqn:Harchi; simpl.
      * left; constructor; exact Harchi.
      * right; intro HC; inversion HC; congruence.
Qed.

Lemma is_protected_subl_archi_ptr64_false :
  ~ is_protected Op.Osubl ->
  Archi.ptr64 = false.
Proof.
  intro H.
  destruct Archi.ptr64 eqn:Harchi; auto.
  exfalso; apply H; constructor; assumption.
Qed.

Definition builtin_can_replicate_platform (pb : platform_builtin) : bool :=
  match pb with end.

(** * Condition classifiers used by the fault model *)

Inductive is_compu : condition -> Prop :=
| is_compu_Ccompu : forall c, is_compu (Ccompu c)
| is_compu_Ccompuimm : forall c n, is_compu (Ccompuimm c n)
| is_compu_Ccompushift : forall c s a, is_compu (Ccompushift c s a).

Inductive is_complu : condition -> Prop :=
| is_complu_Ccomplu : forall c, is_complu (Ccomplu c)
| is_complu_Ccompluimm : forall c n, is_complu (Ccompluimm c n)
| is_complu_Ccomplushift : forall c s a, is_complu (Ccomplushift c s a).

(** * RTLfault compatibility lemmas *)

Section RTLFAULT_OPS.
Variables F V : Type.
Variable ge : Genv.t F V.

Lemma val_compat_eval_shift s a v v' :
  val_compat v v' ->
  val_compat (eval_shift s v a) (eval_shift s v' a).
Proof.
  intro Hcompat.
  destruct s; simpl.
  - apply val_compat_shl_imm; assumption.
  - apply val_compat_shru_imm; assumption.
  - apply val_compat_shr_imm; assumption.
  - inv Hcompat; simpl; constructor.
Qed.

Lemma val_compat_eval_shiftl s a v v' :
  val_compat v v' ->
  val_compat (eval_shiftl s v a) (eval_shiftl s v' a).
Proof.
  intro Hcompat.
  destruct s; simpl.
  - apply val_compat_shll_imm; assumption.
  - apply val_compat_shrlu_imm; assumption.
  - apply val_compat_shrl_imm; assumption.
  - inv Hcompat; simpl; constructor.
Qed.

Lemma val_compat_longofint v v' :
  val_compat v v' ->
  val_compat (Val.longofint v) (Val.longofint v').
Proof.
  intro Hcompat; inv Hcompat; simpl; constructor.
Qed.

Lemma val_compat_longofintu v v' :
  val_compat v v' ->
  val_compat (Val.longofintu v) (Val.longofintu v').
Proof.
  intro Hcompat; inv Hcompat; simpl; constructor.
Qed.

Lemma val_compat_eval_extend x a v v' :
  val_compat v v' ->
  val_compat (eval_extend x v a) (eval_extend x v' a).
Proof.
  intro Hcompat.
  destruct x; simpl.
  - apply val_compat_shll_imm.
    apply val_compat_longofint; assumption.
  - apply val_compat_shll_imm.
    apply val_compat_longofintu; assumption.
Qed.
Lemma eval_shiftl_not_ptr s a v b ofs :
  eval_shiftl s v a <> Vptr b ofs.
Proof.
  destruct s; destruct v; intro Hc; cbn in Hc; try discriminate;
    destruct (Integers.Int.ltu a Integers.Int64.iwordsize'); discriminate.
Qed.

Lemma eval_extend_not_ptr x a v b ofs :
  eval_extend x v a <> Vptr b ofs.
Proof.
  destruct x; destruct v; intro Hc; cbn in Hc; try discriminate;
    destruct (Integers.Int.ltu a Integers.Int64.iwordsize'); discriminate.
Qed.

Lemma val_compat_maskint_bool c v v' n b :
  val_compat v v' ->
  Val.cmp_bool c (Val.and v (Vint n)) (Vint Integers.Int.zero) = Some b ->
  exists b', Val.cmp_bool c (Val.and v' (Vint n)) (Vint Integers.Int.zero) = Some b'.
Proof.
  intros Hcompat Hmask.
  inv Hcompat; simpl in *; try congruence.
  eexists; reflexivity.
Qed.

Lemma val_compat_masklong_bool c v v' n b :
  val_compat v v' ->
  Val.cmpl_bool c (Val.andl v (Vlong n)) (Vlong Integers.Int64.zero) = Some b ->
  exists b', Val.cmpl_bool c (Val.andl v' (Vlong n)) (Vlong Integers.Int64.zero) = Some b'.
Proof.
  intros Hcompat Hmask.
  inv Hcompat; simpl in *; try congruence.
  eexists; reflexivity.
Qed.

Lemma rs_compat_eval_condition cond rs1 rs2 args m1 m2 b :
  (Archi.ptr64 = false -> ~ is_compu cond) ->
  (Archi.ptr64 = true -> ~ is_complu cond) ->
  rs_compat rs1 rs2 ->
  eval_condition cond (rs1 ## args) m1 = Some b ->
  exists b', eval_condition cond (rs2 ## args) m2 = Some b'.
Proof.
  intros Hnotcompu Hnotcomplu Hcompat Hcond.
  destruct cond; simpl in *.
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
    eapply val_compat_cmp_bool; eauto using val_compat_eval_shift.
  - do 3 (destruct args; simpl in *; try congruence).
    destruct Archi.ptr64 eqn:Harchi.
    + eapply val_compat_cmpu_bool; eauto using val_compat_eval_shift.
    + exfalso; eapply Hnotcompu; constructor.
  - do 2 (destruct args; simpl in *; try congruence).
    eapply val_compat_maskint_bool; eauto.
  - do 2 (destruct args; simpl in *; try congruence).
    eapply val_compat_maskint_bool; eauto.
  - do 3 (destruct args; simpl in *; try congruence).
    eapply val_compat_cmpl_bool; eauto.
  - do 3 (destruct args; simpl in *; try congruence).
    destruct Archi.ptr64 eqn:Harchi.
    + exfalso; apply Hnotcomplu; auto; constructor.
    + eapply val_compat_cmplu_bool; eauto.
  - do 2 (destruct args; simpl in *; try congruence).
    eapply val_compat_cmpl_bool; eauto; constructor.
  - do 2 (destruct args; simpl in *; try congruence).
    destruct Archi.ptr64 eqn:Harchi.
    + exfalso; apply Hnotcomplu; auto; constructor.
    + eapply val_compat_cmplu_bool; eauto; constructor.
  - do 3 (destruct args; simpl in *; try congruence).
    eapply val_compat_cmpl_bool; eauto using val_compat_eval_shiftl.
  - do 3 (destruct args; simpl in *; try congruence).
    destruct Archi.ptr64 eqn:Harchi.
    + exfalso; apply Hnotcomplu; auto; constructor.
    + eapply val_compat_cmplu_bool; eauto using val_compat_eval_shiftl.
  - do 2 (destruct args; simpl in *; try congruence).
    eapply val_compat_masklong_bool; eauto.
  - do 2 (destruct args; simpl in *; try congruence).
    eapply val_compat_masklong_bool; eauto.
  - do 3 (destruct args; simpl in *; try congruence).
    eapply val_compat_cmpf_bool; eauto.
  - do 3 (destruct args; simpl in *; try congruence).
    apply option_map_some in Hcond.
    destruct Hcond as (b' & Hcmp & ->).
    eapply val_compat_cmpf_bool in Hcmp; eauto.
    destruct Hcmp as (b'' & Hcmp).
    exists (negb b'').
    now rewrite Hcmp.
  - do 2 (destruct args; simpl in *; try congruence).
    eapply val_compat_cmpf_bool; eauto; constructor.
  - do 2 (destruct args; simpl in *; try congruence).
    apply option_map_some in Hcond.
    destruct Hcond as (b' & Hcmp & ->).
    eapply val_compat_cmpf_bool in Hcmp; eauto; [|constructor].
    destruct Hcmp as (b'' & Hcmp).
    exists (negb b'').
    now rewrite Hcmp.
  - do 3 (destruct args; simpl in *; try congruence).
    eapply val_compat_cmpfs_bool; eauto.
  - do 3 (destruct args; simpl in *; try congruence).
    apply option_map_some in Hcond.
    destruct Hcond as (b' & Hcmp & ->).
    eapply val_compat_cmpfs_bool in Hcmp; eauto.
    destruct Hcmp as (b'' & Hcmp).
    exists (negb b'').
    now rewrite Hcmp.
  - do 2 (destruct args; simpl in *; try congruence).
    eapply val_compat_cmpfs_bool; eauto; constructor.
  - do 2 (destruct args; simpl in *; try congruence).
    apply option_map_some in Hcond.
    destruct Hcond as (b' & Hcmp & ->).
    eapply val_compat_cmpfs_bool in Hcmp; eauto; [|constructor].
    destruct Hcmp as (b'' & Hcmp).
    exists (negb b'').
    now rewrite Hcmp.
Qed.

Lemma rs_compat_eval_operation rs1 rs2 sp op args m v :
  ~ is_protected op ->
  rs_compat rs1 rs2 ->
  eval_operation ge sp op (rs1 ## args) m = Some v ->
  exists v', eval_operation ge sp op (rs2 ## args) m = Some v'.
Proof.
  intros Hsafe Hcompat Hop.
  destruct op; simpl in *;
    try (destruct args; simpl in *; try congruence);
    try (destruct args; simpl in *; try congruence);
    try (destruct args; simpl in *; try congruence);
    try (destruct args; simpl in *; try congruence);
    inv Hop; try solve [eexists; eauto];
    try solve [exfalso; apply Hsafe; constructor].
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

Lemma eval_operation_val_compat rs1 rs2 sp op args m1 m2 v v' :
  ~ is_protected op ->
  rs_compat rs1 rs2 ->
  eval_operation ge sp op (rs1 ## args) m1 = Some v ->
  eval_operation ge sp op (rs2 ## args) m2 = Some v' ->
  val_compat v v'.
Proof.
  intros Hsafe Hcompat H0 H1.
  destruct op; simpl in *;
    try (destruct args; simpl in *; try congruence);
    try (destruct args; simpl in *; try congruence);
    try (destruct args; simpl in *; try congruence);
    try (destruct args; simpl in *; try congruence).
  all: try solve [exfalso; apply Hsafe; constructor].
  all: try solve [inv H0; inv H1; constructor].
  all: try solve [inv H0; inv H1; apply val_compat_refl].
  all: try solve [inv H0; inv H1; exact (Hcompat p)].
  all: try solve [inv H0; inv H1;
                  pose proof (Hcompat p) as Hp;
                  inv Hp; simpl; constructor].
  all: try solve [inv H0; inv H1;
                  pose proof (Hcompat p) as Hp;
                  pose proof (Hcompat p0) as Hq;
                  inv Hp; inv Hq; simpl; constructor].
  all: try solve [inv H0; inv H1;
                  pose proof (Hcompat p) as Hp;
                  pose proof (Hcompat p0) as Hq;
                  pose proof (Hcompat p1) as Hr;
                  inv Hp; inv Hq; inv Hr; simpl; constructor].
  - inv H0; inv H1.
    eapply val_compat_eval_shift; eauto.
  - inv H0; inv H1.
    pose proof (Hcompat p) as Hp.
    pose proof (val_compat_eval_shift s a (rs1 # p0) (rs2 # p0) (Hcompat p0)) as Hs.
    inv Hp; inv Hs; simpl; constructor.
  - inv H0; inv H1.
    pose proof (val_compat_eval_shift s a (rs1 # p) (rs2 # p) (Hcompat p)) as Hs.
    inv Hs; simpl; constructor.
  - inv H0; inv H1.
    pose proof (Hcompat p) as Hp.
    pose proof (val_compat_eval_shift s a (rs1 # p0) (rs2 # p0) (Hcompat p0)) as Hs.
    inv Hp; inv Hs; simpl; constructor.
  - inv H0; inv H1.
    pose proof (Hcompat p) as Hp.
    pose proof (val_compat_eval_shift s a (rs1 # p0) (rs2 # p0) (Hcompat p0)) as Hs.
    inv Hp; inv Hs; simpl; constructor.
  - inv H0; inv H1.
    pose proof (Hcompat p) as Hp.
    pose proof (val_compat_eval_shift s a (rs1 # p0) (rs2 # p0) (Hcompat p0)) as Hs.
    inv Hp; inv Hs; simpl; constructor.
  - inv H0; inv H1.
    pose proof (Hcompat p) as Hp.
    pose proof (val_compat_eval_shift s a (rs1 # p0) (rs2 # p0) (Hcompat p0)) as Hs.
    inv Hp; inv Hs; simpl; constructor.
  - inv H0; inv H1.
    pose proof (val_compat_eval_shift s a (rs1 # p) (rs2 # p) (Hcompat p)) as Hs.
    inv Hs; simpl; constructor.
  - inv H0; inv H1.
    pose proof (Hcompat p) as Hp.
    pose proof (val_compat_eval_shift s a (rs1 # p0) (rs2 # p0) (Hcompat p0)) as Hs.
    inv Hp; inv Hs; simpl; constructor.
  - inv H0; inv H1.
    pose proof (Hcompat p) as Hp.
    pose proof (val_compat_eval_shift s a (rs1 # p0) (rs2 # p0) (Hcompat p0)) as Hs.
    inv Hp; inv Hs; simpl; constructor.
  - inv H0; inv H1.
    pose proof (Hcompat p) as Hp.
    pose proof (val_compat_eval_shift s a (rs1 # p0) (rs2 # p0) (Hcompat p0)) as Hs.
    inv Hp; inv Hs; simpl; constructor.
  - eapply val_compat_shrx_imm; eauto using Hcompat.
  - inv H0; inv H1.
    apply val_compat_shl_imm.
    pose proof (Hcompat p) as Hp.
    inv Hp; simpl; constructor.
  - inv H0; inv H1.
    apply val_compat_shl_imm.
    pose proof (Hcompat p) as Hp.
    inv Hp; simpl; constructor.
  - inv H0; inv H1.
    pose proof (val_compat_shru_imm (rs1 # p) (rs2 # p) a (Hcompat p)) as Hs.
    inv Hs; simpl; constructor.
  - inv H0; inv H1.
    pose proof (val_compat_shr_imm (rs1 # p) (rs2 # p) a (Hcompat p)) as Hs.
    inv Hs; simpl; constructor.
  - inv H0; inv H1.
    eapply val_compat_eval_shiftl; eauto.
  - inv H0; inv H1.
    eapply val_compat_eval_extend; eauto.
  - inv H0; inv H1.
    pose proof (Hcompat p) as Hp.
    pose proof (val_compat_eval_shiftl s a (rs1 # p0) (rs2 # p0) (Hcompat p0)) as Hs.
    inv Hp; inv Hs; simpl; constructor.
  - inv H0; inv H1.
    pose proof (Hcompat p) as Hp.
    pose proof (val_compat_eval_extend x a (rs1 # p0) (rs2 # p0) (Hcompat p0)) as Hs.
    inv Hp; inv Hs; simpl; constructor.
  - inv H0; inv H1.
    pose proof (val_compat_eval_shiftl s a (rs1 # p) (rs2 # p) (Hcompat p)) as Hs.
    inv Hs; simpl; constructor.
  - inv H0; inv H1.
    eapply val_compat_subl.
    + apply is_protected_subl_archi_ptr64_false; exact Hsafe.
    + exact (Hcompat p).
    + exact (Hcompat p0).
  - inv H0; inv H1.
    pose proof (Hcompat p) as Hp.
    pose proof (val_compat_eval_shiftl s a (rs1 # p0) (rs2 # p0) (Hcompat p0)) as Hs.
    inv Hp; inv Hs; simpl in *;
      try congruence;
      try apply val_compat_undef;
      try apply val_compat_long;
      try apply val_compat_ptr.
    destruct Archi.ptr64;
      repeat destruct (eq_block _ _);
      try apply val_compat_undef;
      try apply val_compat_long.
    exfalso; eapply eval_shiftl_not_ptr; eauto.
  - inv H0; inv H1.
    pose proof (Hcompat p) as Hp.
    pose proof (val_compat_eval_extend x a (rs1 # p0) (rs2 # p0) (Hcompat p0)) as Hs.
    inv Hp; inv Hs; simpl in *;
      try congruence;
      try apply val_compat_undef;
      try apply val_compat_long;
      try apply val_compat_ptr.
    destruct Archi.ptr64;
      repeat destruct (eq_block _ _);
      try apply val_compat_undef;
      try apply val_compat_long.
    exfalso; eapply eval_extend_not_ptr; eauto.
  - inv H0; inv H1.
    pose proof (Hcompat p) as Hp.
    pose proof (val_compat_eval_shiftl s a (rs1 # p0) (rs2 # p0) (Hcompat p0)) as Hs.
    inv Hp; inv Hs; simpl; constructor.
  - inv H0; inv H1.
    pose proof (Hcompat p) as Hp.
    pose proof (val_compat_eval_shiftl s a (rs1 # p0) (rs2 # p0) (Hcompat p0)) as Hs.
    inv Hp; inv Hs; simpl; constructor.
  - inv H0; inv H1.
    pose proof (Hcompat p) as Hp.
    pose proof (val_compat_eval_shiftl s a (rs1 # p0) (rs2 # p0) (Hcompat p0)) as Hs.
    inv Hp; inv Hs; simpl; constructor.
  - inv H0; inv H1.
    pose proof (val_compat_eval_shiftl s a (rs1 # p) (rs2 # p) (Hcompat p)) as Hs.
    inv Hs; simpl; constructor.
  - inv H0; inv H1.
    pose proof (Hcompat p) as Hp.
    pose proof (val_compat_eval_shiftl s a (rs1 # p0) (rs2 # p0) (Hcompat p0)) as Hs.
    inv Hp; inv Hs; simpl; constructor.
  - inv H0; inv H1.
    pose proof (Hcompat p) as Hp.
    pose proof (val_compat_eval_shiftl s a (rs1 # p0) (rs2 # p0) (Hcompat p0)) as Hs.
    inv Hp; inv Hs; simpl; constructor.
  - inv H0; inv H1.
    pose proof (Hcompat p) as Hp.
    pose proof (val_compat_eval_shiftl s a (rs1 # p0) (rs2 # p0) (Hcompat p0)) as Hs.
    inv Hp; inv Hs; simpl; constructor.
  - eapply val_compat_shrxl_imm; eauto using Hcompat.
  - inv H0; inv H1.
    apply val_compat_shll_imm.
    pose proof (Hcompat p) as Hp.
    inv Hp; simpl; constructor.
  - inv H0; inv H1.
    apply val_compat_shll_imm.
    pose proof (Hcompat p) as Hp.
    inv Hp; simpl; constructor.
  - inv H0; inv H1.
    pose proof (val_compat_shrlu_imm (rs1 # p) (rs2 # p) a (Hcompat p)) as Hs.
    inv Hs; simpl; constructor.
  - inv H0; inv H1.
    pose proof (val_compat_shrl_imm (rs1 # p) (rs2 # p) a (Hcompat p)) as Hs.
    inv Hs; simpl; constructor.
  - eapply val_compat_floatofint; [exact (Hcompat p) | exact H0 | exact H1].
  - eapply val_compat_floatofintu; [exact (Hcompat p) | exact H0 | exact H1].
  - eapply val_compat_singleofint; [exact (Hcompat p) | exact H0 | exact H1].
  - eapply val_compat_singleofintu; [exact (Hcompat p) | exact H0 | exact H1].
  - eapply val_compat_floatoflong; [exact (Hcompat p) | exact H0 | exact H1].
  - eapply val_compat_floatoflongu; [exact (Hcompat p) | exact H0 | exact H1].
  - eapply val_compat_singleoflong; [exact (Hcompat p) | exact H0 | exact H1].
  - eapply val_compat_singleoflongu; [exact (Hcompat p) | exact H0 | exact H1].
  - inv H0; inv H1.
    destruct (eval_condition cond (rs1 # p :: nil) m1) eqn:Hcond.
    + change (eval_condition cond (rs1 ## (p :: nil)) m1 = Some b) in Hcond.
      eapply rs_compat_eval_condition in Hcond; eauto.
      * destruct Hcond as (b' & Hcond).
        rewrite Hcond; simpl.
        destruct b, b'; constructor.
      * intros Harchi HC; inv HC; apply Hsafe; constructor; assumption.
      * intros Harchi HC; inv HC; apply Hsafe; constructor; assumption.
    + constructor.
  - inv H0; inv H1.
    destruct (eval_condition cond (rs1 # p :: rs1 # p0 :: nil) m1) eqn:Hcond.
    + change (eval_condition cond (rs1 ## (p :: p0 :: nil)) m1 = Some b) in Hcond.
      eapply rs_compat_eval_condition in Hcond; eauto.
      * destruct Hcond as (b' & Hcond).
        rewrite Hcond; simpl.
        destruct b, b'; constructor.
      * intros Harchi HC; inv HC; apply Hsafe; constructor; assumption.
      * intros Harchi HC; inv HC; apply Hsafe; constructor; assumption.
    + constructor.
Qed.

End RTLFAULT_OPS.
