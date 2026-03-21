(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(* *********************************************************************)

(** Shared helper definitions for the CompCertZap fault-tolerance
    development.  These are backend-specific utilities, but they are
    not part of the core RTL syntax or semantics. *)

Require Import Coqlib AST Events Integers Memory Op Registers Values.

(** * Builtin-argument and builtin-result helpers *)

Fixpoint regs_of_builtin_arg (arg : builtin_arg reg) : list reg :=
  match arg with
  | BA r => r :: nil
  | BA_splitlong hi lo => regs_of_builtin_arg hi ++ regs_of_builtin_arg lo
  | BA_addptr a1 a2 => regs_of_builtin_arg a1 ++ regs_of_builtin_arg a2
  | _ => nil
  end.

(** Pull out registers from builtin arguments. *)
Fixpoint regs_of_builtin_args (args : list (builtin_arg reg)) : list reg :=
  match args with
  | nil => nil
  | ba :: rest => regs_of_builtin_arg ba ++ regs_of_builtin_args rest
  end.

(** This ignores the recursive cases because according to
    [Events.exec_Ibuiltin] (specifically [regmap_setres]) the result is used
    only in the [BR] case. *)
Definition reg_of_builtin_res (res : builtin_res reg) : option reg :=
  match res with
  | BR r => Some r
  | _ => None
  end.

(** * Generic positive-list and register-set helpers *)

Definition inb (p : positive) (l : list positive) : bool :=
  existsb (fun x => Pos.eqb x p) l.

Lemma inb_spec (p : positive) (l : list positive) :
  reflect (In p l) (inb p l).
Proof.
  revert p; induction l; intros; simpl.
  { right; auto. }
  destruct (peq a p); subst.
  - rewrite Pos.eqb_refl; left; left; reflexivity.
  - destruct (IHl p).
    + rewrite orb_true_r; left; right; assumption.
    + apply Pos.eqb_neq in n; rewrite n; right; intros [H|H]; subst.
      * rewrite Pos.eqb_refl in n; discriminate.
      * contradiction.
Qed.

Lemma not_in_inb x l :
  ~ In x l ->
  inb x l = true ->
  False.
Proof. intros Hnotin Hinb; destruct (inb_spec x l); congruence. Qed.

Fixpoint dedup (l : list positive) : list positive :=
  match l with
  | nil => nil
  | x :: xs =>
      let l' := dedup xs in
      if inb x l' then l' else x :: l'
  end.

Lemma in_dedup (p : positive) (l : list positive) :
  In p (dedup l) -> In p l.
Proof.
  revert p; induction l; simpl; intros p Hin; auto.
  destruct (inb_spec a (dedup l)).
  - right; apply IHl; assumption.
  - inv Hin.
    + left; reflexivity.
    + right; apply IHl; assumption.
Qed.

Definition Regset_of_list (l : list positive) : Regset.t :=
  fold_right (fun acc p => Regset.add acc p) Regset.empty l.

Definition Regset_of_option (x : option positive) : Regset.t :=
  match x with
  | Some p => Regset.singleton p
  | None => Regset.empty
  end.

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

Fixpoint in_builtin_argb (r : reg) (barg : builtin_arg reg) : bool :=
  match barg with
  | BA r' => Pos.eqb r r'
  | BA_splitlong hi lo => in_builtin_argb r hi || in_builtin_argb r lo
  | BA_addptr a b => in_builtin_argb r a || in_builtin_argb r b
  | _ => false
  end.

Lemma in_builtin_argb_spec (r : reg) (barg : builtin_arg reg) :
  reflect (in_builtin_arg r barg) (in_builtin_argb r barg).
Proof.
  induction barg; simpl; try solve [right; intro HC; inv HC].
  - destruct (Pos.eqb_spec r x); subst.
    + left; constructor.
    + right; intro HC; inv HC; congruence.
  - destruct IHbarg1; simpl.
    + left; constructor; auto.
    + destruct IHbarg2; simpl.
      * left; solve [constructor; auto].
      * right; intro HC; inv HC; contradiction.
  - destruct IHbarg1; simpl.
    + left; constructor; auto.
    + destruct IHbarg2; simpl.
      * left; solve [constructor; auto].
      * right; intro HC; inv HC; contradiction.
Qed.

Lemma in_builtin_argb_sound (r : reg) (barg : builtin_arg reg) :
  in_builtin_argb r barg = true -> in_builtin_arg r barg.
Proof. destruct (in_builtin_argb_spec r barg); congruence. Qed.

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

Inductive in_builtin_res {A : Type} (a : A) : builtin_res A -> Prop :=
| in_builtin_res_BR : in_builtin_res a (BR a)
| in_builtin_res_splitlong_hi : forall hi lo,
    in_builtin_res a hi ->
    in_builtin_res a (BR_splitlong hi lo)
| in_builtin_res_splitlong_lo : forall hi lo,
    in_builtin_res a lo ->
    in_builtin_res a (BR_splitlong hi lo).

Fixpoint in_builtin_resb (r : reg) (bres : builtin_res reg) : bool :=
  match bres with
  | BR r' => Pos.eqb r r'
  | BR_none => false
  | BR_splitlong hi lo => in_builtin_resb r hi || in_builtin_resb r lo
  end.

Lemma in_builtin_resb_spec (r : reg) (bres : builtin_res reg) :
  reflect (in_builtin_res r bres) (in_builtin_resb r bres).
Proof.
  induction bres; simpl; try solve [right; intro HC; inv HC].
  - destruct (Pos.eqb_spec r x); subst.
    + left; constructor.
    + right; intro HC; inv HC; congruence.
  - destruct IHbres1; simpl.
    + left; constructor; auto.
    + destruct IHbres2; simpl.
      * left; solve [constructor; auto].
      * right; intro HC; inv HC; contradiction.
Qed.

Lemma in_builtin_resb_sound (r : reg) (bres : builtin_res reg) :
  in_builtin_resb r bres = true -> in_builtin_res r bres.
Proof. destruct (in_builtin_resb_spec r bres); congruence. Qed.

(** * Fault-model value compatibility *)

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

Definition rs_compat (rs1 rs2 : Regmap.t val) : Prop :=
  forall r, val_compat (rs1 # r) (rs2 # r).

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

Lemma val_compat_floatofintu_exists v1 v2 vres :
  val_compat v1 v2 ->
  Val.floatofintu v1 = Some vres ->
  exists vres' : val, Val.floatofintu v2 = Some vres'.
Proof.
  intros Hcompat Hfoi.
  inv Hcompat; simpl in *; try congruence.
  eexists; reflexivity.
Qed.

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

Lemma val_compat_singleoflong_exists v1 v2 vres :
  val_compat v1 v2 ->
  Val.singleoflong v1 = Some vres ->
  exists vres' : val, Val.singleoflong v2 = Some vres'.
Proof.
  intros Hcompat Hsol.
  inv Hcompat; simpl in *; try congruence.
  eexists; reflexivity.
Qed.

Lemma val_compat_floatoflongu_exists v1 v2 vres :
  val_compat v1 v2 ->
  Val.floatoflongu v1 = Some vres ->
  exists vres' : val, Val.floatoflongu v2 = Some vres'.
Proof.
  intros Hcompat Hfol.
  inv Hcompat; simpl in *; try congruence.
  eexists; reflexivity.
Qed.

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

Lemma val_compat_floatofintu v v' vres vres' :
  val_compat v v' ->
  Val.floatofintu v = Some vres ->
  Val.floatofintu v' = Some vres' ->
  val_compat vres vres'.
Proof.
  intros Hcompat H0 H1; inv Hcompat; inv H0; inv H1; constructor.
Qed.

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

Lemma val_compat_singleoflong v v' vres vres' :
  val_compat v v' ->
  Val.singleoflong v = Some vres ->
  Val.singleoflong v' = Some vres' ->
  val_compat vres vres'.
Proof.
  intros Hcompat H0 H1; inv Hcompat; inv H0; inv H1; constructor.
Qed.
Lemma val_compat_floatoflongu v v' vres vres' :
  val_compat v v' ->
  Val.floatoflongu v = Some vres ->
  Val.floatoflongu v' = Some vres' ->
  val_compat vres vres'.
Proof.
  intros Hcompat H0 H1; inv Hcompat; inv H0; inv H1; constructor.
Qed.

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

(** * Predicates over builtin results *)

Fixpoint builtin_res_forall {A : Type} (P : A -> Prop) (bres : builtin_res A) : Prop :=
  match bres with
  | BR x => P x
  | BR_none => True
  | BR_splitlong hi lo => builtin_res_forall P hi /\ builtin_res_forall P lo
  end.

Lemma builtin_res_forall_impl {A : Type} (P Q : A -> Prop) bres :
  (forall a, P a -> Q a) ->
  builtin_res_forall P bres ->
  builtin_res_forall Q bres.
Proof.
  induction bres; simpl; intros Hpq Hforall; auto;
    destruct Hforall; auto.
Qed.

Fixpoint builtin_res_forallb {A : Type} (f : A -> bool) (bres : builtin_res A) : bool :=
  match bres with
  | BR x => f x
  | BR_none => true
  | BR_splitlong hi lo => builtin_res_forallb f hi && builtin_res_forallb f lo
  end.

Lemma builtin_res_forallb_spec {A : Type} (f : A -> bool) (bres : builtin_res A) :
  reflect (builtin_res_forall (fun a => f a = true) bres) (builtin_res_forallb f bres).
Proof.
  induction bres; simpl; try left; auto.
  - destruct (f x); solve [constructor; auto].
  - destruct IHbres1; simpl.
    + destruct IHbres2; simpl.
      * left; split; auto.
      * right; intros [H0 H1]; congruence.
    + right; intros [H0 H1]; congruence.
Qed.

Lemma builtin_res_forallb_sound {A : Type} (f : A -> bool) (bres : builtin_res A) :
  builtin_res_forallb f bres = true -> builtin_res_forall (fun a => f a = true) bres.
Proof. destruct (builtin_res_forallb_spec f bres); congruence. Qed.

Lemma in_builtin_arg_forall {A : Type} (P : A -> Prop) barg x :
  builtin_arg_forall P barg ->
  in_builtin_arg x barg ->
  P x.
Proof.
  revert x; induction barg; simpl; intros y Hforall Hin; inv Hin; auto;
    try solve [apply IHbarg1; intuition]; apply IHbarg2; intuition.
Qed.

(** Bridge: [in_builtin_arg] implies membership in [params_of_builtin_arg]. *)

Lemma in_builtin_arg_in_params {A : Type} (a : A) barg :
  in_builtin_arg a barg -> In a (params_of_builtin_arg barg).
Proof.
  induction barg; simpl; intro H; inv H;
    try (left; reflexivity);
    try (apply in_or_app; left; auto; fail);
    try (apply in_or_app; right; auto; fail).
Qed.

Lemma in_builtin_arg_in_params_args {A : Type} (a : A) barg bargs :
  In barg bargs ->
  in_builtin_arg a barg ->
  In a (params_of_builtin_args bargs).
Proof.
  induction bargs; simpl; intros Hin Harg.
  - destruct Hin.
  - destruct Hin as [-> | Hin].
    + apply in_or_app; left. apply in_builtin_arg_in_params; auto.
    + apply in_or_app; right. eapply IHbargs; eauto.
Qed.

(** Variant of [builtin_arg_forall_impl] that also provides
    [in_builtin_arg a barg] evidence to the callback. *)

Lemma builtin_arg_forall_impl_in {A : Type} (P Q : A -> Prop) barg :
  (forall a, P a -> in_builtin_arg a barg -> Q a) ->
  builtin_arg_forall P barg ->
  builtin_arg_forall Q barg.
Proof.
  induction barg; simpl; intros Hpq Hforall; auto.
  - apply Hpq; auto. constructor.
  - destruct Hforall as [H1 H2]; split.
    + apply IHbarg1; auto.
      intros a Ha Hin. apply Hpq; auto. constructor; auto.
    + apply IHbarg2; auto.
      intros a Ha Hin. apply Hpq; auto.
      apply in_builtin_arg_splitlong_lo; auto.
  - destruct Hforall as [H1 H2]; split.
    + apply IHbarg1; auto.
      intros a Ha Hin. apply Hpq; auto. constructor; auto.
    + apply IHbarg2; auto.
      intros a Ha Hin. apply Hpq; auto.
      apply in_builtin_arg_addptr_a2; auto.
Qed.

Lemma in_builtin_res_forall {A : Type} (P : A -> Prop) bres x :
  builtin_res_forall P bres ->
  in_builtin_res x bres ->
  P x.
Proof.
  revert x; induction bres; simpl; intros y Hforall Hin; inv Hin; auto;
    destruct Hforall as [H1 H2]; auto.
Qed.
