(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(* *********************************************************************)

(** Shared helper definitions for the CompCertZap fault-tolerance
    development.  These are backend-specific utilities, but they are
    not part of the core RTL syntax or semantics. *)

Require Import Coqlib AST Events Op Registers Locations.

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

Fixpoint in_builtin_largb (r : loc) (barg : builtin_arg loc) : bool :=
  match barg with
  | BA r' => Locset.MF.eqb r r'
  | BA_splitlong hi lo => in_builtin_largb r hi || in_builtin_largb r lo
  | BA_addptr a b => in_builtin_largb r a || in_builtin_largb r b
  | _ => false
  end.

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
    + left. constructor.
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


Lemma in_builtin_largb_spec (r : loc) (barg : builtin_arg loc) :
  reflect (in_builtin_arg r barg) (in_builtin_largb r barg).
Proof.
  induction barg; simpl; try solve [right; intro HC; inv HC].
  unfold Locset.MF.eqb.
  - destruct (Locset.MF.eq_dec r x).
    + left. rewrite e. constructor.
    + right. unfold not in n. intro HC. inv HC. auto.
  - destruct IHbarg1; simpl.
    + left. constructor. auto.
    + destruct IHbarg2; simpl.
      * left; solve [constructor; auto].
      * right; intro HC; inv HC; contradiction.
  - destruct IHbarg1; simpl.
    + left; constructor; auto.
    + destruct IHbarg2; simpl.
      * left; solve [constructor; auto].
      * right; intro HC; inv HC; contradiction.
Qed.


Lemma in_builtin_largb_sound (r : loc) (barg : builtin_arg loc) :
  in_builtin_largb r barg = true -> in_builtin_arg r barg.
Proof. destruct (in_builtin_largb_spec r barg); congruence. Qed.

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

(** * Condition classifiers used by the fault model *)

Inductive is_compu : condition -> Prop :=
| is_compu_CCompu : forall c, is_compu (Ccompu c)
| is_compu_CCompuimm : forall c n, is_compu (Ccompuimm c n).

Inductive is_complu : condition -> Prop :=
| is_compu_CComplu : forall c, is_complu (Ccomplu c)
| is_compu_CCompluimm : forall c n, is_complu (Ccompluimm c n).

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
