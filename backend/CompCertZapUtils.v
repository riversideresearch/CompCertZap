(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(* *********************************************************************)

(** Shared helper definitions for the CompCertZap fault-tolerance
    development.  These are backend-specific utilities, but they are
    not part of the core RTL syntax or semantics. *)

Require Import Coqlib AST Events Op Registers.

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

Lemma in_builtin_res_forall {A : Type} (P : A -> Prop) bres x :
  builtin_res_forall P bres ->
  in_builtin_res x bres ->
  P x.
Proof.
  revert x; induction bres; simpl; intros y Hforall Hin; inv Hin; auto;
    destruct Hforall as [H1 H2]; auto.
Qed.
