Require Import Coq.Classes.Morphisms_Prop.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetDecide.

Set Implicit Arguments.
Unset Strict Implicit.

(** ** An axiomatization of infinite types. *)
(**
A type T is infinite if, for any finite set X of inhabitants of T,
there exists an inhabitant of T not in X.
*)
Module InfiniteType.

  Module Type S (E : DecidableType) (S : WSetsOn E).
    Axiom outside : forall s, exists x, ~ S.In x s.
  End S.

  Module Type INHABITED (Import T : Typ).
    Parameter inhabitant : t.
  End INHABITED.

  Module Type SUCC (Import T : Typ) (Import Lt : HasLt T).
    Parameter succ : t -> t.
    Axiom lt_succ_diag_r : forall n, lt n (succ n).
  End SUCC.

  (**
  Any inhabited ordered type with a successor function is infinite.
  *)
  Module Make (E : OrderedType)
      (Import Inh : INHABITED E)
      (Import Suc : SUCC E E)
      (Import S : SetsOn E) <: S E S.

    Lemma outside s : exists x, ~ In x s.
    Proof.
      exists (match max_elt s with Some n => succ n | None => inhabitant end).
      destruct (max_elt s) as [n|] eqn:M.
      { intros S. apply (max_elt_spec2 M S). apply lt_succ_diag_r. }
      { apply max_elt_spec3 in M. intros ?. now apply (M inhabitant). }
    Qed.

  End Make.

End InfiniteType.

(** ** Module types for possibly infinite sets *)

Module Type IWSetsCoreOn (E : DecidableType).

  Notation elt := E.t (only parsing).

  Parameter t : Type.

  (*
  Compared to [WSetsOn], we add [top], [is_top]; drop <<fold>>,
  <<for_all>>, <<exists_>>, <<filter>>, <<partition>>, <<cardinal>>,
  <<elements>>, <<choose>>; and relegate the quantifiers <<Forall>>,
  <<Exists>> to derived notions.

  A natural extension (not yet needed) would be tools like <<is_finite
  : t -> bool>>, <<Finite : t -> Prop>>, with (say) <<choose : forall
  X, Finite X -> t>> picking an <<x>> not in <<X>>.
  *)
  Parameter empty : t.
  Parameter is_empty : t -> bool.
  Parameter top : t.
  Parameter is_top : t -> bool.
  Parameter mem : elt -> t -> bool.
  Parameter add : elt -> t -> t.
  Parameter singleton : elt -> t.
  Parameter remove : elt -> t -> t.
  Parameter union : t -> t -> t.
  Parameter inter : t -> t -> t.
  Parameter diff : t -> t -> t.
  Parameter equal : t -> t -> bool.
  Parameter subset : t -> t -> bool.

  Parameter In : elt -> t -> Prop.
  Parameter In_proper_weak : Proper (E.eq ==> eq ==> iff) In.

  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition Top s := forall a : elt, In a s.

  Section Spec.
    Variable s s': t.
    Variable x y : elt.
    Parameter mem_spec : mem x s = true <-> In x s.
    Parameter equal_spec : equal s s' = true <-> Equal s s'.
    Parameter subset_spec : subset s s' = true <-> Subset s s'.
    Parameter empty_spec : Empty empty.
    Parameter is_empty_spec : is_empty s = true <-> Empty s.
    Parameter top_spec : Top top.
    Parameter is_top_spec : is_top s = true <-> Top s.
    Parameter add_spec : In y (add x s) <-> E.eq y x \/ In y s.
    Parameter remove_spec : In y (remove x s) <-> In y s /\ ~E.eq y x.
    Parameter singleton_spec : In y (singleton x) <-> E.eq y x.
    Parameter union_spec : In x (union s s') <-> In x s \/ In x s'.
    Parameter inter_spec : In x (inter s s') <-> In x s /\ In x s'.
    Parameter diff_spec : In x (diff s s') <-> In x s /\ ~In x s'.
  End Spec.
End IWSetsCoreOn.

(** ** Derived notions *)

Module Type IWSetsDerivedOn (E : DecidableType) (Import Core : IWSetsCoreOn E).

  Notation eq := Equal (only parsing).

  Definition Forall (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.

  #[global] Hint Opaque
    empty is_empty top is_top mem add singleton remove union inter
    diff equal subset
    In Equal Subset Empty Top Forall Exists
  : typeclass_instances.

  #[global] Instance equal_equiv : Equivalence Equal.
  Proof. firstorder. Qed.

  #[global] Instance subset_preorder : PreOrder Subset.
  Proof. firstorder. Qed.

  (** *** Setoids *)
  (* We don't bother with [Params] instances since they're all zero. *)

  #[global] Instance In_proper : Proper (E.eq ==> Equal ==> iff) In.
  Proof.
    intros x1 ?? ?? EQX. rewrite (EQX x1). now apply In_proper_weak.
  Qed.
  #[global] Instance In_mono : Proper (E.eq ==> Subset ==> impl) In.
  Proof.
    intros ?? EQx ?? EQX Hx. apply EQX. now rewrite <-EQx.
  Qed.
  #[global] Instance In_flip_mono : Proper (E.eq ==> flip Subset ==> flip impl) In.
  Proof.
    intros ?? EQx ?? EQX Hx. apply EQX. now rewrite EQx.
  Qed.

  #[global] Instance Subset_proper : Proper (Equal ==> Equal ==> iff) Subset.
  Proof. repeat intro. firstorder. Qed.
  #[global] Instance Subset_mono : Proper (flip Subset ==> Subset ==> impl) Subset.
  Proof. repeat intro. firstorder. Qed.
  #[global] Instance Subset_flip_mono : Proper (Subset ==> flip Subset ==> flip impl) Subset.
  Proof. Fail apply _. repeat intro. firstorder. Qed.

  #[global] Instance Empty_proper : Proper (Equal ==> iff) Empty.
  Proof. repeat intro. firstorder. Qed.
  #[global] Instance Empty_mono : Proper (flip Subset ==> impl) Empty.
  Proof. repeat intro. firstorder. Qed.
  #[global] Instance Empty_flip_mono : Proper (Subset ==> flip impl) Empty.
  Proof. repeat intro. firstorder. Qed.

  #[global] Instance Top_proper : Proper (Equal ==> iff) Top.
  Proof. repeat intro. firstorder. Qed.
  #[global] Instance Top_mono : Proper (Subset ==> impl) Top.
  Proof. repeat intro. firstorder. Qed.
  #[global] Instance Top_flip_mono : Proper (flip Subset ==> flip impl) Top.
  Proof. repeat intro. firstorder. Qed.

  #[global] Instance Forall_proper :
    Proper (pointwise_relation _ iff ==> Equal ==> iff) Forall.
  Proof.
    intros P1 P2 EQP X1 X2 EQX. apply all_iff_morphism. intros x.
    now rewrite (EQP x), (EQX x).
  Qed.
  #[global] Instance Forall_mono :
    Proper (pointwise_relation _ impl ==> Equal ==> impl) Forall.
  Proof.
    intros P1 P2 EQP X1 X2 EQX. apply all_impl_morphism. intros x.
    now rewrite (EQP x), (EQX x).
  Qed.
  #[global] Instance Forall_flip_mono :
    Proper (pointwise_relation _ (flip impl) ==> Equal ==> flip impl) Forall.
  Proof.
    intros P1 P2 EQP X1 X2 EQX. apply all_impl_morphism. intros x.
    now rewrite (EQP x), (EQX x).
  Qed.

  #[global] Instance Exists_proper :
    Proper (pointwise_relation _ iff ==> Equal ==> iff) Exists.
  Proof.
    intros P1 P2 EQP X1 X2 EQX. apply ex_iff_morphism. intros x.
    now rewrite (EQP x), (EQX x).
  Qed.
  #[global] Instance Exists_mono :
    Proper (pointwise_relation _ impl ==> Equal ==> impl) Exists.
  Proof.
    intros P1 P2 EQP X1 X2 EQX. apply ex_impl_morphism. intros x.
    now rewrite (EQP x), (EQX x).
  Qed.
  #[global] Instance Exists_flip_mono :
    Proper (pointwise_relation _ (flip impl) ==> Equal ==> flip impl) Exists.
  Proof.
    intros P1 P2 EQP X1 X2 EQX. apply ex_impl_morphism. intros x.
    now rewrite (EQP x), (EQX x).
  Qed.

  (** *** Sumbool *)

  Local Tactic Notation "decide" "using" open_constr(op)
      open_constr(spec) :=
    destruct op eqn:?; [left | right]; rewrite <- spec; congruence.

  Local Notation DEC P := ({P} + {~ P}) (only parsing).

  Lemma In_dec x X : DEC (In x X).
  Proof. decide using (mem x X) mem_spec. Defined.
  Lemma eq_dec X Y : DEC (Equal X Y).
  Proof. decide using (equal X Y) equal_spec. Defined.
  Lemma subset_dec X Y : DEC (Subset X Y).
  Proof. decide using (subset X Y) subset_spec. Defined.
  Lemma empty_dec X : DEC (Empty X).
  Proof. decide using (is_empty X) is_empty_spec. Defined.
  Lemma top_dec X : DEC (Top X).
  Proof. decide using (is_top X) is_top_spec. Defined.

  (*
  We're chiefly interested in supporting Compcert module types here.
  Compare to Coq.Structures.{Equalities, Orders} and the old Coq.FSets
  interface.
  *)

  (** *** Properties of membership *)

  Lemma not_mem_iff X x : ~ In x X <-> mem x X = false.
  Proof. now rewrite <-mem_spec, not_true_iff_false. Qed.

  (** *** Properties of equality *)

  Lemma eq_refl X : Equal X X.
  Proof. reflexivity. Qed.
  Lemma eq_sym X Y : Equal X Y -> Equal Y X.
  Proof. now symmetry. Qed.
  Lemma eq_trans X Y Z : Equal X Y -> Equal Y Z -> Equal X Z.
  Proof. now transitivity Y. Qed.

  #[global] Hint Immediate eq_sym : core.
  #[global] Hint Resolve eq_refl eq_trans : core.

  Lemma equal_1 X Y : Equal X Y -> equal X Y = true.
  Proof. now rewrite equal_spec. Qed.
  Lemma equal_2 X Y : equal X Y = true -> Equal X Y.
  Proof. now rewrite equal_spec. Qed.

  (** *** Properties of subset *)

  Lemma subset_refl X : Subset X X.
  Proof. reflexivity. Qed.

  Lemma subset_trans X Y Z : Subset X Y -> Subset Y Z -> Subset X Z.
  Proof. now transitivity Y. Qed.

  Lemma subset_antisym X Y : Subset X Y -> Subset Y X -> Equal X Y.
  Proof. firstorder. Qed.

  #[global] Instance subset_antisymmetric : Antisymmetric _ Equal Subset :=
    subset_antisym.

  Lemma subset_equal X Y : Equal X Y -> Subset X Y.
  Proof. firstorder. Qed.

  Lemma subset_empty X : Subset empty X.
  Proof. generalize empty_spec. firstorder. Qed.

  Lemma subset_top X : Subset X top.
  Proof. generalize top_spec. firstorder. Qed.

  (** *** Properties of intersection *)

  Lemma inter_subset_1 X Y : Subset (inter X Y) X.
  Proof. generalize (inter_spec X Y). firstorder. Qed.

  Lemma inter_subset_2 X Y : Subset (inter X Y) Y.
  Proof. generalize (inter_spec X Y). firstorder. Qed.

  Lemma inter_subset_3 X Y Z : Subset Z X -> Subset Z Y -> Subset Z (inter X Y).
  Proof. generalize (inter_spec X Y). firstorder. Qed.

End IWSetsDerivedOn.

(** ** Lift finite sets over infinite types to finite/cofinite sets *)
Module FinCofinCoreOn (E : DecidableType) (S : WSetsOn E)
    (Import Inf : InfiniteType.S E S) <: IWSetsCoreOn E.

  (*
  Modules [WFactsOn] (extra theory) and [WDecideOn] (<<fsetdec>>) are
  handy. Unfortunately, they are not ascribed module types so we
  cannot simply assume implementations.

  This matters because [WFactsOn] declares global [Proper] instances
  and redundant instances can slow down typeclass resolution.
  *)
  Module Import Dec := WDecideOn E S.

  Definition elt := E.t.

  Variant repr : Type :=
  | Fin (s : S.t)
  | Cofin (c : S.t).
  Definition t := repr.

  Definition empty : t := Fin S.empty.

  Definition is_empty (X : t) : bool :=
    match X with
    | Fin s => S.is_empty s
    | Cofin _ => false
    end.

  Definition top : t := Cofin S.empty.

  Definition is_top (X : t) : bool :=
    match X with
    | Cofin c => S.is_empty c
    | Fin _ => false
    end.

  Definition mem (x : elt) (X : t) : bool :=
    match X with
    | Fin s => S.mem x s
    | Cofin c => negb (S.mem x c)
    end.

  Definition add (x : elt) (X : t) : t :=
    match X with
    | Fin s => Fin (S.add x s)
    | Cofin c => Cofin (S.remove x c)
    end.

  Definition singleton (x : elt) : t := Fin (S.singleton x).

  Definition remove (x : elt) (X : t) : t :=
    match X with
    | Fin s => Fin (S.remove x s)
    | Cofin c => Cofin (S.add x c)
    end.

  Definition union (X Y : t) : t :=
    match X, Y with
    | Fin s, Fin t => Fin (S.union s t)
    | Cofin c, Cofin d => Cofin (S.inter c d)
    | Fin s, Cofin c | Cofin c, Fin s => Cofin (S.diff c s)
    end.

  Definition inter (X Y : t) : t :=
    match X, Y with
    | Fin s, Fin t => Fin (S.inter s t)
    | Cofin c, Cofin d => Cofin (S.union c d)
    | Fin s, Cofin c | Cofin c, Fin s => Fin (S.diff s c)
    end.

  Definition diff (X Y : t) : t :=
    match X, Y with
    | Fin s, Fin t => Fin (S.diff s t)
    | Cofin c, Cofin d => Fin (S.diff d c)
    | Fin s, Cofin c => Fin (S.inter s c)
    | Cofin c, Fin s => Cofin (S.union s c)
    end.

  Definition equal (X Y : t) : bool :=
    match X, Y with
    | Fin s, Fin t | Cofin s, Cofin t => S.equal s t
    | Fin _, Cofin _ | Cofin _, Fin _ => false
    end.

  Definition subset (X Y : t) : bool :=
    match X, Y with
    | Fin s, Fin t => S.subset s t
    | Cofin c, Cofin d => S.subset d c
    | Fin s, Cofin c => S.is_empty (S.inter s c)
    | Cofin _, Fin _ => false
    end.

  Definition In (x : elt) (X : t) : Prop :=
    match X with
    | Fin s => S.In x s
    | Cofin c => ~ S.In x c
    end.

  Lemma In_proper_weak : Proper (E.eq ==> eq ==> iff) In.
  Proof.
    intros x y EQ X Y ->. destruct Y; cbn. all: now rewrite EQ.
  Qed.

  Definition Equal X Y : Prop := forall x, In x X <-> In x Y.
  Definition Subset X Y : Prop := forall x, In x X -> In x Y.
  Definition Empty X : Prop := forall x, ~ In x X.
  Definition Top X := forall x, In x X.

  Infix "[=]" := Equal (at level 70, no associativity).
  Infix "[<=]" := Subset (at level 70, no associativity).

  Local Tactic Notation "lift" open_constr(H) :=
    first [ now apply H | fsetdec | split; fsetdec ].

  Lemma mem_spec X x : mem x X = true <-> In x X.
  Proof.
    destruct X; cbn.
    { apply S.mem_spec. }
    { rewrite <- S.mem_spec. now rewrite eq_true_not_negb_iff. }
  Qed.

  Lemma equal_spec X Y : equal X Y = true <-> X [=] Y.
  Proof.
    unfold Equal. destruct X as [s|s], Y as [t|t]; cbn.
    4:{ rewrite S.equal_spec. split; [fsetdec|].
      intros EQ z. specialize (EQ z). fsetdec. }
    1:{ apply S.equal_spec. }
    all: split; [discriminate|].
    all: destruct (outside (S.union s t)) as [w ?].
    all: intros EQ; specialize (EQ w).
    all: fsetdec.
  Qed.

  Definition subset_spec X Y : subset X Y = true <-> X [<=] Y.
  Proof.
    unfold Subset. destruct X as [s|s], Y as [t|t]; cbn.
    { apply S.subset_spec. }
    { rewrite S.is_empty_spec. split; [fsetdec|].
      intros SUB x ?. specialize (SUB x). fsetdec. }
    { split; [discriminate|]. intros SUB.
      destruct (outside (S.union s t)) as [w ?].
      specialize (SUB w). fsetdec. }
    { rewrite S.subset_spec. split; [fsetdec|].
      intros SUB z. specialize (SUB z). fsetdec. }
  Qed.

  Lemma empty_spec : Empty empty.
  Proof. apply S.empty_spec. Qed.

  Lemma is_empty_spec X : is_empty X = true <-> Empty X.
  Proof.
    destruct X as [?|c]; cbn.
    { apply S.is_empty_spec. }
    { split; [discriminate|]. intros E. exfalso.
      destruct (outside c) as [w ?]. now apply (E w). }
  Qed.

  Lemma top_spec : Top top.
  Proof. apply S.empty_spec. Qed.

  Lemma is_top_spec X : is_top X = true <-> Top X.
  Proof.
    unfold Top. destruct X as [s|?]; cbn.
    { split; [discriminate|]. intros T. exfalso.
      destruct (outside s) as [w Hw]. apply Hw, T. }
    { apply S.is_empty_spec. }
  Qed.

  Lemma add_spec X x y : In y (add x X) <-> E.eq y x \/ In y X.
  Proof.
    destruct X; cbn; lift S.add_spec.
  Qed.

  Lemma remove_spec X x y : In y (remove x X) <-> In y X /\ ~ E.eq y x.
  Proof.
    destruct X; cbn; lift S.remove_spec.
  Qed.

  Lemma singleton_spec x y : In y (singleton x) <-> E.eq y x.
  Proof. apply S.singleton_spec. Qed.

  Lemma union_spec X Y x : In x (union X Y) <-> In x X \/ In x Y.
  Proof.
    destruct X, Y; cbn; lift S.union_spec.
  Qed.

  Lemma inter_spec X Y x : In x (inter X Y) <-> In x X /\ In x Y.
  Proof.
    destruct X, Y; cbn; lift S.inter_spec.
  Qed.

  Lemma diff_spec X Y x : In x (diff X Y) <-> In x X /\ ~ In x Y.
  Proof.
    destruct X, Y; cbn; lift S.diff_spec.
  Qed.

End FinCofinCoreOn.

(** ** Questionable bundling *)

Module Type IWSetsOn (E : DecidableType) :=
  IWSetsCoreOn E <+ IWSetsDerivedOn E.

Module FinCofinOn (E : DecidableType) (S : WSetsOn E)
    (Import Inf : InfiniteType.S E S) <: IWSetsOn E.
  Include FinCofinCoreOn E S Inf.
  Include IWSetsDerivedOn E.
End FinCofinOn.
