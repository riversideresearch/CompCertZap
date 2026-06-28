Require Import String Coqlib.
Require Import AST Floats Integers Values.
Require Import Builtins0.
Import ListNotations.

Local Open Scope asttyp_scope.

(* Definition ptr64 := Archi.ptr64. *)
(* Global Opaque ptr64. *)

Inductive replicate_builtin : Type :=
| BI_smove_int_green
| BI_smove_long_green
| BI_smove_single_green
| BI_smove_float_green
| BI_smove_int_blue
| BI_smove_long_blue
| BI_smove_single_blue
| BI_smove_float_blue
| BI_vote_int
| BI_vote_long
| BI_vote_single
| BI_vote_float
| BI_check_int
| BI_check_long
| BI_check_single
| BI_check_float.

Definition eq_replicate_builtin: forall (x y: replicate_builtin), {x=y} + {x<>y}.
Proof.
  decide equality.
Defined.

Local Open Scope string_scope.

Definition replicate_builtin_table : list (string * replicate_builtin) :=
  [("__builtin_smove_int_green", BI_smove_int_green);
   ("__builtin_smove_long_green", BI_smove_long_green);
   ("__builtin_smove_single_green", BI_smove_single_green);
   ("__builtin_smove_float_green", BI_smove_float_green);
   ("__builtin_smove_int_blue", BI_smove_int_blue);
   ("__builtin_smove_long_blue", BI_smove_long_blue);
   ("__builtin_smove_single_blue", BI_smove_single_blue);
   ("__builtin_smove_float_blue", BI_smove_float_blue);
   ("__builtin_vote_int", BI_vote_int);
   ("__builtin_vote_long", BI_vote_long);
   ("__builtin_vote_single", BI_vote_single);
   ("__builtin_vote_float", BI_vote_float);
   ("__builtin_check_int", BI_check_int);
   ("__builtin_check_long", BI_check_long);
   ("__builtin_check_single", BI_check_single);
   ("__builtin_check_float", BI_check_float)].

Definition replicate_builtin_sig (b: replicate_builtin) : signature :=
  match b with
  | BI_smove_int_green | BI_smove_int_blue =>
      [Xint ---> Xint]
  | BI_smove_long_green | BI_smove_long_blue =>
      [Xlong ---> Xlong]
  | BI_smove_single_green | BI_smove_single_blue =>
      [Xsingle ---> Xsingle]
  | BI_smove_float_green | BI_smove_float_blue =>
      [Xfloat ---> Xfloat]
  | BI_vote_int =>
      [Xint; Xint; Xint ---> Xint]
  | BI_vote_long =>
      [Xlong; Xlong; Xlong ---> Xlong]
  | BI_vote_single =>
      [Xsingle; Xsingle; Xsingle ---> Xsingle]
  | BI_vote_float =>
      [Xfloat; Xfloat; Xfloat ---> Xfloat]
  | BI_check_int =>
      [Xint; Xint ---> Xvoid]
  | BI_check_long =>
      [Xlong; Xlong ---> Xvoid]
  | BI_check_single =>
      [Xsingle; Xsingle ---> Xvoid]
  | BI_check_float =>
      [Xfloat; Xfloat ---> Xvoid]
  end.

Program Definition smove_int_sem : builtin_sem Xint :=
  {| bs_sem := fun vs => match vs with
                      | [x] => match x with
                              | Vint i => Some (Vint i)
                              | Vptr b ofs => if Archi.ptr64
                                             then Some Vundef
                                             else Some (Vptr b ofs)
                              | _ => Some Vundef
                              end
                      | _ => None
                      end
  |}.
Solve Obligations with try solve [split; congruence].
Next Obligation. Qed.
Next Obligation. Qed.
Next Obligation.
  unfold val_opt_has_rettype.
  destruct vl; auto.
  destruct vl; auto.
  destruct v; simpl; auto.
  destruct Archi.ptr64; auto.
Qed.
Next Obligation.
  unfold val_opt_inject.
  destruct vl; auto; inv H.
  destruct vl; auto; inv H4.
  destruct Archi.ptr64.
  - destruct v; auto; try solve [destruct v'; auto].
    inv H2; auto.
  - destruct v; auto; try solve [destruct v'; auto].
    + inv H2; auto.
    + inv H2; econstructor; eauto.
Qed.

Program Definition smove_long_sem : builtin_sem Xlong :=
  {| bs_sem := fun vs => match vs with
                      | [x] => match x with
                              | Vlong i => Some (Vlong i)
                              | Vptr b ofs => if Archi.ptr64
                                             then Some (Vptr b ofs)
                                             else Some Vundef
                              | _ => Some Vundef
                              end
                      | _ => None
                      end
  |}.
Solve Obligations with try solve [split; congruence].
Next Obligation. Qed.
Next Obligation. Qed.
Next Obligation.
  unfold val_opt_has_rettype.
  destruct vl; auto.
  destruct vl; auto.
  destruct v; simpl; auto.
  destruct Archi.ptr64; auto.
Qed.
Next Obligation.
  unfold val_opt_inject.
  destruct vl; auto; inv H.
  destruct vl; auto; inv H4.
  destruct Archi.ptr64.
  - destruct v; auto; try solve [destruct v'; auto].
    + inv H2; auto.
    + inv H2; econstructor; eauto.
  - destruct v; auto; try solve [destruct v'; auto].
    inv H2; auto.
Qed.

Program Definition smove_single_sem : builtin_sem Xsingle :=
  {| bs_sem := fun vs => match vs with
                      | [x] => match x with
                              | Vsingle f => Some (Vsingle f)
                              | _ => Some Vundef
                              end
                      | _ => None
                      end
  |}.
Solve Obligations with try solve [split; congruence].
Next Obligation.
  unfold val_opt_has_rettype.
  destruct vl; auto.
  destruct vl; auto.
  destruct v; simpl; auto.
Qed.
Next Obligation.
  unfold val_opt_inject.
  destruct vl; auto; inv H.
  destruct vl; auto; inv H4.
  destruct v; auto; try solve [destruct v'; auto].
  inv H2; auto.
Qed.

Program Definition smove_float_sem : builtin_sem Xfloat :=
  {| bs_sem := fun vs => match vs with
                      | [x] => match x with
                              | Vfloat f => Some (Vfloat f)
                              | _ => Some Vundef
                              end
                      | _ => None
                      end
  |}.
Solve Obligations with try solve [split; congruence].
Next Obligation.
  unfold val_opt_has_rettype.
  destruct vl; auto.
  destruct vl; auto.
  destruct v; simpl; auto.
Qed.
Next Obligation.
  unfold val_opt_inject.
  destruct vl; auto; inv H.
  destruct vl; auto; inv H4.
  destruct v; auto; try solve [destruct v'; auto].
  inv H2; auto.
Qed.

(** 2-vote *)

Definition vote (t : typ) (a b c : val) : val :=
  if Val.has_type_dec a t && (Val.eq a b || Val.eq a c)
  then a
  else if Val.has_type_dec b t && Val.eq b c
       then b
       else Vundef.

Lemma vote_well_typed t a b c :
  Val.has_rettype (vote t a b c) (inj_type t).
Proof.
  unfold Val.has_rettype, vote.
  destruct t;
    repeat destruct (Val.eq _ _); subst; simpl; auto; try contradiction;
    try destruct a; try destruct b; try destruct c;
    simpl; auto; destruct (bool_dec _ _) eqn:Hb; simpl; auto.
Qed.

Lemma vote_compat_inject t j v1 v1' v2 v2' v3 v3' :
  Val.inject j v1 v1' ->
  Val.inject j v2 v2' ->
  Val.inject j v3 v3' ->
  Val.inject j (vote t v1 v2 v3) (vote t v1' v2' v3').
Proof.
  unfold vote.
  intros H0 H1 H2.
  destruct t; repeat destruct (Val.eq _ _);
    inv H0; simpl; auto; inv H1; simpl; auto; inv H2; simpl; auto;
    try congruence; try destruct (Val.has_type_dec _ _); simpl; auto;
    try destruct (bool_dec _ _) eqn:Hb; simpl; auto; econstructor; eauto.
Qed.

Definition vote_sem (t : typ) : builtin_sem (inj_type t) :=
  mkbuiltin_v3t (inj_type t) (vote t) (vote_well_typed t) (vote_compat_inject t).

(** 3-vote *)

Definition vote3 (t : typ) (a b c : val) : val :=
  if Val.has_type_dec a t && Val.eq a b && Val.eq a c
  then a
  else Vundef.

Lemma vote3_well_typed t a b c :
  Val.has_rettype (vote3 t a b c) (inj_type t).
Proof.
  unfold Val.has_rettype, vote3.
  destruct t;
    repeat destruct (Val.eq _ _); subst; simpl; auto; try contradiction;
    try destruct a; try destruct b; try destruct c;
    simpl; auto; destruct (bool_dec _ _) eqn:Hb; simpl; auto.
Qed.

Lemma vote3_compat_inject t j v1 v1' v2 v2' v3 v3' :
  Val.inject j v1 v1' ->
  Val.inject j v2 v2' ->
  Val.inject j v3 v3' ->
  Val.inject j (vote3 t v1 v2 v3) (vote3 t v1' v2' v3').
Proof.
  unfold vote3.
  intros H0 H1 H2.
  destruct t; repeat destruct (Val.eq _ _);
    inv H0; simpl; auto; inv H1; simpl; auto; inv H2; simpl; auto;
    try congruence; try destruct (Val.has_type_dec _ _); simpl; auto;
    try destruct (bool_dec _ _) eqn:Hb; simpl; auto; econstructor; eauto.
Qed.

Definition vote3_sem (t : typ) : builtin_sem (inj_type t) :=
  mkbuiltin_v3t (inj_type t) (vote3 t) (vote3_well_typed t) (vote3_compat_inject t).

(** Stuff for switching vote type (2- or 3-vote). *)

Record vote_sems : Type :=
  { vote_sem_int : builtin_sem Xint
  ; vote_sem_long : builtin_sem Xlong
  ; vote_sem_single : builtin_sem Xsingle
  ; vote_sem_float : builtin_sem Xfloat
  }.

Inductive vote_type : Type :=
| Two
| Three.

Definition vote_eqb (v1 v2 : vote_type) : bool :=
  match v1, v2 with
  | Two, Two => true
  | Three, Three => true
  | _, _ => false
  end.

Definition vote_type_sem (vty: vote_type) : vote_sems :=
  match vty with
  | Two => {| vote_sem_int := vote_sem Tint
            ; vote_sem_long := vote_sem Tlong
            ; vote_sem_single := vote_sem Tsingle
            ; vote_sem_float := vote_sem Tfloat |}
  | Three => {| vote_sem_int := vote3_sem Tint
              ; vote_sem_long := vote3_sem Tlong
              ; vote_sem_single := vote3_sem Tsingle
              ; vote_sem_float := vote3_sem Tfloat |}
  end.

(* When all three arguments are equal, the output is equal to them. *)
Definition vote_sem_ok {tret: xtype} (sem : builtin_sem tret) : Prop :=
  forall a, Val.has_rettype a tret -> sem.(bs_sem _) [a; a; a] = Some a.

Class VoteSemantics (vty : vote_type) : Prop :=
  { vote_sem_int_ok : vote_sem_ok (vote_type_sem vty).(vote_sem_int)
  ; vote_sem_long_ok : vote_sem_ok (vote_type_sem vty).(vote_sem_long)
  ; vote_sem_single_ok : vote_sem_ok (vote_type_sem vty).(vote_sem_single)
  ; vote_sem_float_ok : vote_sem_ok (vote_type_sem vty).(vote_sem_float)
  }.

Section VOTE_SEMANTICS.

#[export]
Program Instance VoteSemantics_Two : VoteSemantics Two.
Next Obligation.
  intros a Ha; simpl; f_equal; unfold vote.
  destruct a; auto; try contradiction.
  - destruct (Val.eq _ _); simpl; congruence.
  - simpl in *; rewrite Ha; simpl.
    destruct (Val.eq _ _); simpl; congruence.
Qed.
Next Obligation.
  intros a Ha; simpl; f_equal; unfold vote.
  destruct a; auto; try contradiction.
  - destruct (Val.eq _ _); simpl; congruence.
  - simpl in *; rewrite Ha; simpl.
    destruct (Val.eq _ _); simpl; congruence.
Qed.
Next Obligation.
  intros a Ha; simpl; f_equal; unfold vote.
  destruct a; auto; try contradiction.
  destruct (Val.eq _ _); simpl; congruence.
Qed.
Next Obligation.
  intros a Ha; simpl; f_equal; unfold vote.
  destruct a; auto; try contradiction.
  destruct (Val.eq _ _); simpl; congruence.
Qed.

(* #[export] *)
Program Instance VoteSemantics_Three : VoteSemantics Three.
Next Obligation.
  intros a Ha; simpl; f_equal; unfold vote3.
  destruct a; auto; try contradiction.
  - destruct (Val.eq _ _); simpl; congruence.
  - simpl in *; rewrite Ha; simpl.
    destruct (Val.eq _ _); simpl; congruence.
Qed.
Next Obligation.
  intros a Ha; simpl; f_equal; unfold vote3.
  destruct a; auto; try contradiction.
  - destruct (Val.eq _ _); simpl; congruence.
  - simpl in *; rewrite Ha; simpl.
    destruct (Val.eq _ _); simpl; congruence.
Qed.
Next Obligation.
  intros a Ha; simpl; f_equal; unfold vote3.
  destruct a; auto; try contradiction.
  destruct (Val.eq _ _); simpl; congruence.
Qed.
Next Obligation.
  intros a Ha; simpl; f_equal; unfold vote3.
  destruct a; auto; try contradiction.
  destruct (Val.eq _ _); simpl; congruence.
Qed.

End VOTE_SEMANTICS.

Lemma vote3_lessdef_vote (t : typ) (x y z : val) :
  Val.lessdef (vote3 t x y z) (vote t x y z).
Proof.
  unfold vote3, vote.
  destruct t; repeat destruct (Val.eq _ _); subst; simpl;
    destruct z; simpl; auto;
    try destruct x; try destruct y; simpl; auto; try congruence; try constructor; destruct (bool_dec _ _); simpl; try constructor.
Qed.

(** ******************)
(** DMR checks. *)

Definition check (x y : val) : val := Vundef.

Lemma check_well_typed x y :
  Val.has_rettype (check x y) Xvoid.
Proof. apply I. Qed.

Lemma check_compat_inject j v1 v1' v2 v2' :
  Val.inject j v1 v1' ->
  Val.inject j v2 v2' ->
  Val.inject j (check v1 v2) (check v1' v2').
Proof. auto. Qed.

Definition check_sem : builtin_sem Xvoid :=
  mkbuiltin_v2t Xvoid check check_well_typed check_compat_inject.

Definition replicate_builtin_sem {VT: vote_type} `{VoteSemantics VT}
  (b: replicate_builtin)
  : builtin_sem (sig_res (replicate_builtin_sig b)) :=
  match b with
  | BI_smove_int_green => smove_int_sem
  | BI_smove_long_green => smove_long_sem
  | BI_smove_single_green => smove_single_sem
  | BI_smove_float_green => smove_float_sem
  | BI_smove_int_blue => smove_int_sem
  | BI_smove_long_blue => smove_long_sem
  | BI_smove_single_blue => smove_single_sem
  | BI_smove_float_blue => smove_float_sem
  | BI_vote_int => (vote_type_sem VT).(vote_sem_int)
  | BI_vote_long => (vote_type_sem VT).(vote_sem_long)
  | BI_vote_single => (vote_type_sem VT).(vote_sem_single)
  | BI_vote_float => (vote_type_sem VT).(vote_sem_float)
  | BI_check_int => check_sem
  | BI_check_long => check_sem
  | BI_check_single => check_sem
  | BI_check_float => check_sem
  end.
