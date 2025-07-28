Require Import String Coqlib.
Require Import AST Floats Integers Values.
Require Import Builtins0.
Import ListNotations.

Local Open Scope asttyp_scope.

(* Definition ptr64 := Archi.ptr64. *)
(* Global Opaque ptr64. *)

Inductive replicate_builtin : Type :=
| BI_smove_int
| BI_smove_long
| BI_smove_single
| BI_smove_float
| BI_vote_int
| BI_vote_long
| BI_vote_single
| BI_vote_float
| BI_vote_int3
| BI_vote_long3
| BI_vote_single3
| BI_vote_float3.

Local Open Scope string_scope.

Definition replicate_builtin_table : list (string * replicate_builtin) :=
  [("__builtin_smove_int", BI_smove_int);
   ("__builtin_smove_long", BI_smove_long);
   ("__builtin_smove_single", BI_smove_single);
   ("__builtin_smove_float", BI_smove_float);
   ("__builtin_vote_int", BI_vote_int);
   ("__builtin_vote_long", BI_vote_long);
   ("__builtin_vote_single", BI_vote_single);
   ("__builtin_vote_float", BI_vote_float);
   ("__builtin_vote_int3", BI_vote_int);
   ("__builtin_vote_long3", BI_vote_long);
   ("__builtin_vote_single3", BI_vote_single);
   ("__builtin_vote_float3", BI_vote_float)].

Definition replicate_builtin_sig (b: replicate_builtin) : signature :=
  match b with
  | BI_smove_int =>
      [Xint ---> Xint]
  | BI_smove_long =>
      [Xlong ---> Xlong]
  | BI_smove_single =>
      [Xsingle ---> Xsingle]
  | BI_smove_float =>
      [Xfloat ---> Xfloat]
  | BI_vote_int =>
      [Xint; Xint; Xint ---> Xint]
  | BI_vote_long =>
      [Xlong; Xlong; Xlong ---> Xlong]
  | BI_vote_single =>
      [Xsingle; Xsingle; Xsingle ---> Xsingle]
  | BI_vote_float =>
      [Xfloat; Xfloat; Xfloat ---> Xfloat]
  | BI_vote_int3 =>
      [Xint; Xint; Xint ---> Xint]
  | BI_vote_long3 =>
      [Xlong; Xlong; Xlong ---> Xlong]
  | BI_vote_single3 =>
      [Xsingle; Xsingle; Xsingle ---> Xsingle]
  | BI_vote_float3 =>
      [Xfloat; Xfloat; Xfloat ---> Xfloat]
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

Definition vote_int (x y z : val) : val :=
  match (x, y, z) with
  | (Vint a, Vint b, Vint c) =>
      if Int.eq_dec a b || Int.eq_dec a c
      then x
      else if Int.eq_dec b c
           then y
           else Vundef
  | (Vptr a i, Vptr b j, Vptr c k) =>
      if negb Archi.ptr64
      then if (eq_block a b && Ptrofs.eq_dec i j) ||
                (eq_block a c && Ptrofs.eq_dec i k)
           then x
           else if eq_block b c && Ptrofs.eq_dec j k
                then y
                else Vundef
      else Vundef
  | _ => Vundef
  end.

Lemma vote_int_well_typed x y z :
  Val.has_rettype (vote_int x y z) Xint.
Proof.
  unfold Val.has_rettype, vote_int.
  destruct x, y, z; auto.
  - repeat destruct (Int.eq_dec _ _); simpl; auto.
  - destruct Archi.ptr64 eqn:Harchi; simpl; auto.
    repeat ((try destruct (eq_block _ _); subst; simpl);
            (try destruct (Ptrofs.eq_dec _ _); simpl; auto)).
Qed.

Lemma vote_int_compat_inject j v1 v1' v2 v2' v3 v3' :
  Val.inject j v1 v1' ->
  Val.inject j v2 v2' ->
  Val.inject j v3 v3' ->
  Val.inject j (vote_int v1 v2 v3) (vote_int v1' v2' v3').
Proof.
  unfold vote_int.
  intros H0 H1 H2.
  inv H0; simpl; auto; inv H1; inv H2; simpl; auto;
    (* This is necessary for riscv but not x86_64. Why? *)
    try solve [destruct Archi.ptr64 eqn:Harchi; simpl; auto;
               repeat ((try destruct (eq_block _ _); subst; simpl);
                       (try destruct (Ptrofs.eq_dec _ _); subst; simpl);
                       (try solve [econstructor; eauto; congruence]);
                       (try congruence))].
  repeat destruct (Int.eq_dec _ _); subst; simpl; auto.
Qed.

Definition vote_int_sem : builtin_sem Xint :=
  mkbuiltin_v3t Xint vote_int vote_int_well_typed vote_int_compat_inject.

Definition vote_long (x y z : val) : val :=
  match (x, y, z) with
  | (Vlong a, Vlong b, Vlong c) =>
      if Int64.eq_dec a b || Int64.eq_dec a c
      then x
      else if Int64.eq_dec b c
           then y
           else Vundef
  | (Vptr a i, Vptr b j, Vptr c k) =>
      if Archi.ptr64
      then if (eq_block a b && Ptrofs.eq_dec i j) ||
                (eq_block a c && Ptrofs.eq_dec i k)
           then x
           else if eq_block b c && Ptrofs.eq_dec j k
                then y
                else Vundef
      else Vundef
  | _ => Vundef
  end.

Lemma vote_long_well_typed x y z :
  Val.has_rettype (vote_long x y z) Xlong.
Proof.
  unfold Val.has_rettype, vote_long.
  destruct x, y, z; auto.
  - repeat destruct (Int64.eq_dec _ _); simpl; auto.
  - destruct Archi.ptr64 eqn:Harchi; simpl; auto.
    repeat ((try destruct (eq_block _ _); subst; simpl);
            (try destruct (Ptrofs.eq_dec _ _); simpl; auto)).
Qed.

Lemma vote_long_compat_inject j v1 v1' v2 v2' v3 v3' :
  Val.inject j v1 v1' ->
  Val.inject j v2 v2' ->
  Val.inject j v3 v3' ->
  Val.inject j (vote_long v1 v2 v3) (vote_long v1' v2' v3').
Proof.
  unfold vote_long.
  intros H0 H1 H2.
  inv H0; simpl; auto; inv H1; inv H2; simpl; auto;
    repeat destruct (Int64.eq_dec _ _); subst; simpl; auto;
    destruct Archi.ptr64 eqn:Harchi; simpl; auto;
    repeat ((try destruct (eq_block _ _); subst; simpl);
            (try destruct (Ptrofs.eq_dec _ _); subst; simpl);
            (try solve [econstructor; eauto; congruence]);
            (try congruence)).
Qed.

Definition vote_long_sem : builtin_sem Xlong :=
  mkbuiltin_v3t Xlong vote_long vote_long_well_typed vote_long_compat_inject.

Definition vote_single (x y z : val) : val :=
  match (x, y, z) with
  | (Vsingle a, Vsingle b, Vsingle c) =>
      if Float32.eq_dec a b || Float32.eq_dec a c
      then x
      else if Float32.eq_dec b c
           then y
           else Vundef
  | _ => Vundef
  end.

Lemma vote_single_well_typed x y z :
  Val.has_rettype (vote_single x y z) Xsingle.
Proof.
  unfold Val.has_rettype, vote_single.
  destruct x, y, z; auto.
  repeat destruct (Float32.eq_dec _ _); simpl; auto.
Qed.

Lemma vote_single_compat_inject j v1 v1' v2 v2' v3 v3' :
  Val.inject j v1 v1' ->
  Val.inject j v2 v2' ->
  Val.inject j v3 v3' ->
  Val.inject j (vote_single v1 v2 v3) (vote_single v1' v2' v3').
Proof.
  unfold vote_single.
  intros H0 H1 H2.
  inv H0; simpl; auto.
  inv H1; simpl; auto.
  inv H2; simpl; auto.
  repeat destruct (Float32.eq_dec _ _); simpl; auto.
Qed.

Definition vote_single_sem : builtin_sem Xsingle :=
  mkbuiltin_v3t Xsingle vote_single vote_single_well_typed vote_single_compat_inject.

Definition vote_float (x y z : val) : val :=
  match (x, y, z) with
  | (Vfloat a, Vfloat b, Vfloat c) =>
      if Float.eq_dec a b || Float.eq_dec a c
      then x
      else if Float.eq_dec b c
           then y
           else Vundef
  | _ => Vundef
  end.

Lemma vote_float_well_typed x y z :
  Val.has_rettype (vote_float x y z) Xfloat.
Proof.
  unfold Val.has_rettype, vote_float.
  destruct x, y, z; auto.
  repeat destruct (Float.eq_dec _ _); simpl; auto.
Qed.

Lemma vote_float_compat_inject j v1 v1' v2 v2' v3 v3' :
  Val.inject j v1 v1' ->
  Val.inject j v2 v2' ->
  Val.inject j v3 v3' ->
  Val.inject j (vote_float v1 v2 v3) (vote_float v1' v2' v3').
Proof.
  unfold vote_float.
  intros H0 H1 H2.
  inv H0; simpl; auto.
  inv H1; simpl; auto.
  inv H2; simpl; auto.
  repeat destruct (Float.eq_dec _ _); simpl; auto.
Qed.

Definition vote_float_sem : builtin_sem Xfloat :=
  mkbuiltin_v3t Xfloat vote_float vote_float_well_typed vote_float_compat_inject.

Definition vote_int3 (x y z : val) : val :=
  match (x, y, z) with
  | (Vint a, Vint b, Vint c) =>
      if Int.eq_dec a b && Int.eq_dec b c
      then x
      else Vundef
  | (Vptr a i, Vptr b j, Vptr c k) =>
      if negb Archi.ptr64
      then if (eq_block a b && Ptrofs.eq_dec i j) &&
                (eq_block b c && Ptrofs.eq_dec j k)
           then x
           else Vundef
      else Vundef
  | _ => Vundef
  end.

Lemma vote_int3_well_typed x y z :
  Val.has_rettype (vote_int3 x y z) Xint.
Proof.
  unfold Val.has_rettype, vote_int3.
  destruct x, y, z; auto.
  - repeat destruct (Int.eq_dec _ _); simpl; auto.
  - destruct Archi.ptr64 eqn:Harchi; simpl; auto.
    repeat ((try destruct (eq_block _ _); subst; simpl);
            (try destruct (Ptrofs.eq_dec _ _); simpl; auto)).
Qed.

Lemma vote_int3_compat_inject j v1 v1' v2 v2' v3 v3' :
  Val.inject j v1 v1' ->
  Val.inject j v2 v2' ->
  Val.inject j v3 v3' ->
  Val.inject j (vote_int3 v1 v2 v3) (vote_int3 v1' v2' v3').
Proof.
  unfold vote_int3.
  intros H0 H1 H2.
  inv H0; simpl; auto; inv H1; inv H2; simpl; auto;
    (* This is necessary for riscv but not x86_64. Why? *)
    try solve [destruct Archi.ptr64 eqn:Harchi; simpl; auto;
               repeat ((try destruct (eq_block _ _); subst; simpl);
                       (try destruct (Ptrofs.eq_dec _ _); subst; simpl);
                       (try solve [econstructor; eauto; congruence]);
                       (try congruence))].
  repeat destruct (Int.eq_dec _ _); subst; simpl; auto.
Qed.

Definition vote_int3_sem : builtin_sem Xint :=
  mkbuiltin_v3t Xint vote_int3 vote_int3_well_typed vote_int3_compat_inject.

Definition vote_long3 (x y z : val) : val :=
  match (x, y, z) with
  | (Vlong a, Vlong b, Vlong c) =>
      if Int64.eq_dec a b && Int64.eq_dec b c
      then x
      else Vundef
  | (Vptr a i, Vptr b j, Vptr c k) =>
      if Archi.ptr64
      then if (eq_block a b && Ptrofs.eq_dec i j) &&
                (eq_block b c && Ptrofs.eq_dec j k)
           then x
           else Vundef
      else Vundef
  | _ => Vundef
  end.

Lemma vote_long3_well_typed x y z :
  Val.has_rettype (vote_long3 x y z) Xlong.
Proof.
  unfold Val.has_rettype, vote_long3.
  destruct x, y, z; auto.
  - repeat destruct (Int64.eq_dec _ _); simpl; auto.
  - destruct Archi.ptr64 eqn:Harchi; simpl; auto.
    repeat ((try destruct (eq_block _ _); subst; simpl);
            (try destruct (Ptrofs.eq_dec _ _); simpl; auto)).
Qed.

Lemma vote_long3_compat_inject j v1 v1' v2 v2' v3 v3' :
  Val.inject j v1 v1' ->
  Val.inject j v2 v2' ->
  Val.inject j v3 v3' ->
  Val.inject j (vote_long3 v1 v2 v3) (vote_long3 v1' v2' v3').
Proof.
  unfold vote_long3.
  intros H0 H1 H2.
  inv H0; simpl; auto; inv H1; inv H2; simpl; auto;
    repeat destruct (Int64.eq_dec _ _); subst; simpl; auto;
    destruct Archi.ptr64 eqn:Harchi; simpl; auto;
    repeat ((try destruct (eq_block _ _); subst; simpl);
            (try destruct (Ptrofs.eq_dec _ _); subst; simpl);
            (try solve [econstructor; eauto; congruence]);
            (try congruence)).
Qed.

Definition vote_long3_sem : builtin_sem Xlong :=
  mkbuiltin_v3t Xlong vote_long3 vote_long3_well_typed vote_long3_compat_inject.

Definition vote_single3 (x y z : val) : val :=
  match (x, y, z) with
  | (Vsingle a, Vsingle b, Vsingle c) =>
      if Float32.eq_dec a b && Float32.eq_dec b c
      then x
      else Vundef
  | _ => Vundef
  end.

Lemma vote_single3_well_typed x y z :
  Val.has_rettype (vote_single3 x y z) Xsingle.
Proof.
  unfold Val.has_rettype, vote_single3.
  destruct x, y, z; auto.
  repeat destruct (Float32.eq_dec _ _); simpl; auto.
Qed.

Lemma vote_single3_compat_inject j v1 v1' v2 v2' v3 v3' :
  Val.inject j v1 v1' ->
  Val.inject j v2 v2' ->
  Val.inject j v3 v3' ->
  Val.inject j (vote_single3 v1 v2 v3) (vote_single3 v1' v2' v3').
Proof.
  unfold vote_single3.
  intros H0 H1 H2.
  inv H0; simpl; auto.
  inv H1; simpl; auto.
  inv H2; simpl; auto.
  repeat destruct (Float32.eq_dec _ _); simpl; auto.
Qed.

Definition vote_single3_sem : builtin_sem Xsingle :=
  mkbuiltin_v3t Xsingle vote_single3 vote_single3_well_typed vote_single3_compat_inject.

Definition vote_float3 (x y z : val) : val :=
  match (x, y, z) with
  | (Vfloat a, Vfloat b, Vfloat c) =>
      if Float.eq_dec a b && Float.eq_dec b c
      then x
      else Vundef
  | _ => Vundef
  end.

Lemma vote_float3_well_typed x y z :
  Val.has_rettype (vote_float3 x y z) Xfloat.
Proof.
  unfold Val.has_rettype, vote_float3.
  destruct x, y, z; auto.
  repeat destruct (Float.eq_dec _ _); simpl; auto.
Qed.

Lemma vote_float3_compat_inject j v1 v1' v2 v2' v3 v3' :
  Val.inject j v1 v1' ->
  Val.inject j v2 v2' ->
  Val.inject j v3 v3' ->
  Val.inject j (vote_float3 v1 v2 v3) (vote_float3 v1' v2' v3').
Proof.
  unfold vote_float3.
  intros H0 H1 H2.
  inv H0; simpl; auto.
  inv H1; simpl; auto.
  inv H2; simpl; auto.
  repeat destruct (Float.eq_dec _ _); simpl; auto.
Qed.

Definition vote_float3_sem : builtin_sem Xfloat :=
  mkbuiltin_v3t Xfloat vote_float3 vote_float3_well_typed vote_float3_compat_inject.

Definition replicate_builtin_sem (b: replicate_builtin)
  : builtin_sem (sig_res (replicate_builtin_sig b)) :=
  match b with
  | BI_smove_int => smove_int_sem
  | BI_smove_long => smove_long_sem
  | BI_smove_single => smove_single_sem
  | BI_smove_float => smove_float_sem
  | BI_vote_int => vote_int_sem
  | BI_vote_long => vote_long_sem
  | BI_vote_single => vote_single_sem
  | BI_vote_float => vote_float_sem
  | BI_vote_int3 => vote_int3_sem
  | BI_vote_long3 => vote_long3_sem
  | BI_vote_single3 => vote_single3_sem
  | BI_vote_float3 => vote_float3_sem
  end.

Lemma vote_int3_vote_int (x y z : val) :
  Val.lessdef (vote_int3 x y z) (vote_int x y z).
Proof.
  unfold vote_int3, vote_int.
  destruct x, y, z; auto;
    repeat destruct (Int.eq_dec _ _); auto;
    destruct Archi.ptr64 eqn:Harchi; simpl; auto;
    repeat ((destruct (eq_block _ _); subst; simpl);
            (try destruct (Ptrofs.eq_dec _ _); subst; simpl)); auto.
Qed.

Lemma vote_long3_vote_long (x y z : val) :
  Val.lessdef (vote_long3 x y z) (vote_long x y z).
Proof.
  unfold vote_long3, vote_long.
  destruct x, y, z; auto;
    repeat destruct (Int64.eq_dec _ _); auto;
    destruct Archi.ptr64 eqn:Harchi; simpl; auto;
    repeat ((destruct (eq_block _ _); subst; simpl);
            (try destruct (Ptrofs.eq_dec _ _); subst; simpl)); auto.
Qed.

Lemma vote_single3_vote_single (x y z : val) :
  Val.lessdef (vote_single3 x y z) (vote_single x y z).
Proof.
  unfold vote_single3, vote_single.
  destruct x, y, z; auto.
  repeat destruct (Float32.eq_dec _ _); auto.
Qed.

Lemma vote_float3_vote_float (x y z : val) :
  Val.lessdef (vote_float3 x y z) (vote_float x y z).
Proof.
  unfold vote_float3, vote_float.
  destruct x, y, z; auto.
  repeat destruct (Float.eq_dec _ _); auto.
Qed.
