Require Import String Coqlib.
Require Import AST Values.
(* Integers Floats Values Memdata. *)
Require Import Builtins0.
Import ListNotations.

Local Open Scope asttyp_scope.

Inductive replicate_builtin : Type :=
| BI_smove_int
| BI_smove_long
| BI_smove_single
| BI_smove_float
| BI_vote_int
| BI_vote_long
| BI_vote_single
| BI_vote_float.

Local Open Scope string_scope.

(* Definition replicate_builtin_table : list (string * replicate_builtin) := *)
(*   ("__smove_int", BI_smove_int) *)
(*     :: ("__smove_long", BI_smove_long) *)
(*     :: ("__smove_single", BI_smove_single) *)
(*     :: ("__smove_float", BI_smove_float) *)
(*     :: nil. *)

Definition replicate_builtin_table : list (string * replicate_builtin) :=
  [("__smove_int", BI_smove_int);
   ("__smove_long", BI_smove_long);
   ("__smove_single", BI_smove_single);
   ("__smove_float", BI_smove_float);
   ("__vote_int", BI_vote_int);
   ("__vote_long", BI_vote_long);
   ("__vote_single", BI_vote_single);
   ("__vote_float", BI_vote_float)].

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

(* Program Definition smove_int_sem : builtin_sem Xint := *)
(*   {| bs_sem := fun vs => match vs with *)
(*                       | [x] => match x with *)
(*                               | Vint i => Some (Vint i) *)
(*                               | Vptr b ofs => if Archi.ptr64 *)
(*                                              then None *)
(*                                              else Some (Vptr b ofs) *)
(*                               | Vundef => Some Vundef *)
(*                               | _ => None *)
(*                               end *)
(*                       | _ => None *)
(*                       end *)
(*   |}. *)
(* Solve Obligations with try solve [repeat split; congruence]. *)
(* Next Obligation. Qed. *)
(* Next Obligation. Qed. *)
(* Next Obligation. *)
(*   unfold val_opt_has_rettype. *)
(*   destruct vl; auto. *)
(*   destruct vl; auto. *)
(*   destruct v; simpl; auto. *)
(*   destruct Archi.ptr64; auto. *)
(* Qed. *)
(* Next Obligation. *)
(*   unfold val_opt_inject. *)
(*   destruct vl; auto; inv H. *)
(*   destruct vl; auto; inv H4. *)
(*   destruct Archi.ptr64. *)
(*   - destruct v; auto; try solve [destruct v'; auto]. *)
(*     + destruct v'; auto. *)
(*     + inv H2; auto. *)
(*   - destruct v; auto; try solve [destruct v'; auto]. *)
(*     + inv H2; auto. *)
(*     + inv H2; econstructor; eauto. *)
(* Qed. *)

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

(* Program Definition vote_int_sem : builtin_sem Xint := *)
(*   {| bs_sem := fun vs => match vs with *)
(*                       | [x; y; z] => *)
(*                           match (x, y, z) with *)
(*                           | (Vint a, Vint b, Vint c) => Some (Vint a) *)
(*                           | (Vptr a i, Vptr b j, Vptr c k) => *)
(*                               if Archi.ptr64 *)
(*                               then Some Vundef *)
(*                               else Some (Vptr a i) *)
(*                           | _ => Some Vundef *)
(*                           end *)
(*                       | _ => None *)
(*                       end *)
(*   |}. *)

Definition vote_int (x y z : val) : val :=
  if Val.has_type_dec x Tint &&
       Val.has_type_dec y Tint &&
       Val.has_type_dec z Tint then
    if Val.eq x y || Val.eq x z
    then x
    else if Val.eq y z
         then y
         else Vundef
  else
    Vundef.

Lemma vote_int_well_typed x y z :
  Val.has_rettype (vote_int x y z) Xint.
Proof.
  unfold Val.has_rettype.
  unfold vote_int.
  destruct (Val.has_type_dec x Tint); simpl; auto.
  destruct (Val.has_type_dec y Tint); simpl; auto.
  destruct (Val.has_type_dec z Tint); simpl; auto.
  destruct (Val.eq x y); simpl; subst.
  - destruct y; auto.
  - destruct (Val.eq x z); simpl; subst.
    + destruct z; auto.
    + destruct (Val.eq y z); subst; auto.
Qed.

Lemma vote_int_compat_inject j v1 v1' v2 v2' v3 v3' :
  Val.inject j v1 v1' ->
  Val.inject j v2 v2' ->
  Val.inject j v3 v3' ->
  Val.inject j (vote_int v1 v2 v3) (vote_int v1' v2' v3').
Proof.
Admitted.

Definition vote_int_sem : builtin_sem Xint :=
  mkbuiltin_v3t Xint vote_int vote_int_well_typed vote_int_compat_inject.

Definition vote_long (x y z : val) : val :=
  if Val.has_type_dec x Tlong &&
       Val.has_type_dec y Tlong &&
       Val.has_type_dec z Tlong then
    if Val.eq x y || Val.eq x z
    then x
    else if Val.eq y z
         then y
         else Vundef
  else
    Vundef.

Lemma vote_long_well_typed x y z :
  Val.has_rettype (vote_long x y z) Xlong.
Proof.
  unfold Val.has_rettype.
  unfold vote_long.
  destruct (Val.has_type_dec x Tlong); simpl; auto.
  destruct (Val.has_type_dec y Tlong); simpl; auto.
  destruct (Val.has_type_dec z Tlong); simpl; auto.
  destruct (Val.eq x y); simpl; subst.
  - destruct y; auto.
  - destruct (Val.eq x z); simpl; subst.
    + destruct z; auto.
    + destruct (Val.eq y z); subst; auto.
Qed.

Lemma vote_long_compat_inject j v1 v1' v2 v2' v3 v3' :
  Val.inject j v1 v1' ->
  Val.inject j v2 v2' ->
  Val.inject j v3 v3' ->
  Val.inject j (vote_long v1 v2 v3) (vote_long v1' v2' v3').
Proof.
Admitted.

Definition vote_long_sem : builtin_sem Xlong :=
  mkbuiltin_v3t Xlong vote_long vote_long_well_typed vote_long_compat_inject.

Definition vote_single (x y z : val) : val :=
  if Val.has_type_dec x Tsingle &&
       Val.has_type_dec y Tsingle &&
       Val.has_type_dec z Tsingle then
    if Val.eq x y || Val.eq x z
    then x
    else if Val.eq y z
         then y
         else Vundef
  else
    Vundef.

Lemma vote_single_well_typed x y z :
  Val.has_rettype (vote_single x y z) Xsingle.
Proof.
  unfold Val.has_rettype.
  unfold vote_single.
  destruct (Val.has_type_dec x Tsingle); simpl; auto.
  destruct (Val.has_type_dec y Tsingle); simpl; auto.
  destruct (Val.has_type_dec z Tsingle); simpl; auto.
  destruct (Val.eq x y); simpl; subst.
  - destruct y; auto.
  - destruct (Val.eq x z); simpl; subst.
    + destruct z; auto.
    + destruct (Val.eq y z); subst; auto.
Qed.

Lemma vote_single_compat_inject j v1 v1' v2 v2' v3 v3' :
  Val.inject j v1 v1' ->
  Val.inject j v2 v2' ->
  Val.inject j v3 v3' ->
  Val.inject j (vote_single v1 v2 v3) (vote_single v1' v2' v3').
Proof.
Admitted.

Definition vote_single_sem : builtin_sem Xsingle :=
  mkbuiltin_v3t Xsingle vote_single vote_single_well_typed vote_single_compat_inject.

Definition vote_float (x y z : val) : val :=
  if Val.has_type_dec x Tfloat &&
       Val.has_type_dec y Tfloat &&
       Val.has_type_dec z Tfloat then
    if Val.eq x y || Val.eq x z
    then x
    else if Val.eq y z
         then y
         else Vundef
  else
    Vundef.

Lemma vote_float_well_typed x y z :
  Val.has_rettype (vote_float x y z) Xfloat.
Proof.
  unfold Val.has_rettype.
  unfold vote_float.
  destruct (Val.has_type_dec x Tfloat); simpl; auto.
  destruct (Val.has_type_dec y Tfloat); simpl; auto.
  destruct (Val.has_type_dec z Tfloat); simpl; auto.
  destruct (Val.eq x y); simpl; subst.
  - destruct y; auto.
  - destruct (Val.eq x z); simpl; subst.
    + destruct z; auto.
    + destruct (Val.eq y z); subst; auto.
Qed.

Lemma vote_float_compat_inject j v1 v1' v2 v2' v3 v3' :
  Val.inject j v1 v1' ->
  Val.inject j v2 v2' ->
  Val.inject j v3 v3' ->
  Val.inject j (vote_float v1 v2 v3) (vote_float v1' v2' v3').
Proof.
Admitted.

Definition vote_float_sem : builtin_sem Xfloat :=
  mkbuiltin_v3t Xfloat vote_float vote_float_well_typed vote_float_compat_inject.

(* Program Definition vote_int_sem : builtin_sem Xint := *)
(*   {| bs_sem := fun vs => match vs with *)
(*                       | [x; y; z] => *)
(*                           if Val.has_type_dec x Tint && *)
(*                                Val.has_type_dec y Tint && *)
(*                                Val.has_type_dec z Tint then *)
(*                             if Val.eq x y || Val.eq x z *)
(*                             then Some x *)
(*                             else if Val.eq y z *)
(*                                  then Some y *)
(*                                  else Some Vundef *)
(*                           else *)
(*                             Some Vundef *)
(*                           | _ => None *)
(*                       end *)
(*   |}. *)
(* Next Obligation. *)
(*   unfold val_opt_has_rettype. *)
(*   destruct vl; auto. *)
(*   destruct vl; auto. *)
(*   destruct vl; auto. *)
(*   destruct vl; auto. *)
(*   destruct (Val.has_type_dec v Tint); simpl; auto. *)
(*   destruct (Val.has_type_dec v0 Tint); simpl; auto. *)
(*   destruct (Val.has_type_dec v1 Tint); simpl; auto. *)
(*   destruct (Val.eq v v0); simpl; subst. *)
(*   - destruct v0; auto. *)
(*   - destruct (Val.eq v v1); simpl; subst. *)
(*     + destruct v1; auto. *)
(*     + destruct (Val.eq v0 v1); subst; auto. *)
(* Qed. *)
(* Next Obligation. *)
(*   unfold val_opt_inject. *)
(*   destruct vl; auto. *)
(*   inv H. *)
(*   destruct vl; auto. *)
(*   inv H4. *)
(*   destruct vl; auto. *)
(*   inv H5. *)
(*   destruct vl; auto. *)
(*   inv H6. *)
(*   destruct (Val.has_type_dec v Tint); simpl; auto. *)
(*   destruct (Val.has_type_dec v0 Tint); simpl; auto. *)
(*   destruct (Val.has_type_dec v1 Tint); simpl; auto. *)
(*   destruct (Val.eq v v0); simpl; subst. *)
(*   - destruct (Val.has_type_dec v' Tint); simpl. *)
(*     + destruct (Val.has_type_dec v'0 Tint); simpl. *)
(*       * destruct (Val.has_type_dec v'1 Tint); simpl. *)
(*         { destruct (Val.eq v' v'0); subst; simpl; auto. *)
(*           destruct (Val.eq v' v'1); subst; simpl; auto. *)
(*           destruct (Val.eq v'0 v'1); subst; auto. *)
(*           destruct v0; auto; inv H2; inv H1; congruence. } *)
(*         destruct v0; auto. *)
(*         { inv H2; inv H1. *)
(*           destruct v1. *)

(*           destruct (Val.eq v' v'0 || Val.eq v' v'1); auto. *)
(*           destruct (Val.eq v'0 v'1); subst; auto. *)
(*           destruct v0; auto. *)
(*           - inv H2; inv H1. *)
(*   - destruct (Val.eq v v1); simpl; subst. *)
(*     + destruct v1; auto. *)
(*     + destruct (Val.eq v0 v1); subst; auto. *)
(* Admitted. *)

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
  end.

(* Inductive smove_sem (ge: Senv.t): *)
(*   list val -> mem -> trace -> val -> mem -> Prop := *)
(*   | smove_sem_int : *)
(*       smove_sem ge [Vint i] m E0 (Vptr b Ptrofs.zero) m''. *)
