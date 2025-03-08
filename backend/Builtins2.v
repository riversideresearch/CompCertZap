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
| BI_smove_float.

Local Open Scope string_scope.

Definition replicate_builtin_table : list (string * replicate_builtin) :=
  ("__smove_int", BI_smove_int)
    :: ("__smove_long", BI_smove_long)
    :: ("__smove_single", BI_smove_single)
    :: ("__smove_float", BI_smove_float)
  :: nil.


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

Definition replicate_builtin_sem (b: replicate_builtin)
  : builtin_sem (sig_res (replicate_builtin_sig b)) :=
  match b with
  | BI_smove_int => smove_int_sem
  | BI_smove_long => smove_long_sem
  | BI_smove_single => smove_single_sem
  | BI_smove_float => smove_float_sem
  end.
