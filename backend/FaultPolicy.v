(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(* *********************************************************************)

(** Shared fault-model classification policy for operations and builtins. *)

From Coq Require Import String.
Require Import Coqlib.
Require Import AST Builtins Op.

(** * Operation classification *)

(* Design note: maybe we can just assume faulted floats aren't NaN,
   and then the conversions from single/float to int/long will always
   succeed and we can consider them safe?

   It seems that considering NaN conversions to int/long to be
   immediate UB is a CompCert choice that isn't necessarily dictated
   by the C standard. *)
Inductive is_protected : operation -> Prop :=
(* Because division by zero causes immediate UB (see [Val.divs] in
   common/Values.v) *)
| is_protected_Odiv : is_protected Odiv
| is_protected_Odivu : is_protected Odivu
| is_protected_Omod : is_protected Omod
| is_protected_Omodu : is_protected Omodu
| is_protected_Odivl : is_protected Odivl
| is_protected_Odivlu : is_protected Odivlu
| is_protected_Omodl : is_protected Omodl
| is_protected_Omodlu : is_protected Omodlu

(* Trying to convert NaN (and maybe something else) causes immediate
   UB (see Val.intoffloat in common/Values.v) *)
| is_protected_Ointofsingle : is_protected Ointofsingle
| is_protected_Ointoffloat : is_protected Ointoffloat
| is_protected_Olongofsingle : is_protected Olongofsingle
| is_protected_Olongoffloat : is_protected Olongoffloat

(* Shifting more than the archi word size is immediate UB (see Val.shl
   in common/Values.v) *)
| is_protected_Oshl : is_protected Oshl
| is_protected_Oshr : is_protected Oshr
| is_protected_Oshru : is_protected Oshru
| is_protected_Oshll : is_protected Oshll
| is_protected_Oshrl : is_protected Oshrl
| is_protected_Oshrlu : is_protected Oshrlu

(* Subtracting pointers in different blocks causes immediate UB (see
   [Val.subl] in common/Values.v) *)
| is_protected_Osubl : Archi.ptr64 = true -> is_protected Osubl

(* A faulty selection can cause the faulty execution to take Vundef
   into a register that the normal execution has a defined value for,
   and subsequently encounter UB that the normal execution avoids. See
   [Val.select] in common/Values.v. *)
| is_protected_Osel : forall cond ty, is_protected (Osel cond ty)

(* Comparing pointers in different blocks or comparing a pointer with
   a nonzero integer causes immediate UB. *)
| is_protected_Ocmp_Ccompu : forall c, Archi.ptr64 = false ->
                               is_protected (Ocmp (Ccompu c))
| is_protected_Ocmp_Ccompuimm : forall c n, Archi.ptr64 = false ->
                                    is_protected (Ocmp (Ccompuimm c n))
| is_protected_Ocmp_Ccomplu : forall c, Archi.ptr64 = true ->
                                is_protected (Ocmp (Ccomplu c))
| is_protected_Ocmp_Ccompluimm : forall c n, Archi.ptr64 = true ->
                                     is_protected (Ocmp (Ccompluimm c n))
.

Definition is_protectedb (op : operation) : bool :=
  match op with
  | Odiv | Odivu | Omod | Omodu
  | Odivl | Odivlu | Omodl | Omodlu
  | Ointofsingle | Ointoffloat => true
  | Olongofsingle | Olongoffloat => true
  | Oshl | Oshr | Oshru | Oshll | Oshrl | Oshrlu => true
  | Osubl => Archi.ptr64
  | Osel _ _ => true
  | Ocmp (Ccompu _) | Ocmp (Ccompuimm _ _) => negb Archi.ptr64
  | Ocmp (Ccomplu _) | Ocmp (Ccompluimm _ _) => Archi.ptr64
  | _ => false
  end.

Lemma is_protectedb_spec (op : operation) :
  reflect (is_protected op) (is_protectedb op).
Proof.
  destruct op; try solve [right; intro HC; inv HC];
    try left; try constructor; auto.
  destruct cond; simpl; try solve [right; intro HC; inv HC].
  - destruct Archi.ptr64 eqn:Harchi; simpl.
    + right; intro HC; inv HC; congruence.
    + left; constructor; assumption.
  - destruct Archi.ptr64 eqn:Harchi; simpl.
    + right; intro HC; inv HC; congruence.
    + left; constructor; assumption.
  - destruct Archi.ptr64 eqn:Harchi; simpl.
    + left; constructor; assumption.
    + right; intro HC; inv HC; congruence.
  - destruct Archi.ptr64 eqn:Harchi; simpl.
    + left; constructor; assumption.
    + right; intro HC; inv HC; congruence.
Qed.

Lemma is_protected_subl_archi_ptr64_false :
  ~ is_protected Op.Osubl ->
  Archi.ptr64 = false.
Proof.
  intro H.
  destruct Archi.ptr64 eqn:Harchi; auto.
  exfalso; apply H; constructor; assumption.
Qed.

(** * Builtin classification *)

(** [builtin_can_replicate_bf b] returns [true] if the builtin function [b]
    is safe to replicate by TMR: its semantics are purely numerical or
    otherwise deterministic, and replicating it does not change the program
    behavior.  Protocol builtins (votes, smoves, checks) are never replicable
    because they are introduced by the TMR pass itself. *)

Definition builtin_can_replicate_bf (b: builtin_function) : bool :=
  match b with
  | BI_standard sb =>
    match sb with
    | BI_fabs | BI_fabsf | BI_fsqrt | BI_negl => true
    | BI_addl | BI_mull => true
    | BI_subl => negb Archi.ptr64
    | BI_i16_bswap | BI_i32_bswap | BI_i64_bswap => true
    | BI_i64_umulh | BI_i64_smulh => true
    | BI_i64_shl | BI_i64_shr | BI_i64_sar => false
    | BI_i64_stod | BI_i64_utod | BI_i64_stof | BI_i64_utof => true
    | BI_select _ | BI_unreachable => false
    | BI_i64_sdiv | BI_i64_udiv | BI_i64_smod | BI_i64_umod => false
    | BI_i64_dtos | BI_i64_dtou => false
    end
  | BI_platform pb =>
    match pb with
    | BI_fmin | BI_fmax => true
    end
  | BI_replicate _ => false
  end.

(** [builtin_can_replicate ef] returns [true] if the external function [ef]
    is safe to replicate.  Only [EF_builtin] calls that resolve to a known
    builtin function via [lookup_builtin_function] can be replicable. *)

Definition builtin_can_replicate (ef: external_function) : bool :=
  match ef with
  | EF_builtin name sg =>
    match lookup_builtin_function name sg with
    | Some bf => builtin_can_replicate_bf bf
    | None => false
    end
  | EF_external _ _ | EF_runtime _ _ | EF_vload _
  | EF_vstore _ | EF_malloc | EF_free | EF_memcpy _ _
  | EF_annot _ _ _ | EF_annot_val _ _ _ | EF_inline_asm _ _ _
  | EF_debug _ _ _ => false
  end.

(** [builtin_can_fault ef] classifies builtins whose semantics may be affected
    by a single-register fault.  Currently equal to [builtin_can_replicate],
    defined separately to allow future divergence (e.g., if some replicable
    builtins are proven fault-immune). *)

Definition builtin_can_fault (ef: external_function) : bool :=
  builtin_can_replicate ef.

(** ** Reflection and convenience lemmas *)

Definition builtin_can_replicate_bf_prop (b: builtin_function) : Prop :=
  builtin_can_replicate_bf b = true.

Lemma builtin_can_replicate_bf_spec (b: builtin_function) :
  reflect (builtin_can_replicate_bf_prop b) (builtin_can_replicate_bf b).
Proof.
  unfold builtin_can_replicate_bf_prop.
  destruct (builtin_can_replicate_bf b) eqn:E.
  - left; auto.
  - right; discriminate.
Qed.

Lemma builtin_can_replicate_bf_true (b: builtin_function) :
  builtin_can_replicate_bf b = true ->
  match b with BI_replicate _ => False | _ => True end.
Proof.
  destruct b as [sb|pb|rb]; simpl;
    [ destruct sb | destruct pb | destruct rb ];
    try discriminate; auto.
Qed.

Lemma builtin_can_replicate_bf_false_replicate (b: replicate_builtin) :
  builtin_can_replicate_bf (BI_replicate b) = false.
Proof.
  reflexivity.
Qed.

Lemma builtin_can_replicate_true_bf (ef: external_function)
    (bf: builtin_function) (name: string) (sg: signature) :
  ef = EF_builtin name sg ->
  lookup_builtin_function name sg = Some bf ->
  builtin_can_replicate_bf bf = true ->
  builtin_can_replicate ef = true.
Proof.
  intros; subst; simpl; rewrite H0; auto.
Qed.

Lemma builtin_can_replicate_not_ef_builtin (ef: external_function) :
  (forall name sg, ef <> EF_builtin name sg) ->
  builtin_can_replicate ef = false.
Proof.
  destruct ef; auto; intros; exfalso; eapply H; eauto.
Qed.

(** * Protocol-builtin recognizers *)

Inductive is_green_smove_builtin : external_function -> Prop :=
| is_green_smove_int :
  is_green_smove_builtin (EF_builtin "__builtin_smove_int_green"
                            [Xint ---> Xint]%asttyp)
| is_green_smove_long :
  is_green_smove_builtin (EF_builtin "__builtin_smove_long_green"
                            [Xlong ---> Xlong]%asttyp)
| is_green_smove_single :
  is_green_smove_builtin (EF_builtin "__builtin_smove_single_green"
                            [Xsingle ---> Xsingle]%asttyp)
| is_green_smove_float :
  is_green_smove_builtin (EF_builtin "__builtin_smove_float_green"
                            [Xfloat ---> Xfloat]%asttyp).

Definition is_green_smove_builtinb (ef : external_function) : bool :=
  match ef with
  | EF_builtin name sg =>
      (String.eqb name "__builtin_smove_int_green" &&
         proj_sumbool (signature_eq sg
                         [Xint ---> Xint]%asttyp)) ||
        (String.eqb name "__builtin_smove_long_green" &&
           proj_sumbool (signature_eq sg
                           [Xlong ---> Xlong]%asttyp)) ||
        (String.eqb name "__builtin_smove_single_green" &&
           proj_sumbool (signature_eq sg
                           [Xsingle ---> Xsingle]%asttyp)) ||
        (String.eqb name "__builtin_smove_float_green" &&
           proj_sumbool (signature_eq sg
                           [Xfloat ---> Xfloat]%asttyp))
  | _ => false
  end.

Lemma is_green_smove_builtinb_spec (ef : external_function) :
  reflect (is_green_smove_builtin ef) (is_green_smove_builtinb ef).
Proof.
  destruct ef; try solve [right; intro HC; inv HC].
  simpl.
  destruct (String.eqb name "__builtin_smove_single_green") eqn:H0.
  { rewrite String.eqb_eq in H0; subst.
    destruct (signature_eq sg
                [Xsingle ---> Xsingle]%asttyp); subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H0.
  destruct (String.eqb name "__builtin_smove_int_green") eqn:H1.
  { rewrite String.eqb_eq in H1; subst.
    destruct (signature_eq sg
                [Xint ---> Xint]%asttyp); subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H1.
  destruct (String.eqb name "__builtin_smove_float_green") eqn:H2.
  { rewrite String.eqb_eq in H2; subst.
    destruct (signature_eq sg
                [Xfloat ---> Xfloat]%asttyp) eqn:H2'; subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H2.
  destruct (String.eqb name "__builtin_smove_long_green") eqn:H3.
  { rewrite String.eqb_eq in H3; subst.
    destruct (signature_eq sg
                [Xlong ---> Xlong]%asttyp); subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H3.
  right; intro HC; inv HC; congruence.
Qed.

Inductive is_blue_smove_builtin : external_function -> Prop :=
| is_blue_smove_int :
  is_blue_smove_builtin (EF_builtin "__builtin_smove_int_blue"
                            [Xint ---> Xint]%asttyp)
| is_blue_smove_long :
  is_blue_smove_builtin (EF_builtin "__builtin_smove_long_blue"
                            [Xlong ---> Xlong]%asttyp)
| is_blue_smove_single :
  is_blue_smove_builtin (EF_builtin "__builtin_smove_single_blue"
                            [Xsingle ---> Xsingle]%asttyp)
| is_blue_smove_float :
  is_blue_smove_builtin (EF_builtin "__builtin_smove_float_blue"
                            [Xfloat ---> Xfloat]%asttyp).

Definition is_blue_smove_builtinb (ef : external_function) : bool :=
  match ef with
  | EF_builtin name sg =>
      (String.eqb name "__builtin_smove_int_blue" &&
         proj_sumbool (signature_eq sg
                         [Xint ---> Xint]%asttyp)) ||
        (String.eqb name "__builtin_smove_long_blue" &&
           proj_sumbool (signature_eq sg
                           [Xlong ---> Xlong]%asttyp)) ||
        (String.eqb name "__builtin_smove_single_blue" &&
           proj_sumbool (signature_eq sg
                           [Xsingle ---> Xsingle]%asttyp)) ||
        (String.eqb name "__builtin_smove_float_blue" &&
           proj_sumbool (signature_eq sg
                           [Xfloat ---> Xfloat]%asttyp))
  | _ => false
  end.

Lemma is_blue_smove_builtinb_spec (ef : external_function) :
  reflect (is_blue_smove_builtin ef) (is_blue_smove_builtinb ef).
Proof.
  destruct ef; try solve [right; intro HC; inv HC].
  simpl.
  destruct (String.eqb name "__builtin_smove_single_blue") eqn:H0.
  { rewrite String.eqb_eq in H0; subst.
    destruct (signature_eq sg
                [Xsingle ---> Xsingle]%asttyp); subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H0.
  destruct (String.eqb name "__builtin_smove_int_blue") eqn:H1.
  { rewrite String.eqb_eq in H1; subst.
    destruct (signature_eq sg
                [Xint ---> Xint]%asttyp); subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H1.
  destruct (String.eqb name "__builtin_smove_float_blue") eqn:H2.
  { rewrite String.eqb_eq in H2; subst.
    destruct (signature_eq sg
                [Xfloat ---> Xfloat]%asttyp) eqn:H2'; subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H2.
  destruct (String.eqb name "__builtin_smove_long_blue") eqn:H3.
  { rewrite String.eqb_eq in H3; subst.
    destruct (signature_eq sg
                [Xlong ---> Xlong]%asttyp); subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H3.
  right; intro HC; inv HC; congruence.
Qed.

Inductive is_vote_builtin : external_function -> Prop :=
| is_vote_int :
  is_vote_builtin (EF_builtin "__builtin_vote_int"
                     [Xint; Xint; Xint ---> Xint]%asttyp)
| is_vote_long :
  is_vote_builtin (EF_builtin "__builtin_vote_long"
                     [Xlong; Xlong; Xlong ---> Xlong]%asttyp)
| is_vote_single :
  is_vote_builtin (EF_builtin "__builtin_vote_single"
                     [Xsingle; Xsingle; Xsingle ---> Xsingle]%asttyp)
| is_vote_float :
  is_vote_builtin (EF_builtin "__builtin_vote_float"
                     [Xfloat; Xfloat; Xfloat ---> Xfloat]%asttyp).

Definition is_vote_builtinb (ef : external_function) : bool :=
  match ef with
  | EF_builtin name sg =>
      (String.eqb name "__builtin_vote_int" &&
         proj_sumbool (signature_eq sg
                         [Xint; Xint; Xint ---> Xint]%asttyp)) ||
        (String.eqb name "__builtin_vote_long" &&
           proj_sumbool (signature_eq sg
                           [Xlong; Xlong; Xlong ---> Xlong]%asttyp)) ||
        (String.eqb name "__builtin_vote_single" &&
           proj_sumbool (signature_eq sg
                           [Xsingle; Xsingle; Xsingle ---> Xsingle]%asttyp)) ||
        (String.eqb name "__builtin_vote_float" &&
           proj_sumbool (signature_eq sg
                           [Xfloat; Xfloat; Xfloat ---> Xfloat]%asttyp))
  | _ => false
  end.

Lemma is_vote_builtinb_spec (ef : external_function) :
  reflect (is_vote_builtin ef) (is_vote_builtinb ef).
Proof.
  destruct ef; try solve [right; intro HC; inv HC].
  simpl.
  destruct (String.eqb name "__builtin_vote_single") eqn:H0.
  { rewrite String.eqb_eq in H0; subst.
    destruct (signature_eq sg
                [Xsingle; Xsingle; Xsingle ---> Xsingle]%asttyp); subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H0.
  destruct (String.eqb name "__builtin_vote_int") eqn:H1.
  { rewrite String.eqb_eq in H1; subst.
    destruct (signature_eq sg
                [Xint; Xint; Xint ---> Xint]%asttyp); subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H1.
  destruct (String.eqb name "__builtin_vote_float") eqn:H2.
  { rewrite String.eqb_eq in H2; subst.
    destruct (signature_eq sg
                [Xfloat; Xfloat; Xfloat ---> Xfloat]%asttyp) eqn:H2'; subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H2.
  destruct (String.eqb name "__builtin_vote_long") eqn:H3.
  { rewrite String.eqb_eq in H3; subst.
    destruct (signature_eq sg
                [Xlong; Xlong; Xlong ---> Xlong]%asttyp); subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H3.
  right; intro HC; inv HC; congruence.
Qed.

Lemma vote_not_green_smove (ef : external_function) :
  is_vote_builtin ef -> ~ is_green_smove_builtin ef.
Proof. intro H; inv H; intro HC; inv HC. Qed.

Lemma vote_not_blue_smove (ef : external_function) :
  is_vote_builtin ef -> ~ is_blue_smove_builtin ef.
Proof. intro H; inv H; intro HC; inv HC. Qed.

Inductive is_vote_runtime : external_function -> Prop :=
| is_vote_runtime_int :
  is_vote_runtime (EF_runtime "__builtin_vote_int"
                     [Xint; Xint; Xint ---> Xint]%asttyp)
| is_vote_runtime_long :
  is_vote_runtime (EF_runtime "__builtin_vote_long"
                     [Xlong; Xlong; Xlong ---> Xlong]%asttyp)
| is_vote_runtime_single :
  is_vote_runtime (EF_runtime "__builtin_vote_single"
                     [Xsingle; Xsingle; Xsingle ---> Xsingle]%asttyp)
| is_vote_runtime_float :
  is_vote_runtime (EF_runtime "__builtin_vote_float"
                     [Xfloat; Xfloat; Xfloat ---> Xfloat]%asttyp).

Definition is_vote_runtimeb (ef : external_function) : bool :=
  match ef with
  | EF_runtime name sg =>
      (String.eqb name "__builtin_vote_int" &&
         proj_sumbool (signature_eq sg
                         [Xint; Xint; Xint ---> Xint]%asttyp)) ||
        (String.eqb name "__builtin_vote_long" &&
           proj_sumbool (signature_eq sg
                           [Xlong; Xlong; Xlong ---> Xlong]%asttyp)) ||
        (String.eqb name "__builtin_vote_single" &&
           proj_sumbool (signature_eq sg
                           [Xsingle; Xsingle; Xsingle ---> Xsingle]%asttyp)) ||
        (String.eqb name "__builtin_vote_float" &&
           proj_sumbool (signature_eq sg
                           [Xfloat; Xfloat; Xfloat ---> Xfloat]%asttyp))
  | _ => false
  end.

Lemma is_vote_runtimeb_spec (ef : external_function) :
  reflect (is_vote_runtime ef) (is_vote_runtimeb ef).
Proof.
  destruct ef; try solve [right; intro HC; inv HC].
  simpl.
  destruct (String.eqb name "__builtin_vote_single") eqn:H0.
  { rewrite String.eqb_eq in H0; subst.
    destruct (signature_eq sg
                [Xsingle; Xsingle; Xsingle ---> Xsingle]%asttyp); subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H0.
  destruct (String.eqb name "__builtin_vote_int") eqn:H1.
  { rewrite String.eqb_eq in H1; subst.
    destruct (signature_eq sg
                [Xint; Xint; Xint ---> Xint]%asttyp); subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H1.
  destruct (String.eqb name "__builtin_vote_float") eqn:H2.
  { rewrite String.eqb_eq in H2; subst.
    destruct (signature_eq sg
                [Xfloat; Xfloat; Xfloat ---> Xfloat]%asttyp) eqn:H2'; subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H2.
  destruct (String.eqb name "__builtin_vote_long") eqn:H3.
  { rewrite String.eqb_eq in H3; subst.
    destruct (signature_eq sg
                [Xlong; Xlong; Xlong ---> Xlong]%asttyp); subst.
    - left; constructor.
    - right; intro HC; inv HC; congruence. }
  rewrite eqb_neq in H3.
  right; intro HC; inv HC; congruence.
Qed.
