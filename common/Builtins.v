(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, Collège de France and Inria Paris            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Known built-in functions *)

From Coq Require Import String.
Require Import Coqlib.
Require Import AST Integers Floats Values.
Require Export Builtins0 Builtins1 Builtins2.

Inductive builtin_function : Type :=
  | BI_standard (b: standard_builtin)
  | BI_platform (b: platform_builtin)
  | BI_replicate (b: replicate_builtin).

Definition eq_builtin_function: forall (x y: builtin_function), {x=y} + {x<>y}.
Proof.
  generalize eq_standard_builtin eq_platform_builtin eq_replicate_builtin; decide equality.
Defined.
Global Opaque eq_builtin_function.

Definition builtin_function_sig (b: builtin_function) : signature :=
  match b with
  | BI_standard b => standard_builtin_sig b
  | BI_platform b => platform_builtin_sig b
  | BI_replicate b => replicate_builtin_sig b
  end.

Definition builtin_function_sem {VT: vote_type} `{HVT: VoteSemantics VT}
  (b: builtin_function) : builtin_sem (sig_res (builtin_function_sig b)) :=
  match b with
  | BI_standard b => standard_builtin_sem b
  | BI_platform b => platform_builtin_sem b
  | BI_replicate b => replicate_builtin_sem b
  end.

Lemma builtin_function_sem_inject {VT: vote_type} `{HVT: VoteSemantics VT}
  : forall b vargs vres f vargs',
  builtin_function_sem b vargs = Some vres ->
  Val.inject_list f vargs vargs' ->
  exists vres', builtin_function_sem b vargs' = Some vres' /\ Val.inject f vres vres'.
Proof.
  intros. exploit (bs_inject _ (builtin_function_sem b)); eauto.
  unfold val_opt_inject; rewrite H; intro J.
  destruct (builtin_function_sem b vargs') as [vres'|]; try contradiction.
  exists vres'; auto.
Qed.

Lemma builtin_function_sem_lessdef {VT: vote_type} `{HVT: VoteSemantics VT}
  : forall b vargs vres vargs',
  builtin_function_sem b vargs = Some vres ->
  Val.lessdef_list vargs vargs' ->
  exists vres', builtin_function_sem b vargs' = Some vres' /\ Val.lessdef vres vres'.
Proof.
  intros. apply val_inject_list_lessdef in H0. 
  exploit builtin_function_sem_inject; eauto.
  intros (vres' & A & B). apply val_inject_lessdef in B.
  exists vres'; auto.
Qed.

Definition lookup_builtin_function (name: string) (sg: signature) : option builtin_function :=
  match lookup_builtin standard_builtin_sig name sg standard_builtin_table with
  | Some b => Some (BI_standard b)
  | None => 
  match lookup_builtin platform_builtin_sig name sg platform_builtin_table with
  | Some b => Some (BI_platform b)
  | None =>
  match lookup_builtin replicate_builtin_sig name sg replicate_builtin_table with
  | Some b => Some (BI_replicate b)
  | None => None
  end end end.

Lemma lookup_builtin_function_sig:
  forall name sg b, lookup_builtin_function name sg = Some b -> builtin_function_sig b = sg.
Proof.
  unfold lookup_builtin_function; intros.
  destruct (lookup_builtin standard_builtin_sig name sg standard_builtin_table) as [bs|] eqn:E.
  inv H. simpl. eapply lookup_builtin_sig; eauto.
  destruct (lookup_builtin platform_builtin_sig name sg platform_builtin_table) as [bp|] eqn:E'.
  inv H. simpl. eapply lookup_builtin_sig; eauto.
  destruct (lookup_builtin replicate_builtin_sig name sg replicate_builtin_table) as [bp|] eqn:E''.
  inv H. simpl. eapply lookup_builtin_sig; eauto.
  discriminate.
Qed.

(** * Builtin classification for TMR replication *)

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

(** Prop form for [builtin_can_replicate_bf]. *)

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

(** A replicable builtin is never a protocol builtin. *)

Lemma builtin_can_replicate_bf_true (b: builtin_function) :
  builtin_can_replicate_bf b = true ->
  match b with BI_replicate _ => False | _ => True end.
Proof.
  destruct b as [sb|pb|rb]; simpl;
    [ destruct sb | destruct pb | destruct rb ];
    try discriminate; auto.
Qed.

(** Protocol builtins are never replicable. *)

Lemma builtin_can_replicate_bf_false_replicate (b: replicate_builtin) :
  builtin_can_replicate_bf (BI_replicate b) = false.
Proof.
  reflexivity.
Qed.

(** Connecting [builtin_can_replicate] to [builtin_can_replicate_bf]
    via [lookup_builtin_function]. *)

Lemma builtin_can_replicate_true_bf (ef: external_function)
    (bf: builtin_function) (name: string) (sg: signature) :
  ef = EF_builtin name sg ->
  lookup_builtin_function name sg = Some bf ->
  builtin_can_replicate_bf bf = true ->
  builtin_can_replicate ef = true.
Proof.
  intros; subst; simpl; rewrite H0; auto.
Qed.

(** Non-[EF_builtin] externals are never replicable. *)

Lemma builtin_can_replicate_not_ef_builtin (ef: external_function) :
  (forall name sg, ef <> EF_builtin name sg) ->
  builtin_can_replicate ef = false.
Proof.
  destruct ef; auto; intros; exfalso; eapply H; eauto.
Qed.

(** * Protocol-builtin recognizers (migrated from RTL.v) *)

(** ** Green smove recognizers *)

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
                [Xfloat ---> Xfloat]%asttyp)eqn:H2; subst.
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

(** ** Blue smove recognizers *)

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
                [Xfloat ---> Xfloat]%asttyp)eqn:H2; subst.
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

(** ** Vote recognizers *)

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
                [Xfloat; Xfloat; Xfloat ---> Xfloat]%asttyp)eqn:H2; subst.
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

(** ** Cross-exclusion lemmas *)

Lemma vote_not_green_smove (ef : external_function) :
  is_vote_builtin ef -> ~ is_green_smove_builtin ef.
Proof. intro H; inv H; intro HC; inv HC. Qed.

Lemma vote_not_blue_smove (ef : external_function) :
  is_vote_builtin ef -> ~ is_blue_smove_builtin ef.
Proof. intro H; inv H; intro HC; inv HC. Qed.

(** ** Vote runtime recognizers *)

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
                [Xfloat; Xfloat; Xfloat ---> Xfloat]%asttyp)eqn:H2; subst.
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
