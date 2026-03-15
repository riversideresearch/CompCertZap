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
    | BI_i64_shl | BI_i64_shr | BI_i64_sar => true
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
