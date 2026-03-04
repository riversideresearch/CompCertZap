(** * Shared imports and utilities for DMR/TMR replication proofs. *)

Require Import AST Coqlib Errors Events Floats Globalenvs Integers Linking Maps Op Registers RTLgen RTLtyping Smallstep Values.
Require Import RTL.
Require Import Errors.
Require Import RTLreplicateSpecCommon.
Import ListNotations.

Local Open Scope positive_scope.

(** Section-internal proof lemmas remain in the pass-specific files
    (RTLdmrproof.v and RTLtmrproof.v) per the move-only constraint.
    This module provides only the shared import preamble. *)
