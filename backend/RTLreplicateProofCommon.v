(** * Shared imports and utilities for DMR/TMR replication proofs. *)

Require Export AST Coqlib Errors Events Floats Globalenvs Integers Linking Maps Op Registers RTLgen RTLtyping Smallstep Values.
Require Export RTL.
Require Export Errors.
Require Export RTLreplicateSpecCommon.
Export ListNotations.

Global Open Scope positive_scope.

(** Section-internal proof lemmas remain in the pass-specific files
    (RTLdmrproof.v and RTLtmrproof.v) per the move-only constraint.
    This module provides only the shared import preamble. *)
