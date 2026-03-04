# CompCert Proof Cleanup and Reorganization

## What This Is

A systematic cleanup of CompCert's fault-tolerance proof codebase. v1.0 delivered dead code removal, shared module extraction, relational spec decomposition, proof de-duplication, and comment/TODO hygiene across the DMR/TMR proof infrastructure.

## Core Value

All Coq proofs continue to compile cleanly after every change — no regressions, no new Admitted proofs.

## Requirements

### Validated

- ✓ CompCert compiles C to x86-64 assembly — existing
- ✓ TMR/DMR replication passes produce correct RTL — existing
- ✓ Fault tolerance backward simulation proof composes four refinements — existing
- ✓ Color checker verifies well-coloredness of replicated programs — existing
- ✓ Delete untracked backup files and dead experimental stubs — v1.0
- ✓ Centralize shared DMR/TMR proof lemmas into common modules — v1.0
- ✓ Strengthen replication-map specifications with relational specs — v1.0
- ✓ Remove large commented-out abandoned proof blocks from active files — v1.0
- ✓ Resolve all TODO markers in in-scope files — v1.0
- ✓ Decompose check_col_instr_sound into per-instruction lemmas — v1.0
- ✓ Remove deprecated external_call_Three_Two — v1.0

### Active

- [ ] Unify no_votes handling across cross-pass assumptions (XPASS-01)
- [ ] Resolve CSEproof.v TODO — decide if Novotes hypothesis needed (XPASS-02)
- [ ] Split RTLtolerant.v into focused modules (STRUCT-01)

### Out of Scope

- New features or compiler passes — this is cleanup only
- Changing theorem statements unless required for cleanup — keep signatures stable
- Optimizing build times — focus is on code quality
- Touching files outside the fault-tolerance extension unless necessary
- De-duplicating no_votes_external_call (DEDUP-01) — blocked by Coq tactic memory explosion
- De-duplicating external_call_vote_lessdef (DEDUP-03) — blocked by Ltac hypothesis instability

## Context

Shipped v1.0 with 13 source files changed, net -167 lines (926 added, 1093 deleted).
Tech stack: Coq proofs + OCaml extraction, OCaml 4.14.2.
Two new shared modules (RTLreplicateSpecCommon.v, RTLreplicateProofCommon.v) centralize DMR/TMR shared machinery.
Relational specs replace monolithic proofs in both DMR and TMR spec files.
Three de-duplication attempts abandoned due to Coq proof automation limitations — documented as tech debt.

## Constraints

- **Build integrity**: Every commit must leave the proof buildable — no broken intermediate states
- **Theorem stability**: Prefer keeping theorem signatures stable; when changing, migrate all call sites in the same commit
- **Coq version**: Must remain compatible with current Coq/OCaml toolchain (OCaml 4.14.2)

## Key Decisions

| Decision | Rationale | Outcome |
|----------|-----------|---------|
| Follow dependency-aware execution order (1→2→3→4→5) | Spec strengthening enables proof de-duplication | ✓ Good |
| Separate commits by type (move-only, extraction, statement changes) | Prevents accidental proof obligation changes | ✓ Good |
| Verify via rg + build before any file deletion | Prevents removing externally referenced code | ✓ Good |
| no_votes policy alignment deferred to v2 | Requires cross-pass architecture decision | — Pending |
| Used Require Export for shared modules | Downstream files get unqualified access to shared names | ✓ Good |
| Abandoned DEDUP-01 (Novotesproof.v) | Coq tactic memory explosion — automation impractical | ⚠️ Revisit |
| Abandoned DEDUP-03 (RTLtolerant.v) | Ltac hypothesis name instability across inversions | ⚠️ Revisit |
| DEDUP-02 inline consolidation without named lemma | Type-dispatch structure prevents clean parametric extraction | ✓ Good |
| Decomposed check_col_instr_sound into 14 lemmas | Per-instruction lemmas with 20-line dispatcher | ✓ Good |
| Retained comment blocks in RTLtmr.v, Complements.v per user review | Design notes serve as architectural documentation | ✓ Good |

---
*Last updated: 2026-03-04 after v1.0 milestone*
