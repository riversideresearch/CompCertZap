---
phase: 04-proof-deduplication
plan: 01
subsystem: backend
tags: [coq, ltac, proof-deduplication, rtl]

requires:
  - phase: 03-tmr-proof-decomposition
    provides: "Decomposed TMR proofs in RTLtolerant.v"
provides:
  - "Deprecated external_call_Three_Two removed, call sites migrated to primed version"
affects: []

tech-stack:
  added: []
  patterns: []

key-files:
  created: []
  modified:
    - backend/RTLtolerant.v

key-decisions:
  - "Abandoned Task 2 (external_call_vote_lessdef deduplication) — Ltac automation could not robustly handle hypothesis name instability across inversion chains"
  - "Kept Task 1 (deprecated lemma removal) as standalone cleanup"

patterns-established: []

requirements-completed: [DEDUP-04]

duration: 30min
completed: 2026-03-03
status: partial
---

# Plan 04-01: RTLtolerant.v Cleanup Summary

**Migrated 3 call sites from deprecated external_call_Three_Two to primed version and removed deprecated lemma; abandoned vote_lessdef deduplication due to Ltac fragility**

## Performance

- **Duration:** ~30 min
- **Tasks:** 1/2 completed (Task 2 abandoned)
- **Files modified:** 1

## Accomplishments
- Migrated all 3 call sites of `external_call_Three_Two` to `external_call_Three_Two'`
- Deleted deprecated `external_call_Three_Two` lemma and commented-out version
- Removed associated TODO comment
- File compiles cleanly with no `Admitted` proofs

## Task Commits

1. **Task 1: Migrate call sites + remove deprecated lemma** - `ef156da2` (refactor)
2. **Task 2: Collapse vote_lessdef four-case duplication** - ABANDONED, reverted via `2e16f1f7`

## Why Task 2 Was Abandoned

The goal was to collapse four identical type cases (Tint/Tlong/Tsingle/Tfloat) in `external_call_vote_lessdef` into a single Ltac tactic. This proved intractable because:

1. **Hypothesis name instability:** The four branches produce different hypothesis names after `inv Hbuiltin`. Coq's `inv` tactic generates names like H, H0, H1, H2, etc. based on context, and these shift between branches. A tactic that works for Tint breaks on Tlong because H1 in one branch corresponds to H2 in another.

2. **Deep nested inversions:** The proof requires ~4 levels of nested inversion on `list_lessdef_mod_1` / `Forall2 Val.lessdef`, each producing different hypothesis names. Writing match-based tactics that pattern-match on hypothesis types (instead of names) partially works but breaks when multiple hypotheses have the same type.

3. **Constructor erasure after simpl:** After `constructor; simpl; auto`, evars introduced by `eexists` need reduction that `auto` alone can't resolve — requiring `constructor; simpl; auto` instead of `constructor; auto`. But the exact reduction behavior varies by type case.

4. **Cost vs. benefit:** The duplication is ~130 lines of mechanical proof script. It's ugly but correct, stable, and never needs to change. The automation attempts all introduced fragility (risking future Coq version breakage) for marginal readability gain.

The original proof with four explicit cases was restored and compiles cleanly.

## Files Modified
- `backend/RTLtolerant.v` - Removed deprecated lemma, migrated call sites (kept); vote_lessdef unchanged

## Deviations from Plan
Task 2 abandoned after multiple failed Ltac approaches. Reverted to original four-case proof.

## Issues Encountered
- Ltac hypothesis name instability made robust tactic automation impractical for this particular proof pattern

## Next Phase Readiness
- RTLtolerant.v is in a clean state (no Admitted, no deprecated lemmas)
- Does not block 04-02 or 04-03

---
*Phase: 04-proof-deduplication*
*Completed: 2026-03-03*
