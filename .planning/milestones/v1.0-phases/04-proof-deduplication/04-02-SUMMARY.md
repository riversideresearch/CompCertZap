---
phase: 04-proof-deduplication
plan: 02
subsystem: backend
tags: [coq, ltac, proof-deduplication, rtl, tmr]

requires:
  - phase: 03-spec-strengthening
    provides: "TMR relational specs in RTLtmrproof.v"
provides:
  - "Deduplicated maj_voteR_step proof in RTLtmrproof.v"
affects: []

tech-stack:
  added: []
  patterns:
    - "first [...] dispatch for type-parametric vote proofs"

key-files:
  created: []
  modified:
    - backend/RTLtmrproof.v

key-decisions:
  - "Abandoned Novotesproof.v deduplication — tactic caused infinite memory consumption during proof checking"
  - "RTLtmrproof.v deduplication used inline semicolon chaining rather than separate Ltac tactic, avoiding hypothesis name issues"

patterns-established:
  - "try solve [...] chains for type-specific equality deciders (Int.eq_dec, Float.eq_dec, etc.)"

requirements-completed: [DEDUP-02]

duration: 15min
completed: 2026-03-04
status: partial
---

# Plan 04-02: Novotesproof/RTLtmrproof Deduplication Summary

**Collapsed maj_voteR_step from 80 to 40 lines via first/try-solve dispatch; abandoned Novotesproof.v dedup due to infinite memory**

## Performance

- **Duration:** ~15 min
- **Tasks:** 1/2 completed (Task 1 abandoned)
- **Files modified:** 1

## Accomplishments
- Collapsed four near-identical type branches in `maj_voteR_step` into single unified proof
- Used `first [apply vote_sem_int_ok | ... | apply vote_sem_single_ok]` for type dispatch
- Used `try solve` chains for register equality cases covering all type-specific deciders
- Removed TODO comment about duplication

## Task Commits

1. **Task 1: Collapse no_votes_external_call in Novotesproof.v** - ABANDONED (infinite memory)
2. **Task 2: Collapse maj_voteR_step in RTLtmrproof.v** - `a5e935af` (refactor)

## Why Task 1 Was Abandoned

The `no_votes_external_call` proof in Novotesproof.v has 8 repeated blocks walking the builtin lookup table. The tactic-based replacement compiled but caused Coq to consume seemingly infinite memory during proof checking — likely the `repeat` tactic over `destruct (string_dec _ _ && signature_eq _ _)` creates an exponential search space. The original explicit `do N` counting is ugly but efficient.

## Files Modified
- `backend/RTLtmrproof.v` - Collapsed maj_voteR_step four-case proof

## Deviations from Plan
Task 1 (Novotesproof.v) abandoned due to memory explosion. Used inline semicolon chaining instead of separate Ltac tactic for Task 2.

## Issues Encountered
- Novotesproof.v tactic caused infinite memory consumption in Coq proof checker

## Next Phase Readiness
- RTLtmrproof.v deduplication complete, does not block 04-03

---
*Phase: 04-proof-deduplication*
*Completed: 2026-03-04*
