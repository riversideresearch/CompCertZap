---
phase: 04-proof-deduplication
plan: 03
subsystem: backend
tags: [coq, proof-decomposition, colorcheck, per-instruction-lemmas]

# Dependency graph
requires:
  - phase: 04-proof-deduplication (plans 01, 02)
    provides: Prior de-duplication of RTLtolerant.v, RTLtmrproof.v, Novotesproof.v
provides:
  - Per-instruction soundness lemmas in RTLcolorcheck.v
  - Full proof suite verification for all Phase 4 work
affects: [05-comment-and-tactic-hygiene]

# Tech tracking
tech-stack:
  added: []
  patterns: [per-instruction-lemma decomposition with dispatcher]

key-files:
  created: []
  modified: [backend/RTLcolorcheck.v]

key-decisions:
  - "Used explicit preconditions (is_protected, is_green_smove_builtin, etc.) on per-instruction builtin lemmas rather than relying on simpl reduction"
  - "Added mutual exclusion preconditions to vote lemma (~ is_green_smove_builtin, ~ is_blue_smove_builtin) to match the nested if-then-else structure in check_col_instr"
  - "Blue smove lemma handles green smove false case via exfalso+inversion rather than relying on simpl alone"

patterns-established:
  - "Per-instruction lemma pattern: each instruction case gets its own named lemma with explicit type signature, main lemma is a short dispatcher"

requirements-completed: [DEDUP-05]

# Metrics
duration: 4min
completed: 2026-03-04
---

# Phase 4 Plan 03: RTLcolorcheck Per-Instruction Decomposition Summary

**Decomposed check_col_instr_sound into 14 self-contained per-instruction soundness lemmas with a 20-line dispatcher**

## Performance

- **Duration:** 4 min
- **Started:** 2026-03-04T05:18:42Z
- **Completed:** 2026-03-04T05:22:34Z
- **Tasks:** 2
- **Files modified:** 1

## Accomplishments
- Extracted 14 per-instruction lemmas from the monolithic 200-line check_col_instr_sound proof
- Each instruction case (Inop, Iop protected/safe, Iload, Istore, Icall, Itailcall, Ibuiltin green/blue/vote/other, Icond, Ijumptable, Ireturn) is now independently stated and proved
- Main check_col_instr_sound is now a 20-line dispatcher that delegates to per-instruction lemmas
- Full proof suite (`make proof -j$(nproc)`) and `make check-admitted` both pass with zero regressions

## Task Commits

Each task was committed atomically:

1. **Task 1: Extract per-instruction lemmas from check_col_instr_sound** - `cacc8821` (refactor)
2. **Task 2: Full proof suite verification** - No commit (verification-only task, no file changes)

## Files Created/Modified
- `backend/RTLcolorcheck.v` - Decomposed check_col_instr_sound into 14 per-instruction lemmas + dispatcher

## Decisions Made
- Used explicit preconditions on builtin lemmas rather than relying on simpl reduction -- this makes each lemma's contract clear and self-documenting
- The vote builtin lemma takes negative preconditions for green_smove and blue_smove to match the nested conditional structure in check_col_instr
- Blue smove lemma proves the green_smove false case via exfalso+inversion on the mutually exclusive builtin name predicates

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Fixed variable name mismatch in builtin lemmas**
- **Found during:** Task 1
- **Issue:** Plan's proof templates used variable name `b0` from the original destruct-instr context, but per-instruction lemmas with explicit parameters generate different auto-names (`b` for head of builtin_arg list)
- **Fix:** Changed `b0` to `b` in green/blue smove lemmas, and `b` to `res` in other_builtin lemma where it referred to builtin_res
- **Files modified:** backend/RTLcolorcheck.v
- **Verification:** `make backend/RTLcolorcheck.vo` succeeded
- **Committed in:** cacc8821

---

**Total deviations:** 1 auto-fixed (1 bug fix)
**Impact on plan:** Trivial variable name adjustment required by Coq's auto-naming. No scope creep.

## Issues Encountered
None beyond the variable name fix documented above.

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- Phase 4 is complete: all three plans (04-01, 04-02, 04-03) have executed
- All proof files compile cleanly, zero admitted proofs
- Ready for Phase 5 (Comment and Tactic Hygiene)

## Self-Check: PASSED

- FOUND: backend/RTLcolorcheck.v
- FOUND: commit cacc8821
- FOUND: 04-03-SUMMARY.md

---
*Phase: 04-proof-deduplication*
*Completed: 2026-03-04*
