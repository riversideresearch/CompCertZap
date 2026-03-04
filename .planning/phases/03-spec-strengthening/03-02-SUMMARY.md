---
phase: 03-spec-strengthening
plan: 02
subsystem: backend
tags: [coq, tmr, relational-spec, proof-decomposition, replication-map]

# Dependency graph
requires:
  - phase: 02-shared-module-introduction
    provides: RTLreplicateSpecCommon shared module with elements_NoDup pattern
provides:
  - Relational spec (replication_map_rel) for TMR replication map construction
  - Decomposed proof of replication_map_wf via foldM_satisfies_rel + rel_implies_rm_wf
  - Helper lemmas for TMR shadow pair properties (consecutive, disjoint, injective)
affects: [04-proof-deduplication]

# Tech tracking
tech-stack:
  added: []
  patterns: [relational-spec-decomposition, range-separation-proof, shadow-disjointness]

key-files:
  created: []
  modified: [backend/RTLtmrspec.v]

key-decisions:
  - "Added replication_map_rel_consecutive lemma (r3 = Pos.succ r2) needed for NoDup6 cross-register proofs, beyond what DMR required"
  - "Proved replication_map_rel_disjoint_shadows directly via induction on the relational spec, providing non-overlapping shadow intervals"
  - "Used range separation + consecutive + disjoint lemmas for NoDup6 proofs instead of generic NoDup6 helper, which was unsound with only pair inequality"

patterns-established:
  - "TMR relational spec pattern: Inductive with rmr_nil/rmr_cons, pair allocation (mid, Pos.succ mid), advancing by 2 per register"
  - "TMR shadow disjointness: proved separately from NoDup construction, used as key structural lemma in rel_implies_rm_wf"

requirements-completed: [SPEC-02, SPEC-04]

# Metrics
duration: 7min
completed: 2026-03-04
---

# Phase 3 Plan 02: TMR Replication Map Spec Decomposition Summary

**Relational spec (replication_map_rel) for TMR replication map replacing ~128-line monolithic proof with 8 focused lemmas and 3-line composition proof**

## Performance

- **Duration:** 7 min
- **Started:** 2026-03-04T00:50:04Z
- **Completed:** 2026-03-04T00:57:37Z
- **Tasks:** 2
- **Files modified:** 1

## Accomplishments
- Defined `replication_map_rel` inductive capturing per-step TMR register allocation with two shadows per original (mid, Pos.succ mid)
- Replaced monolithic `replication_map_wf_aux` (~128 lines) with decomposed proofs: `foldM_satisfies_rel` and `rel_implies_rm_wf`
- Re-proved `replication_map_wf` via 3-line composition, same type signature
- RTLtmrproof.v compiles unchanged against new interface

## Task Commits

Each task was committed atomically:

1. **Task 1: Define replication_map_rel inductive and helper lemmas** - `1adced11` (feat)
2. **Task 2: Replace replication_map_wf_aux with decomposed proofs** - `26748e39` (feat)

## Files Created/Modified
- `backend/RTLtmrspec.v` - TMR relational spec with decomposed replication_map_wf proof

## Decisions Made
- Added `replication_map_rel_consecutive` lemma proving `r3 = Pos.succ r2` for each shadow pair. This was needed beyond the DMR pattern because TMR's NoDup6 cross-register proof requires showing all 15 pairwise distinctness conditions. The DMR only needs NoDup4 which works with simple range separation, but TMR needs to know shadow pairs don't overlap (not just that they're unequal as pairs).
- Proved `replication_map_rel_disjoint_shadows` as a separate structural lemma showing that distinct registers' shadow intervals `[r2, r3]` and `[r2', r3']` don't overlap. Combined with `consecutive`, this provides the full range separation needed for NoDup6.
- Added `elements_NoDup` locally (same as in RTLdmrspec.v) rather than moving to common module, keeping changes minimal and isolated.

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Fixed NoDup6 proof strategy for TMR cross-register distinctness**
- **Found during:** Task 2 (rel_implies_rm_wf proof)
- **Issue:** Plan's suggested approach using `replication_map_rel_injective` (pair inequality) was insufficient for NoDup6. Pair inequality `(r2, r3) <> (r2', r3')` only gives `r2 <> r2' \/ r3 <> r3'`, not all 4 cross-shadow distinctness conditions needed. Example: `r2 = 5, r3 = 6, r2' = 6, r3' = 7` satisfies pair inequality but `r3 = r2'`.
- **Fix:** Added `replication_map_rel_consecutive` (r3 = Pos.succ r2) and `replication_map_rel_disjoint_shadows` (non-overlapping intervals) lemmas. Combined these to get full range separation: `r3 < r2' \/ r3' < r2`, which with consecutive gives all pairwise distinctness.
- **Files modified:** backend/RTLtmrspec.v
- **Verification:** `make backend/RTLtmrspec.vo backend/RTLtmrproof.vo` passes
- **Committed in:** 26748e39 (Task 2 commit)

---

**Total deviations:** 1 auto-fixed (1 bug in proof strategy)
**Impact on plan:** Proof strategy strengthened to be correct. No scope creep -- additional lemmas are structurally necessary for TMR's 6-element NoDup proofs.

## Issues Encountered
None beyond the deviation noted above.

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- Both DMR (03-01) and TMR (03-02) relational specs are complete
- Phase 3 (spec strengthening) is fully done
- Ready to proceed to Phase 4 (proof de-duplication) which can reference cleaner relational specs
- Note: Phase 4 pre-condition about `no_votes` policy (Option A vs B) still needs decision before Phase 4 begins

## Self-Check: PASSED

- backend/RTLtmrspec.v: FOUND
- 03-02-SUMMARY.md: FOUND
- Commit 1adced11: FOUND
- Commit 26748e39: FOUND
- replication_map_rel inductive: FOUND
- foldM_satisfies_rel: FOUND
- rel_implies_rm_wf: FOUND
- replication_map_wf_aux absent: CONFIRMED (count=0)

---
*Phase: 03-spec-strengthening*
*Completed: 2026-03-04*
