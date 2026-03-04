---
phase: 05-comment-tactic-hygiene
plan: 03
subsystem: backend
tags: [coq, hygiene, comments, naming, rtl]

# Dependency graph
requires:
  - phase: 05-comment-tactic-hygiene (plans 01-02)
    provides: RTLagreement.v/RTLtmr.v/Complements.v comment review decisions
provides:
  - Cleaned RTLfault.v with dead idfg block removed
  - All in-scope TODOs resolved to design notes
  - maj_vote_regsR_star_step naming aligned with RTLtmrspec.v
affects: []

# Tech tracking
tech-stack:
  added: []
  patterns: [TODO-to-design-note conversion, lemma naming aligned with spec]

key-files:
  created: []
  modified:
    - backend/RTLfault.v
    - backend/RTL.v
    - backend/Novotesproof.v
    - backend/RTLtmrproof.v

key-decisions:
  - "RTLcolorcheck.v, Novotes.v, RTLinfercolor.ml, RTLtmr.v comment blocks intentionally retained per user review -- no changes"
  - "RTLfault.v design note (fault/builtin policy) preserved; only dead idfg lemma removed"
  - "Novotesproof.v TODO converted to design note documenting Phase 4 Ltac memory issue"

patterns-established:
  - "TODO markers converted to 'Design note:' or 'Note:' prefixes when issue is documented but not actionable"

requirements-completed: [HYG-05, HYG-06, HYG-07, HYG-08, HYG-09]

# Metrics
duration: 3min
completed: 2026-03-04
---

# Phase 05 Plan 03: RTLfault cleanup, TODO resolution, and naming alignment Summary

**Dead idfg block removed from RTLfault.v, 3 TODO markers converted to design notes, maj_vote_regR_star_step renamed to maj_vote_regsR_star_step across 9 sites in RTLtmrproof.v -- full proof suite green**

## Performance

- **Duration:** 3 min
- **Started:** 2026-03-04T14:55:28Z
- **Completed:** 2026-03-04T14:58:36Z
- **Tasks:** 2
- **Files modified:** 4

## Accomplishments
- Removed dead commented-out idfg lemma block from RTLfault.v (HYG-07)
- Converted 3 in-scope TODO markers to design notes in RTL.v and Novotesproof.v (HYG-08)
- Renamed maj_vote_regR_star_step to maj_vote_regsR_star_step in RTLtmrproof.v (HYG-09, 9 occurrences)
- Verified RTLcolorcheck.v and Novotes.v comment blocks intentionally retained (HYG-05, HYG-06)
- Full `make proof -j$(nproc)` passes, `make check-admitted` returns "Nothing admitted."

## Task Commits

Each task was committed atomically:

1. **Task 1: Remove commented-out block from RTLfault.v; verify RTLcolorcheck.v and Novotes.v** - `0f61c2f8` (chore)
2. **Task 2: Resolve remaining TODOs and rename maj_vote_regR_star_step** - `5e9443ce` (chore)

**Plan metadata:** (pending) (docs: complete plan)

## Files Created/Modified
- `backend/RTLfault.v` - Removed dead idfg lemma block (8 lines); design note preserved
- `backend/RTL.v` - Converted 2 TODO markers to design notes (comment-only change)
- `backend/Novotesproof.v` - Converted TODO to design note explaining intentional repetition
- `backend/RTLtmrproof.v` - Renamed maj_vote_regR_star_step to maj_vote_regsR_star_step (9 occurrences)

## Decisions Made
- RTLcolorcheck.v, Novotes.v, RTLinfercolor.ml, and RTLtmr.v comment blocks intentionally retained per user review from plans 01-02 -- no modifications
- RTLfault.v design note at lines 50-51 preserved (fault/builtin policy rationale) while dead idfg lemma removed
- Novotesproof.v TODO converted to note documenting Phase 4 Ltac memory issue (explains why 8-case repetition is intentional)

## Deviations from Plan

None - plan executed exactly as written.

## Issues Encountered
None

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- Phase 5 (Comment and Tactic Hygiene) is now fully complete (all 3 plans executed)
- All 5 phases of the cleanup milestone are complete
- Full proof suite passes with zero regressions and zero Admitted proofs

## Self-Check: PASSED

- All 4 modified files exist on disk
- Commit 0f61c2f8 (Task 1) verified
- Commit 5e9443ce (Task 2) verified

---
*Phase: 05-comment-tactic-hygiene*
*Completed: 2026-03-04*
