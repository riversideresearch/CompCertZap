---
phase: 05-comment-tactic-hygiene
plan: 01
subsystem: backend
tags: [coq, proof-hygiene, comments, rtl, fault-tolerance]

# Dependency graph
requires:
  - phase: 04-proof-deduplication
    provides: "Stable proof code in RTLtolerant.v (dedup decisions finalized)"
provides:
  - "Cleaned RTLtolerant.v with 10 dead comment blocks removed (~214 lines)"
  - "TODO markers converted to design notes in both RTLtolerant.v and RTLagreement.v"
affects: [05-02, 05-03]

# Tech tracking
tech-stack:
  added: []
  patterns: ["Design-note comments replace TODO markers for abandoned approaches"]

key-files:
  created: []
  modified:
    - backend/RTLtolerant.v
    - backend/RTLagreement.v

key-decisions:
  - "RTLagreement.v comment blocks retained per user review -- only TODO converted"

patterns-established:
  - "TODO-to-design-note: Convert TODO markers for known-abandoned approaches to design notes explaining why the approach was not pursued"

requirements-completed: [HYG-01, HYG-02]

# Metrics
duration: 4min
completed: 2026-03-04
---

# Phase 05 Plan 01: RTLtolerant/RTLagreement Comment Cleanup Summary

**Removed 10 dead proof blocks (~214 lines) from RTLtolerant.v and converted TODO markers to design notes in both files**

## Performance

- **Duration:** 4 min
- **Started:** 2026-03-04T14:46:28Z
- **Completed:** 2026-03-04T14:50:18Z
- **Tasks:** 2
- **Files modified:** 2

## Accomplishments
- Removed 10 commented-out abandoned proof blocks from RTLtolerant.v (214 lines deleted)
- Converted TODO marker at vote lessdef proof to design note documenting Phase 4 Ltac dedup failure
- Converted TODO marker in RTLagreement.v from task-oriented to design-rationale comment
- Both files compile cleanly with zero regressions

## Task Commits

Each task was committed atomically:

1. **Task 1: Remove 10 commented-out blocks from RTLtolerant.v and convert TODO** - `88e5550e` (chore)
2. **Task 2: Convert TODO marker in RTLagreement.v to design note** - `32b59eeb` (chore)

## Files Created/Modified
- `backend/RTLtolerant.v` - Removed 10 dead comment blocks, converted TODO to design note (214 lines removed)
- `backend/RTLagreement.v` - Converted TODO to design note (comment blocks intentionally retained)

## Decisions Made
- RTLagreement.v comment blocks retained per user review -- only TODO prefix converted to "Design note:" prefix while preserving substance

## Deviations from Plan

None - plan executed exactly as written.

## Issues Encountered
None

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- RTLtolerant.v and RTLagreement.v cleaned, ready for remaining hygiene plans
- Plans 05-02 and 05-03 can proceed on other files

## Self-Check: PASSED

All files exist. All commits verified.

---
*Phase: 05-comment-tactic-hygiene*
*Completed: 2026-03-04*
