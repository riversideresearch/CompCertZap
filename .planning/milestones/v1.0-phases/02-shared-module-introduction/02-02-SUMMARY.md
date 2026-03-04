---
phase: 02-shared-module-introduction
plan: 02
subsystem: backend
tags: [coq, refactoring, deduplication, imports, rtl]

# Dependency graph
requires:
  - phase: 02-shared-module-introduction
    plan: 01
    provides: RTLreplicateProofCommon.v shared import preamble and RTLreplicateSpecCommon.v shared definitions
provides:
  - DMR and TMR proof files wired to import from RTLreplicateProofCommon
  - Full shared module chain (SpecCommon -> ProofCommon -> spec -> proof) verified
affects: [03-spec-strengthening, 04-proof-deduplication]

# Tech tracking
tech-stack:
  added: []
  patterns: [Require Export for transitive import propagation in proof common module]

key-files:
  created: []
  modified:
    - backend/RTLdmrproof.v
    - backend/RTLtmrproof.v
    - backend/RTLreplicateProofCommon.v

key-decisions:
  - "Changed RTLreplicateProofCommon from Require Import to Require Export for transitive import propagation (same pattern as SpecCommon in plan 01)"

patterns-established:
  - "Shared proof common module: use Require Export so consuming proof files get all shared imports transitively"

requirements-completed: [MOD-04]

# Metrics
duration: 2min
completed: 2026-03-04
---

# Phase 02 Plan 02: Proof Common Wiring Summary

**Wired RTLdmrproof.v and RTLtmrproof.v to import shared preamble from RTLreplicateProofCommon, replacing 44 lines of duplicated imports with 2 single-line imports**

## Performance

- **Duration:** 2 min
- **Started:** 2026-03-04T00:07:13Z
- **Completed:** 2026-03-04T00:09:00Z
- **Tasks:** 1
- **Files modified:** 3

## Accomplishments
- Replaced duplicated 22-line import preambles in both RTLdmrproof.v and RTLtmrproof.v with single `Require Import RTLreplicateProofCommon` line
- Fixed RTLreplicateProofCommon to use `Require Export` for transitive import propagation
- Removed stale TODO comment in RTLdmrproof.v ("factor out things in common with TMR")
- Verified full dependent chain (SpecCommon -> ProofCommon -> spec files -> proof files) compiles cleanly
- Confirmed zero admitted proofs via `make check-admitted`

## Task Commits

Each task was committed atomically:

1. **Task 1: Wire proof files to import from RTLreplicateProofCommon** - `b92deb58` (refactor)

## Files Created/Modified
- `backend/RTLdmrproof.v` - DMR proof now imports shared preamble from RTLreplicateProofCommon instead of 22 direct imports
- `backend/RTLtmrproof.v` - TMR proof now imports shared preamble from RTLreplicateProofCommon instead of 22 direct imports
- `backend/RTLreplicateProofCommon.v` - Changed from Require Import to Require Export for transitive propagation

## Decisions Made
- Changed RTLreplicateProofCommon from `Require Import` to `Require Export` for all its imports, and `Import ListNotations` to `Export ListNotations`, and `Local Open Scope` to `Global Open Scope`. This mirrors the pattern established in plan 01 for RTLreplicateSpecCommon and is required for the shared preamble to actually provide transitive imports to consuming files.

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 3 - Blocking] Changed RTLreplicateProofCommon from Require Import to Require Export**
- **Found during:** Task 1 (Wire proof files)
- **Issue:** RTLreplicateProofCommon.v used `Require Import` for all its sub-imports. This means importing ProofCommon does NOT make those names available to the importing file. Both proof files failed to compile with "The reference program was not found in the current environment."
- **Fix:** Changed all `Require Import` to `Require Export`, `Import ListNotations` to `Export ListNotations`, and `Local Open Scope` to `Global Open Scope` in RTLreplicateProofCommon.v
- **Files modified:** backend/RTLreplicateProofCommon.v
- **Verification:** Both proof files compile cleanly, make check-admitted passes
- **Committed in:** b92deb58 (Task 1 commit)

---

**Total deviations:** 1 auto-fixed (1 blocking)
**Impact on plan:** Essential fix for Coq module system -- same pattern already applied to RTLreplicateSpecCommon in plan 01. No scope creep.

## Issues Encountered
None beyond the deviation documented above.

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- Phase 2 (Shared Module Introduction) is now complete
- Full shared module chain verified: RTLreplicateSpecCommon -> RTLreplicateProofCommon -> spec files -> proof files
- Ready for Phase 3 (Spec Strengthening) which can build on the shared spec module
- Ready for Phase 4 (Proof Deduplication) which can build on the shared proof module

## Self-Check: PASSED

All files verified present, all commits verified in git log.

---
*Phase: 02-shared-module-introduction*
*Completed: 2026-03-04*
