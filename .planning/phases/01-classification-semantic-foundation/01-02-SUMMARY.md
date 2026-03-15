---
phase: 01-classification-semantic-foundation
plan: 02
subsystem: builtins
tags: [coq, protocol-recognizers, builtins, migration, smove, vote]

# Dependency graph
requires:
  - phase: 01-classification-semantic-foundation/01
    provides: builtin_can_replicate, builtin_can_fault classification predicates in common/Builtins.v
provides:
  - Protocol-builtin recognizers (is_green_smove_builtin, is_blue_smove_builtin, is_vote_builtin) consolidated in common/Builtins.v
  - Vote runtime recognizers (is_vote_runtime) in common/Builtins.v
  - Cross-exclusion lemmas (vote_not_green_smove, vote_not_blue_smove) in common/Builtins.v
  - Single import point for all builtin classification and protocol recognition
affects: [01-classification-semantic-foundation/03, 02-subsystem-updates]

# Tech tracking
tech-stack:
  added: []
  patterns: [protocol-recognizer consolidation into common/Builtins.v]

key-files:
  created: []
  modified:
    - common/Builtins.v
    - backend/RTL.v
    - backend/RTLcolor.v
    - backend/RTLcolorcheck.v
    - backend/Novotes.v
    - backend/Novotesproof.v
    - backend/RTLtolerant.v
    - backend/RTLagreement.v

key-decisions:
  - "Added explicit Require Import Builtins to 6 downstream consumers rather than changing RTL.v from Import to Export -- more targeted, avoids broadening RTL's re-export surface"

patterns-established:
  - "Protocol recognizer import: downstream files that need is_*_builtin must import Builtins directly (not rely on transitive re-export through RTL)"

requirements-completed: [CLAS-05]

# Metrics
duration: 5min
completed: 2026-03-15
---

# Phase 1 Plan 2: Protocol-Builtin Recognizer Migration Summary

**Migrated is_green_smove_builtin, is_blue_smove_builtin, is_vote_builtin, is_vote_runtime recognizers from backend/RTL.v to common/Builtins.v with 6 downstream import fixups**

## Performance

- **Duration:** 5 min
- **Started:** 2026-03-15T01:24:56Z
- **Completed:** 2026-03-15T01:30:09Z
- **Tasks:** 2
- **Files modified:** 8

## Accomplishments
- All protocol-builtin recognizers (green smove, blue smove, vote, vote runtime) consolidated into common/Builtins.v as single import point
- backend/RTL.v slimmed by ~280 lines of protocol recognizer definitions
- All 6 downstream Coq consumer files verified to build cleanly with new import chain
- Cross-exclusion lemmas (vote_not_green_smove, vote_not_blue_smove) preserved in new location

## Task Commits

Each task was committed atomically:

1. **Task 1: Move protocol recognizers to common/Builtins.v** - `1754851e` (feat)
2. **Task 2: Verify downstream consumers build** - `a0a487d3` (fix)

## Files Created/Modified
- `common/Builtins.v` - Added protocol-builtin recognizer inductives, Boolean variants, reflection lemmas, cross-exclusion lemmas, and vote runtime recognizers
- `backend/RTL.v` - Removed all protocol-builtin recognizer definitions (lines 1063-1341)
- `backend/RTLcolor.v` - Added `Require Import Builtins`
- `backend/RTLcolorcheck.v` - Added `Require Import Builtins`
- `backend/Novotes.v` - Added `Require Import Builtins`
- `backend/Novotesproof.v` - Added `Require Import Builtins`
- `backend/RTLtolerant.v` - Added `Require Import Builtins`
- `backend/RTLagreement.v` - Added `Require Import Builtins`

## Decisions Made
- Added explicit `Require Import Builtins` to 6 downstream consumers rather than changing RTL.v's `Require Import Builtins` to `Require Export Builtins`. Rationale: more targeted approach that avoids broadening RTL's re-export surface and making all of Builtins visible to every RTL consumer.

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 3 - Blocking] Added Builtins import to 6 downstream consumer files**
- **Found during:** Task 2 (downstream consumer build verification)
- **Issue:** `Require Import RTL` does not transitively re-export Builtins definitions; downstream files got "is_green_smove_builtin was not found" errors
- **Fix:** Added `Require Import Builtins` to import blocks of RTLcolor.v, RTLcolorcheck.v, Novotes.v, Novotesproof.v, RTLtolerant.v, RTLagreement.v
- **Files modified:** 6 backend .v files
- **Verification:** All 6 .vo files build successfully
- **Committed in:** a0a487d3 (Task 2 commit)

---

**Total deviations:** 1 auto-fixed (1 blocking)
**Impact on plan:** Auto-fix was anticipated by the plan as a possible outcome. No scope creep.

## Issues Encountered
None beyond the expected import chain adjustment documented above.

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- All builtin classification and protocol recognition now consolidated in common/Builtins.v
- Ready for Plan 03 (builtin_sem_val_compat proof) which depends on having all classification in one place
- Phase 2 subsystem updates will benefit from single import point for both safe-classification and protocol-recognition

## Self-Check: PASSED

All files verified present, all commits verified in git log.

---
*Phase: 01-classification-semantic-foundation*
*Completed: 2026-03-15*
