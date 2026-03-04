---
phase: 02-shared-module-introduction
plan: 01
subsystem: backend
tags: [coq, refactoring, deduplication, ltac, rtl]

# Dependency graph
requires:
  - phase: 01-baseline-and-file-cleanup
    provides: Clean baseline with no dead files or false-positive Admitted strings
provides:
  - RTLreplicateSpecCommon.v with 7 shared Ltac tactics, type definitions, builtin_res utilities, and reg_used definitions
  - RTLreplicateProofCommon.v with shared import preamble for proof files
  - DMR/TMR spec files wired to import shared content instead of duplicating
affects: [02-shared-module-introduction, 03-spec-strengthening, 04-proof-deduplication]

# Tech tracking
tech-stack:
  added: []
  patterns: [shared-common-module extraction, Require Export for transitive re-export]

key-files:
  created:
    - backend/RTLreplicateSpecCommon.v
    - backend/RTLreplicateProofCommon.v
  modified:
    - backend/RTLdmrspec.v
    - backend/RTLtmrspec.v
    - Makefile

key-decisions:
  - "Used Require Export (not Import) for RTLreplicateSpecCommon in spec files so downstream proof files get unqualified access to shared names"

patterns-established:
  - "Shared module extraction: extract byte-identical definitions into *Common.v, use Require Export in consuming files"

requirements-completed: [MOD-01, MOD-02, MOD-03]

# Metrics
duration: 4min
completed: 2026-03-04
---

# Phase 02 Plan 01: Shared Module Creation Summary

**Extracted 7 Ltac tactics, 4 type/utility definitions, and 3 reg_used definitions into RTLreplicateSpecCommon.v, eliminating 238 lines of duplication between DMR/TMR spec files**

## Performance

- **Duration:** 4 min
- **Started:** 2026-03-04T00:00:26Z
- **Completed:** 2026-03-04T00:04:43Z
- **Tasks:** 2
- **Files modified:** 5

## Accomplishments
- Created RTLreplicateSpecCommon.v with all shared definitions (7 Ltac tactics, comp_of_typ, is_actual_type, is_BR, is_BR_dec, reg_used_in_instr, reg_used_in_code, reg_used)
- Created RTLreplicateProofCommon.v with shared import preamble for future proof deduplication
- Wired both RTLdmrspec.v and RTLtmrspec.v to import from the shared module, removing 238 lines of duplication
- Verified all four files (spec + proof) compile cleanly with no regressions

## Task Commits

Each task was committed atomically:

1. **Task 1: Create shared modules and register in Makefile** - `551f9b41` (feat)
2. **Task 2: Wire spec files to import from RTLreplicateSpecCommon** - `84623e58` (refactor)

## Files Created/Modified
- `backend/RTLreplicateSpecCommon.v` - Shared Ltac tactics, type definitions, builtin_res utilities, and register-usage definitions for DMR/TMR specs
- `backend/RTLreplicateProofCommon.v` - Shared import preamble for DMR/TMR proof files
- `backend/RTLdmrspec.v` - Now imports from RTLreplicateSpecCommon instead of duplicating shared content
- `backend/RTLtmrspec.v` - Now imports from RTLreplicateSpecCommon instead of duplicating shared content
- `Makefile` - BACKEND variable updated to include both new common files

## Decisions Made
- Used `Require Export` instead of `Require Import` for RTLreplicateSpecCommon in the spec files. This ensures downstream proof files (RTLdmrproof.v, RTLtmrproof.v) automatically get unqualified access to shared names like `reg_used` without needing their own direct import of RTLreplicateSpecCommon.

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 3 - Blocking] Changed Require Import to Require Export for downstream compatibility**
- **Found during:** Task 2 (Wire spec files)
- **Issue:** Downstream proof files (RTLdmrproof.v, RTLtmrproof.v) reference `reg_used` unqualified. Using `Require Import RTLreplicateSpecCommon` in spec files does not re-export names to downstream importers of the spec files.
- **Fix:** Changed to `Require Export RTLreplicateSpecCommon` so names propagate transitively
- **Files modified:** backend/RTLdmrspec.v, backend/RTLtmrspec.v
- **Verification:** Both proof files compile cleanly
- **Committed in:** 84623e58 (Task 2 commit)

---

**Total deviations:** 1 auto-fixed (1 blocking)
**Impact on plan:** Essential fix for Coq module system compatibility. No scope creep.

## Issues Encountered
None beyond the deviation documented above.

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- Shared spec module in place and compiling, ready for Plan 02 (proof common module wiring)
- RTLreplicateProofCommon.v created but not yet wired into proof files (that is Plan 02's scope)
- All downstream files (dmrproof, tmrproof) verified to compile cleanly

---
*Phase: 02-shared-module-introduction*
*Completed: 2026-03-04*
