---
phase: 08-validation-and-cleanup
plan: 01
subsystem: compiler
tags: [coq, cleanup, validation, novotes, ccomp, tmr]

# Dependency graph
requires:
  - phase: 07-theorem-recomposition
    provides: Complete fault tolerance proof with Qed (no Admitted)
provides:
  - Clean Compiler.v with no Novotes residue
  - Validated .vo files (zero Admitted)
  - Working ccomp binary with TMR support
  - Fixed Interp.ml OCaml extraction mismatch
affects: []

# Tech tracking
tech-stack:
  added: []
  patterns: []

key-files:
  created: []
  modified:
    - driver/Compiler.v
    - backend/Constpropproof.v
    - x86/Asmagreement.v
    - backend/CSEproof.v
    - backend/RTLLTLAgreement.v
    - Makefile
    - driver/Interp.ml

key-decisions:
  - "Novotes.v and Novotesproof.v kept on disk but removed from Makefile build list"
  - "Removed erased Builtins2.Two vote_type argument from Interp.ml (pre-existing extraction mismatch)"

patterns-established: []

requirements-completed: [VALID-01, VALID-02, VALID-03, VALID-04]

# Metrics
duration: 4min
completed: 2026-03-05
---

# Phase 08 Plan 01: Validation and Cleanup Summary

**Removed all Novotes residue from 6 source files, validated zero Admitted proofs across entire Coq development, and confirmed ccomp binary builds and compiles C with -tmr**

## Performance

- **Duration:** 4 min
- **Started:** 2026-03-05T21:28:59Z
- **Completed:** 2026-03-05T21:33:00Z
- **Tasks:** 2
- **Files modified:** 7

## Accomplishments
- Removed all 10 Novotes references (commented-out code, dead imports, TODO comments) from Compiler.v, Constpropproof.v, Asmagreement.v, CSEproof.v, RTLLTLAgreement.v, and Makefile
- Full `make proof` succeeds with zero errors; `make check-admitted` reports "Nothing admitted."
- ccomp binary builds and successfully compiles a TMR test program that returns correct result (exit code 42)

## Task Commits

Each task was committed atomically:

1. **Task 1: Remove all Novotes residue from active source files** - `11276c87` (chore)
2. **Task 2: Full build validation (proof, admitted check, ccomp binary)** - `dc1136be` (fix -- includes Interp.ml auto-fix)

## Files Created/Modified
- `driver/Compiler.v` - Removed 8 commented-out Novotes lines from pass lists and proof scripts
- `backend/Constpropproof.v` - Removed dead `Require Import Novotesproof`
- `x86/Asmagreement.v` - Removed `Novotes` from import list
- `backend/CSEproof.v` - Deleted obsolete TODO comment about Novotes
- `backend/RTLLTLAgreement.v` - Removed commented-out Novotes import
- `Makefile` - Removed Novotes.v and Novotesproof.v from BACKEND file list
- `driver/Interp.ml` - Fixed pre-existing extraction mismatch (removed erased vote_type arguments)

## Decisions Made
- Kept Novotes.v and Novotesproof.v on disk as reference code but removed from build (per plan)
- Fixed Interp.ml extraction mismatch as Rule 3 auto-fix (blocking ccomp build)

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 3 - Blocking] Fixed Interp.ml Cexec function signature mismatch**
- **Found during:** Task 2 (ccomp binary build)
- **Issue:** `driver/Interp.ml` passed `Builtins2.Two` as first argument to `Cexec.step_expr` and `Cexec.do_step`, but Coq extraction erases the vote_type parameter, causing OCaml type error
- **Fix:** Removed the `Builtins2.Two` argument from both call sites (lines 465 and 499)
- **Files modified:** driver/Interp.ml
- **Verification:** `make ccomp` builds successfully, TMR test compilation works
- **Committed in:** dc1136be

---

**Total deviations:** 1 auto-fixed (1 blocking)
**Impact on plan:** Pre-existing bug unrelated to Novotes removal. Fix required for ccomp binary to build.

## Issues Encountered
- Runtime library (`libcompcert.a`) needed `make runtime` before TMR test binary could link. This is expected behavior (not built by default with `make ccomp`).

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- All validation requirements (VALID-01 through VALID-04) satisfied
- Proof development is sound: zero Admitted proofs, all .vo files compile
- ccomp binary functional with TMR flag
- Ready for technical report or further development

## Self-Check: PASSED

All 7 modified files verified on disk. Both task commits (11276c87, dc1136be) verified in git log.

---
*Phase: 08-validation-and-cleanup*
*Completed: 2026-03-05*
