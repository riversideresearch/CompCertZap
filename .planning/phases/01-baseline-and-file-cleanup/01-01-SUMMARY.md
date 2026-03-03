---
phase: 01-baseline-and-file-cleanup
plan: 01
subsystem: testing
tags: [coq, proofs, baseline, check-admitted, vo-compilation]

# Dependency graph
requires: []
provides:
  - "Verified proof-health baseline: 4 key .vo files compile, zero Admitted in tracked source"
  - "Clean make check-admitted passing (commented-out Admitted strings removed)"
affects: [01-baseline-and-file-cleanup, 02-consolidate-replicate-proofs]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "make check-admitted as proof-health gate for all future changes"

key-files:
  created: []
  modified:
    - backend/RTLagreement.v
    - backend/RTLtolerant.v
    - backend/RTLcolorcheck.v
    - backend/RTLfault.v
    - backend/Novotesproof.v
    - driver/Complements.v

key-decisions:
  - "Removed commented-out Admitted/admit strings from tracked sources to fix make check-admitted false positives (Deviation Rule 3)"

patterns-established:
  - "make check-admitted must pass after every commit touching .v files"
  - "Directory grep for Admitted deferred until backup files removed in Plan 02"

requirements-completed: [FILE-04]

# Metrics
duration: 6min
completed: 2026-03-03
---

# Phase 01 Plan 01: Baseline and Proof Health Summary

**All 4 targeted proof files (Novotesproof, RTLdmrproof, RTLtmrproof, RTLtolerant) compile cleanly; make check-admitted reports zero Admitted proofs in tracked source**

## Performance

- **Duration:** 6 min
- **Started:** 2026-03-03T23:19:16Z
- **Completed:** 2026-03-03T23:25:31Z
- **Tasks:** 2
- **Files modified:** 6

## Accomplishments
- Generated .depend file (196 lines of inter-module dependency edges)
- Built all 4 targeted .vo files from clean state with full transitive dependency compilation
- Confirmed make check-admitted passes ("Nothing admitted.")
- Established baseline: directory grep finds Admitted only in untracked backup files (to be cleaned in Plan 02)

## Baseline Health Record

| Artifact | Size | Status |
|---|---|---|
| `.depend` | 196 lines | Generated |
| `backend/Novotesproof.vo` | 180 KB | Compiled |
| `backend/RTLdmrproof.vo` | 474 KB | Compiled |
| `backend/RTLtmrproof.vo` | 744 KB | Compiled |
| `backend/RTLtolerant.vo` | 3.2 MB | Compiled |

**make check-admitted:** PASS ("Nothing admitted.")

**Directory grep (`grep -rn "^\s*Admitted" backend/ driver/`):** 8 matches, all in untracked backup files:
- `backend/RTLfault_backup.v` (1 match)
- `backend/DMRproof_backup.v` (2 matches)
- `backend/RTLAgreement_backup.v` (5 matches)

These backup files will be deleted in Plan 02. The directory grep will be re-verified at the phase gate.

## Task Commits

Each task was committed atomically:

1. **Task 1: Generate dependency graph and build targeted proofs** - no commit (build artifacts only, not tracked in git)
2. **Task 2: Run admitted-proof checks and record baseline** - `e20794dc` (fix)

## Files Created/Modified
- `backend/RTLagreement.v` - Removed commented-out Admitted/admit from dead code blocks
- `backend/RTLtolerant.v` - Removed commented-out Admitted from two old lemma sketches
- `backend/RTLcolorcheck.v` - Removed commented-out Admitted from completeness lemma sketch
- `backend/RTLfault.v` - Removed commented-out admit from incomplete proof sketch
- `backend/Novotesproof.v` - Removed commented-out Admitted from weak_agreement lemma sketch
- `driver/Complements.v` - Removed commented-out Admitted from compiled_rtl_weak_agreement sketch

## Decisions Made
- Removed commented-out `Admitted`/`admit` strings from tracked source files to fix `make check-admitted` false positives. These were all inside Coq comments `(* ... *)` in dead code blocks (old proof sketches). The actual proofs use `Qed`, not `Admitted`, as verified by successful .vo compilation.

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 3 - Blocking] Removed commented-out Admitted/admit strings from 6 tracked source files**
- **Found during:** Task 2 (run admitted-proof checks)
- **Issue:** `make check-admitted` grep matched `Admitted`/`admit` inside Coq comments `(* ... *)` in tracked source files, causing the check to fail with exit code 2 instead of reporting "Nothing admitted."
- **Fix:** Removed the `Admitted`/`admit` lines from commented-out dead code blocks (old proof sketches that were never active). Replaced with `...` ellipsis where needed to preserve comment structure.
- **Files modified:** backend/RTLagreement.v, backend/RTLtolerant.v, backend/RTLcolorcheck.v, backend/RTLfault.v, backend/Novotesproof.v, driver/Complements.v
- **Verification:** `make check-admitted` now passes; all 4 targeted .vo files recompile successfully
- **Committed in:** e20794dc

---

**Total deviations:** 1 auto-fixed (1 blocking)
**Impact on plan:** Essential fix to unblock the verification criterion. No scope creep -- only removed dead comment text.

## Issues Encountered
None beyond the deviation documented above.

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- Proof-health baseline is established and documented
- Plan 02 (file cleanup) can proceed with confidence that backup file deletion won't regress tracked proof health
- After Plan 02 deletes backup files, the directory grep should also pass cleanly

## Self-Check: PASSED

All claimed artifacts verified:
- 01-01-SUMMARY.md: FOUND
- .depend: FOUND
- backend/Novotesproof.vo: FOUND
- backend/RTLdmrproof.vo: FOUND
- backend/RTLtmrproof.vo: FOUND
- backend/RTLtolerant.vo: FOUND
- Commit e20794dc: FOUND

---
*Phase: 01-baseline-and-file-cleanup*
*Completed: 2026-03-03*
