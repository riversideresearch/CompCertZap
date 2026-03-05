---
phase: 02-color-system-update
plan: 01
subsystem: backend
tags: [coq, liveness, color-system, proof, regset, for_all]

# Dependency graph
requires:
  - phase: 01-proofliveness-analysis
    provides: ProofLiveness.v conservative liveness analysis with analyze_solution lemma
provides:
  - RTLcolor.v wc_function referencing ProofLiveness.analyze
  - RTLcolorcheck.v check_function dispatching on ProofLiveness.analyze
  - Fully proved check_col_instr_sound (no Admitted) covering 14 instruction cases
affects: [03-tolerant-proof-update, 04-pipeline-integration]

# Tech tracking
tech-stack:
  added: []
  patterns: [Regset.for_all_2 bridge pattern for color checker proofs]

key-files:
  created: []
  modified:
    - backend/RTLcolor.v
    - backend/RTLcolorcheck.v

key-decisions:
  - "Used Regset.for_all_2 instead of PTree_Properties.for_all_correct since checker iterates over Regset not PTree"
  - "Used eqb_sound instead of is_colorb_sound since col returns color (not option color)"
  - "Introduced compat_bool_tac Ltac with ?-prefixed names to avoid variable capture in complex proof contexts"

patterns-established:
  - "Regset.for_all_2 bridge: apply Regset.for_all_2 in H; [| compat_bool_tac] to convert Regset.for_all boolean to For_all propositional"

requirements-completed: [COLR-01, COLR-02, COLR-03, COLR-04]

# Metrics
duration: 7min
completed: 2026-03-04
---

# Phase 2 Plan 1: Color System Update Summary

**Swapped color system from Liveness.analyze to ProofLiveness.analyze and completed check_col_instr_sound proof with Regset.for_all_2 bridge for all 14 instruction cases**

## Performance

- **Duration:** 7 min
- **Started:** 2026-03-04T18:46:50Z
- **Completed:** 2026-03-04T18:54:46Z
- **Tasks:** 2
- **Files modified:** 2

## Accomplishments
- Replaced Liveness.analyze with ProofLiveness.analyze in both RTLcolor.v (declarative spec) and RTLcolorcheck.v (verified checker)
- Completed the check_col_instr_sound proof, eliminating the last Admitted in the color checker
- Both files compile with zero Admitted proofs

## Task Commits

Each task was committed atomically:

1. **Task 1: Swap Liveness to ProofLiveness in RTLcolor.v** - `d35b32ca` (feat)
2. **Task 2: Swap Liveness to ProofLiveness in RTLcolorcheck.v and complete check_col_instr_sound proof** - `34339c70` (feat)

## Files Created/Modified
- `backend/RTLcolor.v` - Declarative color system spec; import and wc_function constructor now reference ProofLiveness.analyze
- `backend/RTLcolorcheck.v` - Verified Boolean color checker; import, check_function, and check_col_function_sound reference ProofLiveness.analyze; check_col_instr_sound fully proved with Qed

## Decisions Made
- Used Regset.for_all_2 as the bridge from boolean Regset.for_all to propositional For_all, replacing the old PTree_Properties.for_all_correct approach from the commented-out proof
- Used eqb_sound (color equality) directly instead of is_colorb_sound (option color equality) since the current col signature returns color, not option color
- Introduced compat_bool_tac Ltac using ?-prefixed variable names to avoid name capture in contexts where destruct introduces variables named x

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Fixed variable name collisions in proof script**
- **Found during:** Task 2 (check_col_instr_sound proof)
- **Issue:** After destruct instr, Coq binds `r` for register arguments (res/src/arg), conflicting with proof variable names. Also `x` was captured by destruct in builtin cases. Additionally, For_all argument ordering was incorrect (Regset.In must come first).
- **Fix:** Used `r0` instead of `r` for For_all introductions; fixed argument ordering to put Regset.In first; used ?-prefixed names in compat_bool_tac
- **Files modified:** backend/RTLcolorcheck.v
- **Verification:** coqc compiles successfully
- **Committed in:** 34339c70 (Task 2 commit)

**2. [Rule 1 - Bug] Fixed double-replacement of Liveness references**
- **Found during:** Task 2 (import swap)
- **Issue:** replace_all for "Liveness.analyze f" matched as substring within "ProofLiveness.analyze f", creating "ProofProofLiveness.analyze f"
- **Fix:** Applied corrective replace_all for "ProofProofLiveness" -> "ProofLiveness"
- **Files modified:** backend/RTLcolorcheck.v
- **Verification:** grep confirms all references are ProofLiveness (not ProofProofLiveness)
- **Committed in:** 34339c70 (Task 2 commit)

---

**Total deviations:** 2 auto-fixed (2 bugs)
**Impact on plan:** Both auto-fixes were necessary for proof compilation. No scope creep.

## Issues Encountered
- Variable name collisions required careful renaming -- Coq's destruct binds `r` for register fields, conflicting with for_all quantified variables
- The Iop case binds `n` as successor (not `n0` as initially assumed), requiring `col n r` instead of `col n0 r` for `col succ res`

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- RTLcolor.v and RTLcolorcheck.v now reference ProofLiveness.analyze
- Downstream files (RTLtolerant.v, Complements.v) will need updating in Phase 3 and Phase 4
- The Regset.for_all_2 bridge pattern is established for any future proof maintenance

---
*Phase: 02-color-system-update*
*Completed: 2026-03-04*
