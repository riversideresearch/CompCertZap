---
phase: 02-subsystem-updates
plan: 03
subsystem: backend
tags: [coq, ocaml, color-system, fault-semantics, builtins, tmr]

# Dependency graph
requires:
  - phase: 01-classification-semantic-foundation
    provides: builtin_can_replicate, builtin_can_fault predicates in common/Builtins.v
provides:
  - wc_Ibuiltin_safe color spec constructor in RTLcolor.v
  - Safe builtin branch in check_col_instr with soundness proof in RTLcolorcheck.v
  - Oracle safe builtin constraint generation in RTLinfercolor.ml
  - Relaxed zap_allowed for safe builtins in RTLfault.v
affects: [03-tolerant-proof]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "Safe builtin color constraints mirror safe Iop pattern: basic color, args match result"
    - "Local OCaml builtin_can_replicate mirrors Coq definition for pre-extraction use"

key-files:
  created: []
  modified:
    - backend/RTLcolor.v
    - backend/RTLcolorcheck.v
    - backend/RTLinfercolor.ml
    - backend/RTLfault.v

key-decisions:
  - "wc_Ibuiltin_safe restricted to BR res result (not BR_none/BR_splitlong)"
  - "Generic wc_Ibuiltin gets builtin_can_replicate ef = false premise for mutual exclusivity"
  - "Local OCaml builtin_can_replicate in oracle to avoid extraction dependency"
  - "zap_allowed uses builtin_can_fault ef = true (Prop form) for Ibuiltin case"

patterns-established:
  - "Safe builtin color spec: same pattern as wc_Iop_safe with builtin_arg_forall"
  - "Checker safe branch: is_basicb + builtin_arg_forallb + Regset.for_all with or-chain"

requirements-completed: [COLR-01, COLR-02, COLR-03, COLR-04, FALT-01, FALT-02, INTG-03, INTG-04]

# Metrics
duration: 6min
completed: 2026-03-15
---

# Phase 2 Plan 3: Color System and Faulty Semantics Summary

**wc_Ibuiltin_safe color spec, checker with soundness proof, oracle safe-builtin constraints, and relaxed zap_allowed for safe builtins**

## Performance

- **Duration:** 6 min
- **Started:** 2026-03-15T02:10:23Z
- **Completed:** 2026-03-15T02:17:06Z
- **Tasks:** 2
- **Files modified:** 4

## Accomplishments
- Added wc_Ibuiltin_safe constructor to RTLcolor.v enabling safe builtins to have basic-colored args/results instead of White
- Updated checker in RTLcolorcheck.v with safe builtin branch and complete soundness proof
- Added oracle constraint generation for safe builtins in RTLinfercolor.ml mirroring the safe Iop pattern
- Relaxed zap_allowed in RTLfault.v from False to builtin_can_fault for Ibuiltin instructions

## Task Commits

Each task was committed atomically:

1. **Task 1: Add wc_Ibuiltin_safe to color spec and update checker with soundness proof** - `2746fa87` (feat)
2. **Task 2: Update oracle and faulty semantics for safe builtins** - `2206a64d` (feat)

## Files Created/Modified
- `backend/RTLcolor.v` - Added wc_Ibuiltin_safe constructor, updated generic wc_Ibuiltin with mutual exclusivity premise
- `backend/RTLcolorcheck.v` - Added safe builtin branch in check_col_instr, updated check_col_instr_sound proof
- `backend/RTLinfercolor.ml` - Added local builtin_can_replicate, safe builtin constraint generation
- `backend/RTLfault.v` - Relaxed zap_allowed for Ibuiltin from False to builtin_can_fault ef = true

## Decisions Made
- wc_Ibuiltin_safe restricted to BR res result (not BR_none or BR_splitlong) -- safe builtins classified by builtin_can_replicate all produce single-register results
- Generic wc_Ibuiltin now requires builtin_can_replicate ef = false for mutual exclusivity with safe case
- Implemented local OCaml builtin_can_replicate in RTLinfercolor.ml rather than depending on extraction, since extraction cannot be re-run until RTLtmrspec.v is fixed (Plan 01/02 in-progress changes)
- zap_allowed uses builtin_can_fault ef = true as Prop form, naturally yielding True for safe builtins and False for protocol/non-replicable builtins

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 3 - Blocking] Local OCaml builtin_can_replicate implementation**
- **Found during:** Task 2
- **Issue:** Coq extraction cannot be re-run due to pre-existing RTLtmrspec.v compilation error from Plan 01/02 changes. The extracted Builtins.ml does not contain builtin_can_replicate.
- **Fix:** Added local OCaml builtin_can_replicate and builtin_can_replicate_bf functions in RTLinfercolor.ml that mirror the Coq definition. Added imports for Builtins0 and Builtins1 modules.
- **Files modified:** backend/RTLinfercolor.ml
- **Verification:** ocamlopt -c backend/RTLinfercolor.ml compiles successfully
- **Committed in:** 2206a64d (Task 2 commit)

---

**Total deviations:** 1 auto-fixed (1 blocking)
**Impact on plan:** The local OCaml implementation faithfully mirrors the Coq definition and will be replaced by the extracted version once extraction is re-run. No correctness impact since the oracle is unverified.

## Issues Encountered
- Coq variable naming after `destruct b` on `builtin_res` used auto-generated name from constructor; fixed by using explicit `destruct b as [res| |]` intro pattern
- Pre-existing RTLtmrspec.v compilation error prevents full `make ccomp` build; verified oracle compilation directly with ocamlopt

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- Color system fully updated for safe builtins -- ready for Phase 3 tolerant proof
- Faulty semantics updated -- safe builtins can now be faulted in the single-fault model
- Note: full `make ccomp` will require Plan 01/02 (TMR pass) to be completed first

## Self-Check: PASSED

All files exist, all commits verified.

---
*Phase: 02-subsystem-updates*
*Completed: 2026-03-15*
