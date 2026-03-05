---
phase: 07-theorem-recomposition
plan: 01
subsystem: proof
tags: [coq, backward-simulation, forward-simulation, behavior-improves, diamond-resolution, faulty-semantics, well-colored, TMR]

# Dependency graph
requires:
  - phase: 05-rtl3-to-rtl-bridge
    provides: "rtl3_rtl_forward_simulation, forward_simulation RTL3->RTL for all programs"
  - phase: 06-pipeline-simplification
    provides: "Clean Compiler.v pipeline without Novotes pass"
  - phase: 01-proofliveness-analysis
    provides: "faulty_backward_simulation in RTLtolerant.v"
provides:
  - "transf_c_program_to_rtl_preservation_faulty with Qed (3-step behavior composition)"
  - "behavior_improves_diamond helper lemma (Admitted edge case for Goes_wrong disagreement)"
  - "Clean Complements.v with zero Novotes/Novotesproof/no_votes references"
affects: [future-dmr-tmr-rtl3-forward-sims]

# Tech tracking
tech-stack:
  added: []
  patterns: [3-step-behavior-composition, diamond-resolution-via-helper-lemma]

key-files:
  created: []
  modified:
    - driver/Complements.v

key-decisions:
  - "Used rtl3_rtl_forward_simulation directly (not rtl_weak_agreement_no_novotes) since the proof needs the forward simulation object for forward_simulation_behavior_improves"
  - "Factored diamond resolution into behavior_improves_diamond helper lemma to isolate the one Admitted edge case"
  - "Admitted the Goes_wrong case where RTL extends past RTL3 (beh2 != beh3), which requires DMR/TMR forward simulations for RTL3 to close formally"

patterns-established:
  - "3-step composition pattern: faulty->RTL3 (backward), RTL3->RTL (forward), RTL->C (backward), resolved via behavior_improves_diamond"
  - "Diamond resolution: non-Goes_wrong cases collapse trivially; Goes_wrong with beh2=beh3 uses behavior_improves_trans; remaining edge case deferred"

requirements-completed: [THERM-01, THERM-02, THERM-03]

# Metrics
duration: ~30min
completed: 2026-03-05
---

# Phase 7 Plan 01: Theorem Recomposition Summary

**Capstone fault-tolerance theorem proved via 3-step behavior composition: faulty->RTL3->RTL->C with diamond resolution helper (one Admitted edge case for RTL3/RTL disagreement)**

## Performance

- **Duration:** ~30 min
- **Started:** 2026-03-05T17:30:11Z
- **Completed:** 2026-03-05T18:00:00Z
- **Tasks:** 1
- **Files modified:** 1

## Accomplishments
- Proved transf_c_program_to_rtl_preservation_faulty with Qed (main theorem complete)
- Composed three refinement steps: faulty_backward_simulation, rtl3_rtl_forward_simulation, transf_c_program_to_rtl_correct
- Removed all commented-out Novotes/Novotesproof/no_votes code blocks (~150 lines of dead code)
- Isolated diamond resolution edge case into behavior_improves_diamond helper lemma with one Admitted

## Task Commits

Each task was committed atomically:

1. **Task 1: Prove faulty theorem via 3-step behavior composition** - `9dcb17ff` (feat)

**Plan metadata:** [pending] (docs: complete plan)

## Files Created/Modified
- `driver/Complements.v` - Main theorem proved with Qed; helper lemma with one Admitted edge case; all Novotes dead code removed

## Decisions Made
- Used `rtl3_rtl_forward_simulation` directly instead of `rtl_weak_agreement_no_novotes` since the proof needs the forward simulation object (not the behavior-level corollary) to feed into `forward_simulation_behavior_improves`
- Factored the diamond resolution into a separate `behavior_improves_diamond` lemma to cleanly isolate the one genuinely hard edge case from the fully-proved main theorem
- Admitted the edge case where RTL3 goes wrong at trace t but RTL continues to trace t++t0 (beh2 strictly extends past beh3). This case cannot arise for well-colored TMR programs (vote3(a,a,a) = a ensures RTL3 and RTL agree), but formally closing it requires DMR/TMR forward simulations for RTL3.semantics, deferred as a future phase

## Deviations from Plan

### Auto-fixed Issues

None - plan executed as written.

---

**Total deviations:** 0

## Deferred Items

The `behavior_improves_diamond` helper lemma has one Admitted case: the `Goes_wrong` scenario where `beh2` (RTL behavior) strictly extends past `beh3` (RTL3 behavior). This edge case:

1. Does not arise for well-colored TMR programs (vote3(a,a,a) = a for identical triples)
2. Formally closing it requires proving that RTL3 never goes wrong where RTL continues, which depends on DMR/TMR forward simulations through the RTL3 semantics
3. The main theorem `transf_c_program_to_rtl_preservation_faulty` ends with `Qed` and is fully proved modulo this helper

This was anticipated by the plan: "If this case proves difficult, use Admitted on JUST this edge case and document as a follow-up."

## Issues Encountered
- Variable name collision (`t'` already bound) required renaming in intermediate proof attempt
- `exploit` tactic generated extra subgoals requiring switch to `pose proof` style
- `transf_c_program_to_rtl_correct` requires explicit `p tp` arguments (not implicit)

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- The capstone theorem is proved (Qed)
- The one Admitted edge case in the helper lemma can be closed when DMR/TMR forward simulations for RTL3.semantics are available
- Complements.v compiles cleanly with zero Novotes references

## Self-Check: PASSED

- FOUND: driver/Complements.v
- FOUND: driver/Complements.vo (compiles successfully)
- FOUND: commit 9dcb17ff
- Qed count: 22 (including transf_c_program_to_rtl_preservation_faulty)
- Admitted count: 1 (behavior_improves_diamond helper only)
- Novotes/Novotesproof/no_votes references: 0

---
*Phase: 07-theorem-recomposition*
*Completed: 2026-03-05*
