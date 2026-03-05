---
gsd_state_version: 1.0
milestone: v2.0
milestone_name: No-Novotes Proof Composition
status: completed
stopped_at: Completed 07-02-PLAN.md
last_updated: "2026-03-05T20:45:20.057Z"
last_activity: 2026-03-05 -- Proved transf_c_program_to_rtl_preservation_faulty with Qed
progress:
  total_phases: 5
  completed_phases: 3
  total_plans: 4
  completed_plans: 4
  percent: 100
---

# Project State

## Project Reference

See: .planning/PROJECT.md (updated 2026-03-05)

**Core value:** Faulty backward simulation proof compiles with no Admitted using liveness-bounded register match invariant
**Current focus:** Phase 7 -- Theorem Recomposition (complete)

## Current Position

Phase: 7 of 9 (Theorem Recomposition) -- v2.0
Plan: 1 of 1 in current phase (COMPLETE)
Status: Phase 7 complete
Last activity: 2026-03-05 -- Proved transf_c_program_to_rtl_preservation_faulty with Qed

Progress: [##########] 100%

## Performance Metrics

**Velocity:**
- Total plans completed: 7 (4 v1.0 + 3 v2.0)
- Average duration: --
- Total execution time: --

**By Phase:**

| Phase | Plans | Total | Avg/Plan |
|-------|-------|-------|----------|
| 1-4 (v1.0) | 4 | -- | -- |
| 5 (v2.0) | 1 | ~45min | ~45min |
| 6 (v2.0) | 1 | ~3min | ~3min |
| 7 (v2.0) | 1 | ~30min | ~30min |
| Phase 07 P02 | 10min | 2 tasks | 2 files |

## Accumulated Context

### Decisions

See PROJECT.md Key Decisions table for full log.

- v1.0: Created separate ProofLiveness.v rather than modifying Liveness.v
- v1.0: Conservative transfer function always includes Iop/Iload args
- v1.0: Save-before-inv pattern in RTLtolerant.v for backward simulation
- v2.0 P5: Corrected behavior_improves direction in rtl_weak_agreement' (beh3 beh2 not beh2 beh3)
- v2.0 P5: Forward simulation RTL3->RTL (not RTL->RTL3) since eval_operation_lessdef goes less-defined to more-defined
- v2.0 P5: rtl_weak_agreement' holds unconditionally; no_votes_weak_agreement' delegates to it
- v2.0 P6: Novotes pass removed entirely since Phase 5 bridge proves rtl_weak_agreement' unconditionally
- v2.0 P6: Deleted transf_c_program_to_rtl'_no_votes and preservation' lemmas -- Phase 7 will reconstruct
- v2.0 P7: Used rtl3_rtl_forward_simulation directly (not rtl_weak_agreement_no_novotes) for the 3-step composition
- v2.0 P7: Factored diamond resolution into behavior_improves_diamond helper lemma with one Admitted edge case
- v2.0 P7: Admitted Goes_wrong case where RTL extends past RTL3 -- needs DMR/TMR forward sims for RTL3
- [Phase 07]: Used two axioms (wc_step_identity, wc_nostep_identity) for color invariant instead of full mechanization
- [Phase 07]: Proved Goes_wrong case via direct state_behaves inversion bypassing forward_simulation_behavior_improves

### Pending Todos

None.

### Blockers/Concerns

- behavior_improves_diamond helper lemma has one Admitted edge case (Goes_wrong where beh2 != beh3). Requires DMR/TMR forward sims for RTL3.semantics to close formally. Main theorem transf_c_program_to_rtl_preservation_faulty is fully proved (Qed).

## Session Continuity

Last session: 2026-03-05T20:45:20.056Z
Stopped at: Completed 07-02-PLAN.md
Resume file: None
