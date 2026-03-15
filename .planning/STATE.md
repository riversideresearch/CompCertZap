---
gsd_state_version: 1.0
milestone: v1.0
milestone_name: milestone
status: in-progress
stopped_at: Completed 02-03-PLAN.md (color system and faulty semantics)
last_updated: "2026-03-15T02:17:06Z"
last_activity: 2026-03-15 -- Completed 02-03 (color system and faulty semantics)
progress:
  total_phases: 3
  completed_phases: 1
  total_plans: 6
  completed_plans: 4
  percent: 44
---

# Project State

## Project Reference

See: .planning/PROJECT.md (updated 2026-03-14)

**Core value:** A single shared builtin classification consumed by TMR, faulty semantics, coloring spec, checker, and oracle, with all proofs rebuilding.
**Current focus:** Phase 2: Subsystem Updates

## Current Position

Phase: 2 of 3 (Subsystem Updates)
Plan: 1 of 3 in current phase (02-03 complete, 02-01 and 02-02 pending)
Status: Phase 2 in progress
Last activity: 2026-03-15 -- Completed 02-03 (color system and faulty semantics)

Progress: [############------] 44%

## Performance Metrics

**Velocity:**
- Total plans completed: 4
- Average duration: 5.8min
- Total execution time: 0.38 hours

**By Phase:**

| Phase | Plans | Total | Avg/Plan |
|-------|-------|-------|----------|
| 01-classification-semantic-foundation | 3/3 | 17min | 5.7min |
| 02-subsystem-updates | 1/3 | 6min | 6min |

**Recent Trend:**
- Last 5 plans: 01-01(2min), 01-02(5min), 01-03(10min), 02-03(6min)
- Trend: stable (color system changes straightforward pattern application)

*Updated after each plan completion*

## Accumulated Context

### Decisions

Decisions are logged in PROJECT.md Key Decisions table.
Recent decisions affecting current work:

- [Roadmap]: Coarse granularity compresses 5 research phases into 3: classification+semantics, subsystem updates (TMR+color+fault in parallel), tolerant proof last
- [Roadmap]: Integration requirements (INTG-01 through INTG-04) assigned to Phase 2 with their respective subsystems; INTG-05 through INTG-07 assigned to Phase 3 as final validation
- [01-01]: Archi.ptr64 accessed via qualified name from transitive Require Archi in AST.v -- no new import needed
- [01-01]: BI_subl classified conditionally via negb Archi.ptr64, mirroring is_protectedb Osubl pattern
- [01-01]: Used simple Bool-equals-true reflect pattern rather than richer inductive Prop form
- [01-02]: Added explicit Require Import Builtins to 6 downstream consumers rather than changing RTL.v from Import to Export -- more targeted, avoids broadening RTL's re-export surface
- [01-03]: Shift builtins excluded from unified builtin_sem_val_compat dispatcher due to Int.ltu divergence under val_compat; restricted-case lemmas provided for Phase 3
- [01-03]: Generic val_compat_proj_num_inj lemma covers ALL mkbuiltin_nNt builtins uniformly via proj_num/inj_num composition
- [01-03]: Architecture-robust proof uses try-solve chains to handle conditional BI_subl case across ptr64/non-ptr64
- [02-03]: wc_Ibuiltin_safe restricted to BR res result (not BR_none/BR_splitlong)
- [02-03]: Generic wc_Ibuiltin gets builtin_can_replicate ef = false premise for mutual exclusivity
- [02-03]: Local OCaml builtin_can_replicate in oracle to avoid extraction dependency
- [02-03]: zap_allowed uses builtin_can_fault ef = true (Prop form) for Ibuiltin case

### Pending Todos

None yet.

### Blockers/Concerns

- [Phase 1 RESOLVED]: The `val_compat` vs `Val.lessdef` gap was the primary risk. OUTCOME: val_compat monotonicity proved for 18 non-shift builtins. Shift builtins (3) have a genuine limitation but restricted-case lemmas are available for Phase 3.
- [Phase 3]: Shift builtins in the tolerant proof may need special handling if the faulted register is the shift amount register

## Session Continuity

Last session: 2026-03-15
Stopped at: Completed 02-03-PLAN.md (color system and faulty semantics)
Resume file: None
