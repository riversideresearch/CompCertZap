# Project State

## Project Reference

See: .planning/PROJECT.md (updated 2026-03-14)

**Core value:** A single shared builtin classification consumed by TMR, faulty semantics, coloring spec, checker, and oracle, with all proofs rebuilding.
**Current focus:** Phase 1: Classification and Semantic Foundation

## Current Position

Phase: 1 of 3 (Classification and Semantic Foundation)
Plan: 3 of 3 in current phase (PHASE COMPLETE)
Status: Phase 1 complete
Last activity: 2026-03-15 -- Completed 01-03 (builtin semantic validation)

Progress: [##########] 33%

## Performance Metrics

**Velocity:**
- Total plans completed: 3
- Average duration: 5.7min
- Total execution time: 0.28 hours

**By Phase:**

| Phase | Plans | Total | Avg/Plan |
|-------|-------|-------|----------|
| 01-classification-semantic-foundation | 3/3 | 17min | 5.7min |

**Recent Trend:**
- Last 5 plans: 01-01(2min), 01-02(5min), 01-03(10min)
- Trend: increasing (expected: semantic proofs more complex than definitions)

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

### Pending Todos

None yet.

### Blockers/Concerns

- [Phase 1 RESOLVED]: The `val_compat` vs `Val.lessdef` gap was the primary risk. OUTCOME: val_compat monotonicity proved for 18 non-shift builtins. Shift builtins (3) have a genuine limitation but restricted-case lemmas are available for Phase 3.
- [Phase 3]: Shift builtins in the tolerant proof may need special handling if the faulted register is the shift amount register

## Session Continuity

Last session: 2026-03-15
Stopped at: Completed 01-03-PLAN.md (builtin semantic validation) -- Phase 1 complete
Resume file: None
