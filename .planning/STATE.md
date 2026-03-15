# Project State

## Project Reference

See: .planning/PROJECT.md (updated 2026-03-14)

**Core value:** A single shared builtin classification consumed by TMR, faulty semantics, coloring spec, checker, and oracle, with all proofs rebuilding.
**Current focus:** Phase 1: Classification and Semantic Foundation

## Current Position

Phase: 1 of 3 (Classification and Semantic Foundation)
Plan: 2 of 3 in current phase
Status: Executing
Last activity: 2026-03-15 -- Completed 01-02 (protocol-builtin recognizer migration)

Progress: [######░░░░] 22%

## Performance Metrics

**Velocity:**
- Total plans completed: 2
- Average duration: 3.5min
- Total execution time: 0.12 hours

**By Phase:**

| Phase | Plans | Total | Avg/Plan |
|-------|-------|-------|----------|
| 01-classification-semantic-foundation | 2/3 | 7min | 3.5min |

**Recent Trend:**
- Last 5 plans: 01-01(2min), 01-02(5min)
- Trend: -

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

### Pending Todos

None yet.

### Blockers/Concerns

- [Phase 1]: The `val_compat` vs `Val.lessdef` gap is the primary risk; if `builtin_sem_val_compat` cannot be proved for a candidate builtin, it must be removed from the whitelist before Phase 2 begins

## Session Continuity

Last session: 2026-03-15
Stopped at: Completed 01-02-PLAN.md (protocol-builtin recognizer migration)
Resume file: None
