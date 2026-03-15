---
phase: 01-classification-semantic-foundation
plan: 01
subsystem: common
tags: [coq, builtins, tmr, classification, reflection]

# Dependency graph
requires: []
provides:
  - builtin_can_replicate_bf: Boolean classifier over builtin_function
  - builtin_can_replicate: Boolean classifier over external_function via lookup_builtin_function
  - builtin_can_fault: separate function for faulty semantics (currently equals builtin_can_replicate)
  - reflection and convenience lemmas bridging Bool/Prop for classification predicates
affects: [01-02-PLAN, 01-03-PLAN, RTLtmr, RTLcolor, RTLcolorcheck, RTLfault, RTLtolerant]

# Tech tracking
tech-stack:
  added: []
  patterns: [exhaustive-match-classification, reflect-bridge-pattern]

key-files:
  created: []
  modified: [common/Builtins.v]

key-decisions:
  - "Archi.ptr64 accessed via qualified name from transitive Require Archi in AST.v -- no new import needed"
  - "BI_subl classified conditionally via negb Archi.ptr64, mirroring is_protectedb Osubl pattern"
  - "builtin_can_fault defined as separate function equal to builtin_can_replicate for future divergence"
  - "Used simple Bool-equals-true reflect pattern rather than richer inductive Prop form"

patterns-established:
  - "Builtin classification pattern: exhaustive match on builtin_function with per-constructor true/false"
  - "EF dispatch pattern: match on external_function, resolve EF_builtin via lookup_builtin_function"

requirements-completed: [CLAS-01, CLAS-02, CLAS-03, CLAS-04, CLAS-06, CLAS-07]

# Metrics
duration: 2min
completed: 2026-03-15
---

# Phase 01 Plan 01: Builtin Classification Summary

**Shared builtin_can_replicate_bf/builtin_can_replicate/builtin_can_fault predicates with reflection lemmas in common/Builtins.v**

## Performance

- **Duration:** 2 min
- **Started:** 2026-03-15T01:20:06Z
- **Completed:** 2026-03-15T01:22:23Z
- **Tasks:** 2
- **Files modified:** 1

## Accomplishments
- Defined builtin_can_replicate_bf with exhaustive match: 18 unconditional true, BI_subl conditional on negb Archi.ptr64, BI_fmin/BI_fmax true, all BI_replicate false
- Defined builtin_can_replicate dispatching EF_builtin through lookup_builtin_function, false for all other external_function constructors
- Defined builtin_can_fault as separate function for future divergence
- Proved 5 lemmas: reflect bridge, replicate-excludes-protocol, protocol-always-false, lookup connection, non-EF_builtin exclusion

## Task Commits

Each task was committed atomically:

1. **Task 1: Define classification predicates** - `b71d1e8e` (feat)
2. **Task 2: Add reflection lemmas** - `51129ac9` (feat)

## Files Created/Modified
- `common/Builtins.v` - Added builtin_can_replicate_bf, builtin_can_replicate, builtin_can_fault definitions and 5 reflection/convenience lemmas (112 lines added)

## Decisions Made
- Archi.ptr64 is accessible via qualified name from transitive `Require Archi` in AST.v -- no additional import was needed in Builtins.v
- BI_subl classified conditionally via `negb Archi.ptr64`, mirroring the `is_protectedb Osubl` pattern from backend/RTL.v
- Used the simpler Bool-equals-true reflect pattern (`builtin_can_replicate_bf_prop b := builtin_can_replicate_bf b = true`) rather than a richer inductive Prop form, which is sufficient for downstream consumers

## Deviations from Plan

None - plan executed exactly as written.

## Issues Encountered
None

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- Classification predicates ready for consumption by plan 01-02 (builtin_sem_val_compat proof) and plan 01-03 (dispatcher updates in TMR/color/fault subsystems)
- No blockers identified

## Self-Check: PASSED

- FOUND: common/Builtins.v
- FOUND: common/Builtins.vo (compiled)
- FOUND: commit b71d1e8e (Task 1)
- FOUND: commit 51129ac9 (Task 2)
- FOUND: builtin_can_replicate_bf definition
- FOUND: builtin_can_fault definition
- FOUND: reflection lemma builtin_can_replicate_bf_spec

---
*Phase: 01-classification-semantic-foundation*
*Completed: 2026-03-15*
