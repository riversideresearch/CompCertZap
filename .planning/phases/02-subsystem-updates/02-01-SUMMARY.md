---
phase: 02-subsystem-updates
plan: 01
subsystem: backend
tags: [tmr, builtin-replication, coq, rtl, map_builtin_arg]

# Dependency graph
requires:
  - phase: 01-classification-semantic-foundation
    provides: builtin_can_replicate predicate in common/Builtins.v
provides:
  - Safe builtin triplication in transf_instr (RTLtmr.v)
  - match_Ibuiltin_safe constructor in RTLtmrspec.v
  - rm_builtin_arg / rm_builtin_args inductives for builtin arg triples
  - rm_builtin_arg_map / rm_builtin_args_map lemmas connecting map_builtin_arg to spec
affects: [02-02 (TMR proof), 02-03 (color system)]

# Tech tracking
tech-stack:
  added: []
  patterns: [safe-builtin-triplication-mirrors-safe-Iop]

key-files:
  created: []
  modified:
    - backend/RTLtmr.v
    - backend/RTLtmrspec.v

key-decisions:
  - "Removed NOT_SAFE premise from match_Ibuiltin_1 -- disjoint from match_Ibuiltin_safe by NORES (~ is_BR bres) premise; avoids unprovable obligation for safe builtins with BR_none/BR_splitlong results"
  - "Kept NOT_SAFE on match_Ibuiltin_2 only -- prevents overlap with match_Ibuiltin_safe which also handles BR results"

patterns-established:
  - "Safe builtin triplication mirrors safe Iop pattern: green copy at pc, blue at n1, original at n2"
  - "rm_builtin_arg inductive relates builtin_arg triples through replication map, paralleling rm_l for plain registers"

requirements-completed: [TMR-01, TMR-02, TMR-03, TMR-04, TMR-05, INTG-01]

# Metrics
duration: 8min
completed: 2026-03-15
---

# Phase 2 Plan 1: TMR Safe Builtin Triplication Summary

**Safe builtin triplication in transf_instr gated by builtin_can_replicate, with rm_builtin_arg spec relation and match_Ibuiltin_safe constructor**

## Performance

- **Duration:** 8 min
- **Started:** 2026-03-15T02:10:21Z
- **Completed:** 2026-03-15T02:18:37Z
- **Tasks:** 1
- **Files modified:** 2

## Accomplishments
- Added explicit Ibuiltin case in transf_instr with builtin_can_replicate gate, emitting three per-color copies for safe builtins via map_builtin_arg
- Defined rm_builtin_arg and rm_builtin_args inductives relating builtin arg triples through the replication map
- Added match_Ibuiltin_safe constructor to match_instr, mirroring the match_Iop_safe pattern exactly
- Proved rm_builtin_arg_map and rm_builtin_args_map connecting map_builtin_arg to the relational spec
- Updated all existing proofs (state_incr_match_instr, transf_instr_match_instr) for the new constructor

## Task Commits

Each task was committed atomically:

1. **Task 1: Add safe builtin triplication to transf_instr and match_Ibuiltin_safe to spec** - `e3380870` (feat)

## Files Created/Modified
- `backend/RTLtmr.v` - Added Ibuiltin case with builtin_can_replicate gate in transf_instr; safe builtins with BR result get three per-color copies
- `backend/RTLtmrspec.v` - Added rm_builtin_arg/rm_builtin_args inductives, match_Ibuiltin_safe constructor, NOT_SAFE premise on match_Ibuiltin_2, rm_builtin_arg_map/rm_builtin_args_map lemmas, updated proofs

## Decisions Made
- Removed NOT_SAFE premise from match_Ibuiltin_1: it's already disjoint from match_Ibuiltin_safe by the NORES (~ is_BR bres) premise. Adding NOT_SAFE would make it impossible to match safe builtins with BR_none or BR_splitlong results (which use the generic path but could have builtin_can_replicate = true).
- Kept NOT_SAFE on match_Ibuiltin_2 only: both match_Ibuiltin_safe and match_Ibuiltin_2 handle BR results, so NOT_SAFE is needed to distinguish which constructor applies based on the builtin classification.

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Removed NOT_SAFE premise from match_Ibuiltin_1**
- **Found during:** Task 1
- **Issue:** Plan specified adding `builtin_can_replicate ef = false` to both match_Ibuiltin_1 and match_Ibuiltin_2. However, match_Ibuiltin_1 (non-BR results) is used for safe builtins with BR_none/BR_splitlong results that fall through to the generic path. With NOT_SAFE = false required, these cases would be unprovable since builtin_can_replicate ef = true.
- **Fix:** Removed NOT_SAFE from match_Ibuiltin_1 only. It's already disjoint from match_Ibuiltin_safe by the NORES premise.
- **Files modified:** backend/RTLtmrspec.v
- **Verification:** RTLtmrspec.vo builds successfully
- **Committed in:** e3380870

---

**Total deviations:** 1 auto-fixed (1 bug)
**Impact on plan:** Single deviation necessary for correctness. No scope creep.

## Issues Encountered
- Coq simpl tactic over-reduced builtin_can_replicate in Htransf, making rewrite impossible. Fixed by moving simpl before destruct of builtin_can_replicate so Coq reduces the if-then-else naturally.
- Auto-generated hypothesis names (H, H1) were fragile after adding new monadic bind steps. Used reserve_instr_inv tactic and explicit constructor names for robustness.

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- TMR pass and spec ready for proof work (Plan 02: RTLtmrproof.v safe builtin case)
- rm_builtin_arg_map and rm_builtin_args_map lemmas available for the proof
- Color system (Plan 03) can proceed in parallel

---
*Phase: 02-subsystem-updates*
*Completed: 2026-03-15*
