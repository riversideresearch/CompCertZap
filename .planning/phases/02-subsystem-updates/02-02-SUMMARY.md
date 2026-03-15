---
phase: 02-subsystem-updates
plan: 02
subsystem: backend
tags: [tmr-proof, backward-simulation, safe-builtin, coq]

# Dependency graph
requires:
  - phase: 02-subsystem-updates
    plan: 01
    provides: match_Ibuiltin_safe constructor, rm_builtin_arg relations
provides:
  - Safe builtin case in exec_Ibuiltin backward simulation proof
  - eval_builtin_arg remapping lemmas (rm_2, rm_3)
  - external_call_can_replicate_E0 lemma
affects: [03 (tolerant proof)]

# Tech tracking
tech-stack:
  added: []
  patterns: [three-step-compound-simulation-for-safe-builtins]

key-files:
  created: []
  modified:
    - backend/RTLtmrproof.v

key-decisions:
  - "Used eval_builtin_args_proper for regular-world (step 3) argument evaluation rather than a custom lemma"
  - "rm_wf_neq_2_3' separation lemma used to show green result register (res2) is distinct from blue argument registers"
  - "match_regsets_update reused from existing proof infrastructure for successor state"

patterns-established:
  - "Safe builtin compound step: green eval at pc->n1, blue eval at n1->n2, original eval at n2->succ, all producing E0 trace and same vres"
  - "eval_builtin_arg_rm_{2,3} lemmas parallel match_regs_1_{2,3}_eval_operation for builtin_arg type"

requirements-completed: [TMR-06, INTG-01, INTG-02]

# Metrics
duration: 5min
completed: 2026-03-15
---

# Phase 2 Plan 2: TMR Backward Simulation for Safe Builtins Summary

**Safe builtin case proved in exec_Ibuiltin backward simulation with three-step compound execution and match_regsets successor state**

## Performance

- **Duration:** 5 min
- **Tasks:** 2 (combined into single commit — helper lemmas + main proof case)
- **Files modified:** 1

## Accomplishments
- Proved external_call_can_replicate_E0: replicable builtins produce E0 trace and don't modify memory
- Added eval_builtin_arg_rm_2 and eval_builtin_arg_rm_3 for green/blue-world argument remapping through rm_builtin_arg
- Added eval_builtin_args_rm_2 and eval_builtin_args_rm_3 list-lifted versions
- Proved match_Ibuiltin_safe case in step_simulation: three exec_Ibuiltin steps (green/blue/original) simulate source step
- Established match_regsets for successor state with res1/res2/res3 all set to vres

## Task Commits

1. **Tasks 1+2: Helper lemmas + safe builtin backward simulation case** - `7d1a9b49` (feat)

## Files Created/Modified
- `backend/RTLtmrproof.v` - Added ~296 lines: external_call_can_replicate_E0, eval_builtin_arg_rm_{2,3}, eval_builtin_args_rm_{2,3}, match_Ibuiltin_safe case in exec_Ibuiltin

## Decisions Made
- Combined both tasks into a single commit since the helper lemmas are only used by the main proof case
- Used eval_builtin_args_proper for step 3 (regular copy) rather than a new custom lemma, since after green and blue writes, we only need to show original arg registers are unaffected
- The rm_wf_neq_2_3' separation lemma proves that green result register (fst(rm#res1)) is distinct from all blue argument registers (snd(rm#r) for r in bargs1)

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Fixed symmetry in match_regsets_get application**
- **Found during:** Task 2
- **Issue:** Previous draft had `symmetry; eapply match_regsets_get; eauto` which reverses the equality direction, causing `eapply` to unify arguments in wrong order
- **Fix:** Changed to `eapply match_regsets_get; eauto; right; auto`
- **Files modified:** backend/RTLtmrproof.v
- **Verification:** RTLtmrproof.vo builds successfully
- **Committed in:** 7d1a9b49

---

**Total deviations:** 1 auto-fixed (1 bug)
**Impact on plan:** Minor fix, no scope change.

## Issues Encountered
- None significant. The proof structure closely followed the existing safe Iop case pattern.

## User Setup Required
None.

## Next Phase Readiness
- All Phase 2 plans complete (02-01, 02-02, 02-03)
- TMR pass, spec, and proof all handle safe builtins
- Color system (spec, checker, oracle) handles safe builtins
- Faulty semantics allows faults on safe builtins
- Phase 3 (tolerant proof) can proceed

---
*Phase: 02-subsystem-updates*
*Completed: 2026-03-15*
