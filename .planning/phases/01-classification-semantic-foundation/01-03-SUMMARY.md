---
phase: 01-classification-semantic-foundation
plan: 03
subsystem: backend
tags: [coq, builtins, val_compat, fault-model, tmr, semantic-validation]

# Dependency graph
requires:
  - phase: 01-classification-semantic-foundation/01-01
    provides: builtin_can_replicate_bf classification predicate in common/Builtins.v
provides:
  - builtin_sem_val_compat: unified val_compat monotonicity dispatcher gated by builtin_can_replicate_bf
  - val_compat_mkbuiltin_n1t: generic monotonicity for 1-arg numerical builtins
  - val_compat_mkbuiltin_n2t: generic monotonicity for 2-arg numerical builtins
  - builtin_sem_val_compat_addl/mull/subl: per-builtin v2t monotonicity lemmas
  - standard_builtin_sem_val_compat: per-standard-builtin dispatcher
  - platform_builtin_sem_val_compat: per-platform-builtin dispatcher
  - builtin_sem_val_compat_shl/shr/sar_restricted: shift restricted-case lemmas
affects: [RTLtolerant, 03-01-PLAN, 03-02-PLAN]

# Tech tracking
tech-stack:
  added: []
  patterns: [proj_num-inj_num-val_compat, v2t-lifting-pattern, try-solve-architecture-robust]

key-files:
  created: []
  modified: [backend/RTLfault.v]

key-decisions:
  - "Shift builtins excluded from unified dispatcher via extra hypothesis due to Int.ltu divergence under val_compat"
  - "Generic val_compat_proj_num_inj lemma covers ALL mkbuiltin_nNt builtins uniformly"
  - "Architecture-robust proof using try-solve chains to handle Archi.ptr64 conditional cases"
  - "val_compat_mull' proved separately since Val.mull' differs from Val.mull (Vint*Vint->Vlong)"

patterns-established:
  - "proj_num/inj_num val_compat pattern: prove val_compat_proj_num_inj once, apply to all nNt builtins"
  - "v2t lifting pattern: solve_v2t_builtin Ltac lifts Val.* val_compat lemmas to builtin_sem wrappers"
  - "Architecture-robust try-solve: use try solve [...] chains to handle conditional cases (BI_subl on ptr64)"

requirements-completed: [SEMA-01, SEMA-02, SEMA-03]

# Metrics
duration: 10min
completed: 2026-03-15
---

# Phase 01 Plan 03: Builtin Semantic Validation Summary

**val_compat monotonicity proved for 19 safe builtins via generic proj_num/inj_num lemma and v2t lifting, with shift builtins documented as unprovable in general and excluded from unified dispatcher**

## Performance

- **Duration:** 10 min
- **Started:** 2026-03-15T01:25:07Z
- **Completed:** 2026-03-15T01:35:40Z
- **Tasks:** 2
- **Files modified:** 1

## Accomplishments
- Proved generic val_compat_proj_num_inj and val_compat_proj_num_inj2 helper lemmas covering all mkbuiltin_nNt builtins (13 standard + 2 platform = 15 builtins)
- Proved val_compat monotonicity for BI_addl, BI_mull (via Val.mull'), BI_subl (conditional on Archi.ptr64=false) = 3 additional builtins
- Documented that shift builtins (BI_i64_shl, BI_i64_shr, BI_i64_sar) do NOT satisfy general val_compat monotonicity due to Int.ltu divergence, with restricted-case lemmas for same-shift-amount
- Proved unified builtin_sem_val_compat dispatcher gated by builtin_can_replicate_bf=true with shift exclusion, dispatching to per-class lemmas
- All lemma statements use val_compat (not Val.lessdef), satisfying SEMA-03

## Task Commits

Each task was committed atomically:

1. **Task 1: Prove val_compat for mkbuiltin_nNt builtins** - `c8080842` (feat)
2. **Task 2: Prove val_compat for mkbuiltin_v2t builtins and unified dispatcher** - `00e9407a` (feat)

## Files Created/Modified
- `backend/RTLfault.v` - Added Require Import Builtins; added ~360 lines: val_compat_proj_num_inj helpers, per-class lemmas (n1t, n2t, addl, mull, subl), shift documentation and restricted lemmas, standard/platform/unified dispatchers

## Decisions Made
- **Shift exclusion from unified dispatcher:** The general val_compat monotonicity for shift builtins (BI_i64_shl/shr/sar) is NOT provable because Int.ltu can diverge between val_compat-related shift amounts, producing Vlong on one side and Vundef on the other. Since val_compat (Vlong _) Vundef is not a constructor, the proof does not close. The unified dispatcher adds a secondary hypothesis excluding shifts. Restricted-case lemmas (same shift amount on both sides) are provided for Phase 3.
- **Generic proj_num/inj_num approach:** Instead of proving per-builtin lemmas for all 15 nNt builtins, a single generic val_compat_proj_num_inj lemma covers all cases uniformly by proving that val_compat is preserved through the proj_num/inj_num composition.
- **Architecture-robust proofs:** The standard_builtin_sem_val_compat proof uses `try solve [...]` chains rather than explicit case bullets, making it robust across architectures where Archi.ptr64 may differ (BI_subl is discriminated on x86_64 but remains as a subgoal on 32-bit).
- **Separate val_compat_mull' lemma:** Val.mull' (used by BI_mull) differs from Val.mull -- it takes Vint*Vint->Vlong rather than Vlong*Vlong->Vlong, so a separate val_compat lemma was needed.

## Deviations from Plan

None - plan executed exactly as written. The shift builtin limitation was anticipated by the plan (research finding) and handled per the plan's option (a): prove what we can, document the shift issue as a finding.

## Issues Encountered
- **Forall2 inversion naming:** The `inv Hcompat` tactic produced different hypothesis names depending on whether `simpl in *` was applied first. Resolved by using `simpl in Hsem` (only on the semantic hypothesis) and explicit `match goal with` for Forall2 inversions.
- **Archi.ptr64 case elimination:** On x86_64, `Archi.ptr64 = true` causes BI_subl to be discriminated, changing the number of proof subgoals. Resolved by using `try solve` chains instead of explicit numbered bullets.

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- val_compat monotonicity is proved for all safe non-shift builtins (15 nNt + 3 v2t = 18 builtins, conditional on architecture for BI_subl)
- Shift builtins remain in the builtin_can_replicate_bf whitelist but require a restricted formulation in Phase 3's tolerant proof
- The unified builtin_sem_val_compat dispatcher is ready for consumption by RTLtolerant.v (Phase 3)
- Phase 1 complete: classification (Plan 01), protocol migration (Plan 02), and semantic validation (Plan 03) are all done

## Self-Check: PASSED

- FOUND: backend/RTLfault.v
- FOUND: backend/RTLfault.vo (compiled)
- FOUND: commit c8080842 (Task 1)
- FOUND: commit 00e9407a (Task 2)
- FOUND: builtin_sem_val_compat unified dispatcher
- FOUND: val_compat_mkbuiltin_n1t generic lemma
- FOUND: val_compat_mkbuiltin_n2t generic lemma
- FOUND: builtin_can_replicate_bf gate hypothesis
- FOUND: Forall2 val_compat in lemma statements

---
*Phase: 01-classification-semantic-foundation*
*Completed: 2026-03-15*
