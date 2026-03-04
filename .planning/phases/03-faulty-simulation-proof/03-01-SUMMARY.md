---
phase: 03-faulty-simulation-proof
plan: 01
subsystem: proof
tags: [coq, backward-simulation, liveness, regset, kildall, rtl, fault-tolerance]

# Dependency graph
requires:
  - phase: 01-proofliveness-analysis
    provides: "ProofLiveness.analyze, analyze_solution, reg_list_live_in, reg_list_live_incl"
  - phase: 02-color-system-update
    provides: "wc_function referencing ProofLiveness.analyze with WC_LIVE hypothesis"
provides:
  - "Fully proved faulty_backward_simulation theorem with zero Admitted"
  - "Liveness-bounded match_states and match_stackframes using ProofLiveness.analyze"
  - "Per-instruction args-in-live helper lemmas for RTL instruction forms"
  - "match_rs_weaken lemma for live set monotonicity"
  - "Fixed ProofLiveness.transfer for Ibuiltin (BR_splitlong/BR_none correctness)"
affects: [04-integration-validation]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "save-before-inv: save critical facts before destructive inv_wc/inv Hstep to avoid variable consumption"
    - "unify_live tactic: assert (live = live0) by congruence; subst after inv WC_FUN"
    - "color contradiction via Hros/Forall: specialize ros color fact, rewrite into HC, inv HC; inv Hc"

key-files:
  created: []
  modified:
    - backend/RTLtolerant.v
    - backend/ProofLiveness.v

key-decisions:
  - "Changed match_stackframes RS field from live!!pc to transfer f pc (live!!pc) to align with exec_return proof obligations"
  - "Changed ProofLiveness.transfer Ibuiltin case to match res with BR x => reg_dead x after | _ => after end (not reg_list_dead params_of_builtin_res) to handle BR_splitlong/BR_none as no-ops"
  - "Updated live_in_transfer_ibuiltin API from ~In r (params_of_builtin_res res) to forall x, res = BR x -> r <> x"
  - "Used H-numbered hypothesis names (H5, n0) for Ijumptable after inv_wc consumes named hypotheses"
  - "Used destruct b1 (not b0) for Icond boolean after eval_condition_lessdef unification"

patterns-established:
  - "save-before-inv: Before inv_wc or inv Hstep that substitutes variables, save needed facts with assert/pose proof"
  - "color-contradiction: For ros register exclusion, specialize ros color hypothesis, rewrite into HC, inv HC; inv Hc"
  - "match-goal for fragile names: Use match goal with patterns instead of concrete H-names after inversions"

requirements-completed: [FSIM-01, FSIM-02, FSIM-03, FSIM-04, FSIM-05, FSIM-06, FSIM-07, FSIM-08]

# Metrics
duration: 267min
completed: 2026-03-04
---

# Phase 3 Plan 1: Faulty Simulation Proof Summary

**Complete faulty backward simulation in RTLtolerant.v with liveness-bounded match relation using ProofLiveness.analyze, zero Admitted, all instruction cases proved including Ibuiltin vote/smove sub-cases**

## Performance

- **Duration:** ~4h 27min (spanning 3 agent sessions due to context limits)
- **Started:** 2026-03-04T19:27:00Z
- **Completed:** 2026-03-04T23:54:00Z
- **Tasks:** 2
- **Files modified:** 2 (backend/RTLtolerant.v: 843 insertions/187 deletions, backend/ProofLiveness.v: 1 insertion/1 deletion)

## Accomplishments

- Fully proved faulty backward simulation theorem (`faulty_backward_simulation`) with zero Admitted proofs
- Swapped all Liveness.analyze references to ProofLiveness.analyze in match_stackframes and match_states
- Added 10+ per-instruction liveness membership helper lemmas (args_in_live_iop, args_in_live_iload, etc.)
- Fixed ProofLiveness.transfer Ibuiltin case to correctly handle BR_splitlong and BR_none as no-ops
- Proved step_simulation for all RTL instruction cases: Inop, Iop, Iload, Istore, Icall, Itailcall, Ibuiltin (5 sub-cases), Icond, Ijumptable, Ireturn, function_internal, function_external, exec_return
- Proved faulty_progress for all RTL instruction cases

## Task Commits

Each task was committed atomically:

1. **Task 1: Foundation changes** - `781815a4` (feat) -- ProofLiveness import, LIVE swap, helper lemmas, inv_rs tactic fix, match_rs_weaken, forall2_lessdef_match_rs_init_regs update
2. **Task 2: Fix all proof cases** - `8777b533` (feat) -- Complete faulty_progress and step_simulation proofs, fix ProofLiveness.transfer Ibuiltin, change match_stackframes to use transfer set

## Files Created/Modified

- `backend/RTLtolerant.v` - Complete faulty backward simulation proof; match_stackframes/match_states use ProofLiveness.analyze; all step_simulation and faulty_progress cases proved
- `backend/ProofLiveness.v` - Fixed Ibuiltin transfer case: `match res with BR x => reg_dead x after | _ => after end` (was `reg_list_dead (params_of_builtin_res res) after`)

## Decisions Made

1. **match_stackframes RS uses transfer set, not raw live set**: Changed from `match_rs_upto res (live !! pc)` to `match_rs_upto res (ProofLiveness.transfer f pc (live !! pc))`. This was necessary because exec_return needs `Regset.In r (transfer f pc (live!!pc))` (the "live-before" set at the return point), and the raw `live!!pc` (the "live-after" set) is too small -- transfer can add registers that the instruction at pc needs.

2. **ProofLiveness.transfer Ibuiltin fix**: The original Ibuiltin transfer killed all registers in `params_of_builtin_res res`, but `regmap_setres` for `BR_splitlong` and `BR_none` is a no-op (does not modify the register map). This mismatch meant the transfer function was more aggressive than the actual semantics, making the BR_splitlong proof case impossible. Fixed by only killing the result register for `BR x`.

3. **live_in_transfer_ibuiltin API change**: Changed precondition from `~ In r (params_of_builtin_res res)` to `forall x, res = BR x -> r <> x`. This is more precise and aligns with the new transfer function behavior.

4. **Save-before-inv pattern**: Variables like `ifso`, `ifnot`, `pc'0`, `b0`, `tbl` are consumed by `inv Hstep; try congruence` and subsequent inversions (`inv H9`, `inv H10`). Key facts must be saved before destructive operations.

5. **H-numbered hypothesis names for Ijumptable**: After `inv_wc` consumes named hypotheses, the For_all hypothesis becomes `H5` and the register inequality becomes `n0`. These are fragile but unavoidable given the proof structure.

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Fixed ProofLiveness.transfer Ibuiltin case**
- **Found during:** Task 2 (BR_splitlong proof case)
- **Issue:** Transfer function killed all `params_of_builtin_res res` registers, but `regmap_setres (BR_splitlong ...)` is a no-op, making the proof obligation impossible
- **Fix:** Changed to `match res with BR x => reg_dead x after | _ => after end` so only `BR x` kills register `x`
- **Files modified:** backend/ProofLiveness.v
- **Verification:** `make backend/ProofLiveness.vo` succeeds; `make backend/RTLtolerant.vo` succeeds
- **Committed in:** 8777b533

**2. [Rule 1 - Bug] Changed match_stackframes RS field to use transfer set**
- **Found during:** Task 2 (exec_return proof case)
- **Issue:** match_stackframes stored `live!!pc` but exec_return needed `Regset.In r (transfer f pc (live!!pc))`. Since transfer adds registers, the subset relationship goes the wrong direction.
- **Fix:** Changed match_stackframes RS to `match_rs_upto res (ProofLiveness.transfer f pc (live !! pc))`, aligning the stored set with exec_return's proof obligation
- **Files modified:** backend/RTLtolerant.v
- **Verification:** All proof cases compile; exec_return uses `apply RS; assumption` directly
- **Committed in:** 8777b533

**3. [Rule 1 - Bug] Fixed Icall non-faulted stackframe match_rs derivation**
- **Found during:** Task 2 (Icall step_simulation case)
- **Issue:** After match_stackframes change, the non-faulted Icall case needed to build `match_rs_upto` for the transfer set from `match_rs` for the live set. Simple `apply match_rs_match_rs_upto; assumption` no longer worked.
- **Fix:** Used explicit `unfold match_rs in RS; unfold match_rs_upto; intros r Hneq; apply RS`
- **Files modified:** backend/RTLtolerant.v
- **Committed in:** 8777b533

---

**Total deviations:** 3 auto-fixed (3 bugs)
**Impact on plan:** All auto-fixes were necessary for proof correctness. The ProofLiveness.transfer fix was a genuine semantic bug (transfer was more aggressive than the actual instruction semantics). The match_stackframes change was a design refinement required by the proof obligations.

## Issues Encountered

- **Variable consumption by inv Hstep**: Icond and Ijumptable cases required saving facts before `inv Hstep; try congruence` because it substitutes variables like `pc'0`, `b0`, `ifso`, `ifnot`. Resolved by using `assert` to save needed facts before destructive inversions.
- **Boolean variable naming after eval_condition_lessdef**: In Icond, `b0` becomes `b1` after boolean unification. Required using `destruct b1` instead of `destruct b0`.
- **H-numbered hypothesis fragility**: After `inv_wc`, named hypotheses shift to H-numbered names. Required trial-and-error to find correct H-names (e.g., `H5` for For_all, `n0` for register inequality).
- **auto/eauto closing too many goals**: In exec_return and other cases, `auto` would close the Val.lessdef goal entirely, preventing bullet-structured proofs. Resolved by using explicit `[|assumption|assumption]` to control goal resolution.
- **Inconsistent library assumptions**: After changing ProofLiveness.v, RTLcolor.vo and RTLcolorcheck.vo needed recompilation. Resolved by removing stale .vo files.
- **Context window limitations**: The proof required 3 agent sessions due to the large number of instruction cases and subtle proof engineering. Each session built on the previous session's commits.

## User Setup Required

None - no external service configuration required.

## Next Phase Readiness

- Phase 3 is complete: RTLtolerant.v compiles with zero Admitted
- Phase 4 (Integration and Validation) can proceed: rebuild Complements.vo and validate end-to-end compiler build
- The ProofLiveness.transfer change may require recompilation of downstream files (RTLcolor.vo, RTLcolorcheck.vo already rebuilt)
- Potential concern: Complements.v references `faulty_backward_simulation` -- verify the theorem signature is unchanged

## Self-Check: PASSED

- backend/RTLtolerant.v: FOUND
- backend/ProofLiveness.v: FOUND
- 03-01-SUMMARY.md: FOUND
- Commit 781815a4 (Task 1): FOUND
- Commit 8777b533 (Task 2): FOUND
- Admitted count in RTLtolerant.v: 0
- ProofLiveness.analyze references: 13
- Standalone Liveness.analyze references: 0

---
*Phase: 03-faulty-simulation-proof*
*Completed: 2026-03-04*
