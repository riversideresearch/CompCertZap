# Plan: Proof-Liveness-Based Invariant Update

## Objective
Port the faulty simulation proof to a liveness-bounded invariant that is strong enough for simulation obligations, by introducing a dedicated `ProofLiveness` analysis instead of relying directly on CompCert's dead-code-oriented `Liveness.transfer`.

## Why this is needed
CompCert `Liveness.transfer` can omit `Iop`/`Iload` operands when the destination is dead, which is good for DCE but too weak for the simulation obligations in `backend/RTLtolerant.v` (e.g., proving argument `Val.lessdef` for current-step evaluation).

## Strategy
Define a new analysis `ProofLiveness.analyze` with a transfer function tailored to simulation proof needs, then use its result consistently in:
1. Well-coloredness definitions/checker soundness.
2. Register-match invariants in `RTLtolerant`.
3. Proof obligations that currently fail due to missing `Regset.In` facts.

## Phase 1: Add `ProofLiveness` analysis

## Files
- `backend/ProofLiveness.v` (new)
- `backend/Makefile` if needed for build wiring

## Actions
1. Copy the structure of `backend/Liveness.v`.
2. Define `transfer` to preserve enough operand liveness for simulation.
3. Instantiate Kildall backward solver and `analyze`.
4. Prove `analyze_solution` theorem analogous to `Liveness.analyze_solution`.

## Recommended transfer shape
Use a conservative first pass:
1. `Iop`: always include args, kill res.
2. `Iload`: always include args, kill dst.
3. Keep other cases close to existing `Liveness.transfer`.

This over-approximates current liveness and avoids proof gaps quickly. Later optimization can selectively relax cases if desired.

## Exit criteria
`ProofLiveness.v` builds standalone.

## Phase 2: Repoint coloring spec/checker to proof liveness

## Files
- `backend/RTLcolor.v`
- `backend/RTLcolorcheck.v`
- `backend/RTLinfercolor.ml` (already live-set-driven; adjust source of live sets)

## Actions
1. In `RTLcolor.v`, make `wc_function` carry `ProofLiveness.analyze f = Some live`.
2. Ensure `wc_instruction` consistency constraints remain quantified over `live !! pc`.
3. In `RTLcolorcheck.v`, replace `Liveness.analyze` assumptions with `ProofLiveness.analyze`.
4. Keep checker algorithm structure unchanged, only analysis source changes.

## Proof work
1. Update `check_col_function_sound` premise from `Liveness.analyze` to `ProofLiveness.analyze`.
2. Finish `check_col_instr_sound` (currently `Admitted`) under the new judgement.

## Exit criteria
- `make backend/RTLcolor.vo backend/RTLcolorcheck.vo`
- `make check-admitted` passes for color checker files.

## Phase 3: Update `RTLtolerant` invariant and local lemmas

## Files
- `backend/RTLtolerant.v`

## Actions
1. Replace all `LIVE: Liveness.analyze f = Some live` with `ProofLiveness.analyze f = Some live`.
2. Keep `match_rs` and `match_rs_upto` parameterized by `live !! pc`.
3. Add helper lemmas to discharge `Regset.In` goals needed at current instruction:
   - membership lemmas for instruction args in `transfer`.
   - helper lemmas for ros/builtin args as needed.
4. Add wrapper lemmas so proof scripts can derive `Val.lessdef` for args from `RS` with one line.

## Expected hotspot updates
1. `faulty_progress` protected `Iop` case near current failure (`~1367`).
2. `Iload`/`Istore` addressing argument cases.
3. `Icall`/`Itailcall` function operand cases.
4. Builtin argument lessdef obligations.
5. External call subproofs that currently do `apply RS` directly.

## Exit criteria
- `make backend/RTLtolerant.vo` succeeds.

## Phase 4: Integrate with top-level theorem path

## Files
- `driver/Complements.v` if signatures changed
- Any transitive proof files that consume `wc_function`

## Actions
1. Rebuild theorem chain to ensure new `wc_function`/analysis assumptions compose.
2. Adjust imports and theorem statements only where required.

## Exit criteria
- `make backend/RTLtolerant.vo driver/Complements.vo`

## Phase 5: Validation and performance sanity

## Checks
1. Proof integrity:
   - `make check-admitted`
   - `make backend/RTLtolerant.vo`
2. End-to-end compile path:
   - `make ccomp`
3. Runtime behavior:
   - compile one representative test with `-tmr` to ensure checker path still runs.

## Optional perf check
Re-run prior large-function workload to confirm sparse inference gains are retained.

## Risks and mitigations

## Risk 1
`check_col_instr_sound` re-proof takes longer than expected.
Mitigation: prove instruction cases incrementally and keep small helper lemmas per opcode family.

## Risk 2
Transfer definition is still too weak for a few `RTLtolerant` obligations.
Mitigation: strengthen only affected instruction transfer clauses and re-use same solver/proof framework.

## Risk 3
Changing `wc_function` ripples into many files.
Mitigation: preserve constructor shape and only swap the analysis premise (`Liveness` -> `ProofLiveness`) to minimize churn.

## Implementation order (recommended)
1. `ProofLiveness.v` complete.
2. `RTLcolor.v` / `RTLcolorcheck.v` switched and building.
3. `RTLtolerant.v` compile-fix loop.
4. Top-level theorem rebuild.

## Deliverables
1. New `backend/ProofLiveness.v` with solver and soundness lemma.
2. No `Admitted` in touched files.
3. `RTLtolerant` proof rebuilt with proof-liveness-bounded invariant.
