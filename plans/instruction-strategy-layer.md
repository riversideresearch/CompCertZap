# Plan: TMR Instruction-Strategy Layer

## Objective
Refactor the TMR pass so that the fault-tolerance policy for each RTL instruction is described once, by an explicit instruction-strategy layer, and then consumed by:

1. The transformation implementation in `backend/RTLtmr.v`.
2. The relational specification in `backend/RTLtmrspec.v`.
3. The coloring rules in `backend/RTLcolor.v` / `backend/RTLcolorcheck.v`.
4. The OCaml color inference oracle in `backend/RTLinfercolor.ml`.

The goal is not to change the current protection policy immediately, but to make that policy explicit and shared.

## Motivation
The current TMR design works, but the instruction policy is duplicated across several modules:

1. `backend/RTLtmr.v` decides how to transform each instruction.
2. `backend/RTLtmrspec.v` re-encodes the same policy in relational form.
3. `backend/RTLcolor.v` and `backend/RTLcolorcheck.v` encode the color obligations induced by that policy.
4. `backend/RTLinfercolor.ml` re-encodes the same obligations as union-find constraints.

This duplication creates three problems:

1. Policy changes require synchronized edits in several places.
2. It is easy for documentation, implementation, and proofs to drift apart.
3. Backend extensions will be harder because the high-level strategy is not factored from the low-level RTL sequence that realizes it.

## Current effective policy
Today, the pass in `backend/RTLtmr.v` effectively classifies instructions as follows:

1. `Inop`: pass through unchanged.
2. `Iop` with `is_protectedb op = false`: replicate in the two shadow worlds, then execute the original instruction in the main world.
3. `Iop` with `is_protectedb op = true`: vote arguments first, execute once in the main world, then copy the result to shadows.
4. Most other instructions: vote arguments first, execute once in the main world, then copy the result to shadows if there is one.

This policy is also reflected separately in:

1. `match_instr` cases in `backend/RTLtmrspec.v`.
2. Well-coloredness rules in `backend/RTLcolor.v`.
3. Constraint generation in `backend/RTLinfercolor.ml`.

## Proposed abstraction
Introduce a small datatype that classifies an RTL instruction by its fault-tolerance strategy.

Possible first-cut shape:

```coq
Inductive ft_exec_mode :=
| FT_passthrough
| FT_replicate
| FT_single_world.

Record ft_plan := {
  fp_sync_regs : list reg;
  fp_exec_mode : ft_exec_mode;
  fp_copy_result : bool;
}.
```

Or, if slightly more structure is useful:

```coq
Inductive ft_result_mode :=
| FT_no_result
| FT_leave_result
| FT_copy_result_to_shadows.

Record ft_plan := {
  fp_sync_regs : list reg;
  fp_exec_mode : ft_exec_mode;
  fp_result_mode : ft_result_mode;
}.
```

Then define a single classifier:

```coq
Definition classify_instr (re : regenv) (i : instruction) : res ft_plan := ...
```

This classifier becomes the source of truth for the TMR policy.

## Non-goal
This refactor should not introduce a new IR. The strategy layer should classify and annotate instructions, not describe exact fresh nodes or exact emitted RTL code.

## Intended layering

## Layer 1: classification
The classifier determines:

1. Which registers must be synchronized before executing the instruction.
2. Whether the instruction executes in all three worlds or only in the main world.
3. Whether its result must be copied back into shadows.

This is the policy layer.

## Layer 2: realization
The pass consumes the classification and emits the concrete RTL sequence:

```coq
Definition emit_plan
  (re : regenv) (rm : PMap.t (reg * reg)) (pc : node)
  (i : instruction) (p : ft_plan) : mon unit := ...
```

Then `transf_instr` becomes:

```coq
do plan <- classify_instr re instr;
emit_plan re rm pc instr plan
```

This is the implementation layer.

## Layer 3: proof/checker interpretation
The same classification should drive:

1. The relational `match_instr` cases in `backend/RTLtmrspec.v`.
2. The color obligations in `backend/RTLcolor.v`.
3. The Boolean checker logic in `backend/RTLcolorcheck.v`.
4. The OCaml constraint generator in `backend/RTLinfercolor.ml`.

These components should consume the same strategy notion rather than re-deriving policy by ad hoc pattern matching.

## Recommended initial strategy categories
The first version should stay close to the current implementation.

1. `FT_passthrough`
   For `Inop`.
2. `FT_replicate`
   For currently replicable `Iop` cases, namely those with `~ is_protected op`.
3. `FT_single_world` plus `fp_sync_regs`
   For instructions whose arguments are voted first and then run once.
4. `FT_single_world` plus `fp_copy_result`
   For single-world instructions whose result must be copied to shadows.

This preserves current behavior while making it explicit.

## Benefits

## Benefit 1: one source of truth
The decision "how is this instruction protected?" moves into one definition instead of being duplicated across Coq and OCaml.

## Benefit 2: easier policy changes
If later work decides that some builtins, loads, or calls should move from "vote then run" to "replicate", the main change is to the classifier. The implementation, spec, and checker remain aligned by construction.

## Benefit 3: less drift
The current codebase already has mild drift between comments and implementation. A named strategy layer should make such mismatches more obvious.

## Benefit 4: better backend portability
For a future RISC-V asm theorem, the strategy categories are likely to survive, while only the realization changes. That gives a cleaner path from RTL proof-of-concept to backend-specific implementations.

## Benefit 5: possible DMR/TMR unification
DMR and TMR have similar shapes today. In the long run, both passes could share a common classification layer, with different realizers:

1. DMR: "sync" means compare/check.
2. TMR: "sync" means majority vote.

This should reduce design drift between `backend/RTLdmr.v` and `backend/RTLtmr.v`.

## Phase 1: Introduce the classification datatype

## Files
- `backend/RTLtmr.v`
- possibly a new shared helper file if the datatype should later be shared with DMR

## Actions
1. Define `ft_plan` and any supporting enums.
2. Add `classify_instr`.
3. Keep the classification exactly equivalent to current behavior.

## Exit criteria
`classify_instr` exists and is clearly the unique place where the TMR policy is chosen.

## Phase 2: Rewrite the pass to consume plans

## Files
- `backend/RTLtmr.v`

## Actions
1. Factor existing emission logic into helper functions such as:
   - emit passthrough
   - emit replicated op
   - emit voted single-world instruction
   - emit copy-result-to-shadows
2. Rewrite `transf_instr` as classify-then-emit.
3. Keep generated code identical if possible.

## Exit criteria
`transf_instr` no longer contains the main policy case split directly.

## Phase 3: Rebase the relational specification on the strategy layer

## Files
- `backend/RTLtmrspec.v`

## Actions
1. Reorganize `match_instr` so that its major cases correspond to strategy categories.
2. Avoid re-encoding policy decisions that the classifier already made.
3. Add bridging lemmas from `classify_instr` to the corresponding `match_instr` constructor.

## Exit criteria
Spec structure matches the strategy layer instead of independently mirroring the raw instruction syntax.

## Phase 4: Rebase color obligations on the strategy layer

## Files
- `backend/RTLcolor.v`
- `backend/RTLcolorcheck.v`
- `backend/RTLinfercolor.ml`

## Actions
1. Factor color obligations by strategy class where practical.
2. Reuse the strategy notion when determining:
   - which regs are synchronized before execution
   - whether a result becomes White
   - whether result repair is required
3. Keep the current White/Pink/Red protocol initially.

## Exit criteria
Color checker and oracle consume the same strategy concepts as the pass and spec.

## Phase 5: Evaluate sharing with DMR

## Files
- `backend/RTLdmr.v`
- `backend/RTLdmrspec.v`
- any new shared helper module

## Actions
1. Compare DMR and TMR classifications after the TMR refactor.
2. Determine whether a shared "fault-tolerance instruction classification" module is worth introducing.
3. Only share what is truly common: instruction categories and sync/result metadata, not backend-specific realizers.

## Exit criteria
Clear decision on whether the classification layer should remain TMR-specific or become shared by DMR/TMR.

## Risks

## Risk 1
The abstraction may be too weak, forcing special-case escape hatches everywhere.

Mitigation: keep the first version close to the current implementation and add only the metadata that is already being recomputed in multiple places.

## Risk 2
The abstraction may be too detailed and effectively become a second IR.

Mitigation: do not encode fresh nodes or emitted instruction sequences in the plan.

## Risk 3
The proof churn may outweigh the cleanup in the short term.

Mitigation: stage the work so that `backend/RTLtmr.v` is refactored first, and the spec/checker migration happens only after the classifier has stabilized.

## Suggested first milestone
The first milestone should be intentionally small:

1. Add `ft_plan` and `classify_instr`.
2. Rewrite `transf_instr` around classify-then-emit.
3. Prove or test that generated code is unchanged.

That alone should already make the design clearer and reduce future maintenance cost.
