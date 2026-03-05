# Plan: Remove `novotes` from RTL Pipeline and Fault-Tolerance Composition

## Goal
Refactor the RTL-level fault-tolerance proof so `transf_c_program_to_rtl_preservation_faulty` no longer depends on `no_votes`, and remove the `Novotes` checker pass from `driver/Compiler.v`.

## Simplification principles
1. Keep one canonical RTL semantics (`RTL.semantics`) for the mainstream compiler path.
2. Keep strict-3 semantics (`RTL3.semantics`) FT-local and bridge it to core RTL directly.
3. Compose end-to-end proof using existing top-level compiler theorem(s) whenever possible; avoid re-proving long pass chains in `driver/Complements.v`.
4. Remove dead compatibility lemmas and imports once the new chain is in place.

## Target theorem shape
For `Hp : transf_c_program_to_rtl p = OK tp`, `Hcheck : RTLcolorcheck.check_program tp = true`, and `Hfaulty : program_behaves (faulty_semantics tp) beh`:

1. `faulty(tp) -> RTL3(tp)` from `RTLtolerant.faulty_backward_simulation`.
2. `RTL3(tp) -> RTL(tp)` from a new generic bridge theorem (no `no_votes` premise).
3. `RTL(tp) -> C(p)` from `Compiler.transf_c_program_to_rtl_correct`.
4. Conclude with `behavior_improves` transitivity.

This removes the old `2 -> 3` agreement step entirely.

## Phase 0: Baseline and dependency map
Files:
1. `driver/Compiler.v`
2. `driver/Complements.v`
3. `backend/RTLagreement.v` (or new `backend/RTL3proof.v`)
4. `common/Events.v` and `backend/Builtins2.v` (only if extra bridge lemmas are needed)

Actions:
1. Confirm current compile failure location in `Complements.v` and preserve as baseline.
2. Identify all current `Novotes` dependencies in pipeline definitions and proof scripts.

Exit criteria:
1. We have a concrete list of lemmas to delete/replace.
2. We have one chosen home for the new `RTL3 -> RTL` bridge theorem.

## Phase 1: Add a generic `RTL3 -> RTL` bridge (no `no_votes`)
Preferred file:
1. `backend/RTLagreement.v` (or `backend/RTL3proof.v` if separation is cleaner)

Actions:
1. Prove call-level bridge lemma: every `external_call3` can be matched by `external_call` with less-defined result and same trace/memory evolution shape needed for RTL step simulation.
2. Prove step simulation from `RTL3.step` to `RTL.step` under a lessdef register relation.
3. Derive a simulation theorem strong enough for behaviors:
   - either `forward_simulation (RTL3.semantics p) (RTL.semantics p)` then convert via `forward_to_backward_simulation`,
   - or directly `backward_simulation (RTL.semantics p) (RTL3.semantics p)`.
4. Export behavior-level corollary:
   - `forall beh3, program_behaves (RTL3.semantics p) beh3 -> exists beh2, program_behaves (RTL.semantics p) beh2 /\ behavior_improves beh2 beh3`.

Notes:
1. Reuse existing 3-to-2 value lemmas (`vote3_lessdef_vote`, known-builtin lessdef lemmas) instead of re-proving vote algebra.
2. Keep this bridge independent of coloring and independent of tolerant simulation internals.

Exit criteria:
1. Bridge theorem compiles and has no `no_votes` hypothesis.
2. Bridge theorem is usable from `driver/Complements.v` with only `p` as parameter.

## Phase 2: Remove `Novotes` pass from `driver/Compiler.v`
Files:
1. `driver/Compiler.v`

Actions:
1. Remove `Require Novotes.` and `Require Novotesproof.` if no longer needed.
2. Remove `@@@ time "Novotes" Novotes.transf_program` from:
   - `transf_rtl_program`
   - `transf_rtl_program_to_rtl`
3. Update pass-match definitions and match/correctness proofs that currently destruct `Novotes.check_program`.
4. Delete commented-out `Novotesproof` pass remnants if they create confusion.

Expected proof simplification:
1. Fewer monadic destruct steps in `transf_*_match` proofs.
2. No `check_program_sound` detours in compiler correctness.

Exit criteria:
1. `driver/Compiler.vo` builds.
2. `transf_c_program_to_rtl_correct` remains unchanged in statement and usable by `Complements.v`.

## Phase 3: Rewrite `transf_c_program_to_rtl_preservation_faulty` minimally
Files:
1. `driver/Complements.v`

Actions:
1. Replace current proof chain with direct 3-step composition:
   - `faulty -> RTL3`
   - `RTL3 -> RTL`
   - `RTL -> C`.
2. Use `Compiler.transf_c_program_to_rtl_correct` directly; avoid hand-rolled decomposition through `p'` unless still needed elsewhere.
3. Remove now-obsolete novotes-dependent lemmas and imports:
   - `transf_c_program_to_rtl'_no_votes`
   - `transf_c_program_to_rtl'_preservation'`
   - `Novotes`/`Novotesproof` imports
   - helper lemmas that exist only to support the old decomposition (`apply_partial_factor` if no longer referenced).
4. Keep only reusable helper lemmas that still serve non-faulty theorems.

Exit criteria:
1. `driver/Complements.vo` builds.
2. The final theorem statement is unchanged, but no longer mentions or depends on `no_votes`.

## Phase 4: Cleanup and validation
Validation commands:
1. `make -j1 backend/RTLagreement.vo`
2. `make -j1 driver/Compiler.vo`
3. `make -j1 backend/RTLtolerant.vo driver/Complements.vo`
4. `make -j1 check-admitted`
5. `make -j1 ccomp` (if extraction surface changed)

Search checks:
1. `rg -n "Novotes|no_votes_weak_agreement'|transf_c_program_to_rtl'_no_votes|VoteSemantics" driver backend common`
2. Confirm `Novotes` no longer appears in active pipeline definitions in `Compiler.v`.

Exit criteria:
1. Faulty preservation theorem compiles with no novotes dependency.
2. Compiler RTL pipeline no longer runs the novotes checker.
3. No admitted proofs introduced.

## Phase 5: Write comprehensive technical report
Output file:
1. `doc/no-novotes-report.md`

Scope:
1. Capture the full refactor rationale and final proof architecture.
2. Document all semantic and pipeline changes with theorem-level traceability.
3. Record validation evidence and residual risks.

Required contents:
1. Executive summary:
   - why `novotes` was removed,
   - what simplified proof shape replaced it,
   - what guarantees remain unchanged.
2. Before/after architecture:
   - old composition (`faulty -> RTL3 -> RTL2 via no_votes -> C` style),
   - new composition (`faulty -> RTL3 -> RTL -> C`),
   - explicit theorem dependency graph.
3. Code and proof deltas:
   - `driver/Compiler.v` pipeline edits,
   - new `RTL3 -> RTL` bridge artifacts,
   - `driver/Complements.v` theorem rewrite,
   - deleted/retired novotes lemmas.
4. Soundness argument:
   - why the new bridge does not require `no_votes`,
   - key lessdef/external-call lemmas used,
   - behavior refinement composition argument.
5. Validation log:
   - commands run,
   - pass/fail outcomes,
   - final green checklist.
6. Residual risks and follow-up work:
   - any non-blocking proof debt,
   - possible cleanup/factoring opportunities.

Exit criteria:
1. Report is complete and checked against the final merged code state.
2. Every nontrivial claim is linked to a concrete theorem/lemma/file location.
3. The report is sufficient for a new contributor to understand and audit the refactor.

## Risks and mitigations
1. Risk: `RTL3 -> RTL` step simulation gets stuck on builtin-call cases.
   Mitigation: prove/strengthen call-level bridge lemmas in `Events` first, then lift to RTL steps.
2. Risk: new bridge proof duplicates `RTLtolerant` internals.
   Mitigation: factor shared lemmas into a lightweight common location and keep tolerant-specific invariants separate.
3. Risk: removing `Novotes` from pipeline breaks existing match proofs in `Compiler.v`.
   Mitigation: rewrite proofs by mirroring the new monadic structure exactly and compile incrementally.

## Definition of done
1. `driver/Compiler.v` has no active `Novotes.transf_program` call.
2. `transf_c_program_to_rtl_preservation_faulty` composes without `no_votes`.
3. The final composition is strictly simpler than current (`faulty -> RTL3 -> RTL -> C`) and compiles end-to-end.
4. A comprehensive technical report is produced at `doc/no-novotes-report.md`.
