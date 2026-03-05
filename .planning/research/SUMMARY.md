# Project Research Summary

**Project:** CompCertZAP Liveness-Bounded Fault Tolerance Proof
**Domain:** Coq formal verification — CompCert simulation proof refactoring
**Researched:** 2026-03-04
**Confidence:** HIGH (all findings from direct codebase inspection)

## Executive Summary

The core problem is a fundamental mismatch between CompCert's `Liveness.transfer` function and what the `RTLtolerant.v` backward simulation proof requires. Standard liveness conditionally omits `Iop`/`Iload` instruction arguments when the destination register is dead — correct for dead code elimination, but wrong for a simulation proof that must evaluate every instruction on both (non-faulty and faulty) sides. The fix is a new `ProofLiveness.v` module that is identical to `Liveness.v` except those two cases unconditionally include args. This is a well-understood pattern in CompCert: four existing backward analyses (`Liveness`, `Deadcode`, `Allocation`, `Regalloc`) all follow the identical Kildall instantiation recipe.

The change requires touching five files in a strict dependency order: create `ProofLiveness.v`, then swap the analysis reference in `RTLcolor.v`, then simultaneously update `RTLcolorcheck.v` (completing the `Admitted` checker soundness proof) and `RTLtolerant.v` (rebuilding the simulation proof cases), and finally rebuild `Complements.v` with no source changes. The two hardest work items are: (1) proving `check_col_instr_sound` fresh from scratch — the commented-out old proof uses a different iteration API and must not be uncommented, and (2) updating the ~2600-line `RTLtolerant.v` proof, which needs new `match_rs_weaken` and `In_transfer` helper lemmas before tackling individual instruction cases.

The key risks are coordination failures: `wc_function` in `RTLcolor.v` and `LIVE` in `RTLtolerant.match_states` must reference the same analysis simultaneously, or the proof will have two unrelated live maps in scope with no connection. The secondary risk is attempting to patch the old `check_col_instr_sound` proof rather than rewriting it — the structural mismatch between `PTree_Properties.for_all` (old) and `Regset.for_all` (new) makes incremental patching slower than a clean rewrite.

## Key Findings

### Recommended Stack

`ProofLiveness.v` should be a near-copy of `Liveness.v` with only two cases changed. Use `Backward_Dataflow_Solver(RegsetLat)(NodeSetBackward)` — the same instantiation as `Liveness.v`. Use the efficient `DS.fixpoint` (not `fixpoint_allnodes`); the side condition `transf bot = bot` is trivially satisfied because the outer match on `fn_code!pc` returns `Regset.empty` when `None`. Do not add a new lattice, do not parameterize by `vote_type`, do not axiomatize the analysis at extraction time.

**Core technologies:**
- `Backward_Dataflow_Solver(RegsetLat)(NodeSetBackward)`: backward fixpoint solver — same instantiation used by all four existing CompCert backward analyses
- `RegsetLat` (`LFSet(Regset)`): semi-lattice over register sets — already defined, no new lattice needed
- `DS.fixpoint_solution`: the one-line proof of `analyze_solution` — identical to `Liveness.analyze_solution`
- `Regset.for_all` / `Regset.For_all`: reflection bridge needed for `check_col_instr_sound` — check for `for_all_spec` or write a custom bridge lemma

### Expected Features (Proof Obligations)

**Must have (table stakes — proof fails without these):**
- `ProofLiveness.transfer` with conservative `Iop`/`Iload` cases — this is the root cause of the current proof breakage
- `analyze_solution` theorem — needed by every instruction case in `step_simulation` to transition `match_rs` from `live!!pc` to `live!!succ`
- `reg_list_live_in` membership lemma — building block for all per-instruction `Regset.In` proofs
- Per-instruction `In_transfer` lemmas (11 instruction forms) — needed at every proof case
- `check_col_instr_sound` proof completed (currently `Admitted`) — blocks the entire theorem chain
- Atomic swap of `Liveness.analyze` to `ProofLiveness.analyze` in both `RTLcolor.v` and `RTLtolerant.v` — must happen together

**Should have (proof engineering quality):**
- `match_rs_weaken` lemma: `Regset.Subset s1 s2 -> match_rs s2 col b rs1 rs2 -> match_rs s1 col b rs1 rs2` — makes successor transitions one-liners
- `match_rs_from_all` helper for `init_regs` at function entry — needed for the `exec_function_internal` case
- Updated `maybe_zap_preserves_match_states` with liveness awareness — must be fixed before main simulation lemmas

**Defer (v2+):**
- `solve_match_rs` unified tactic (D1) — proof length reduction, not blocking
- Separate `wc_consistency` from `wc_color` judgement (D4) — high refactoring cost, unclear benefit now
- Weaker `match_rs` for non-faulty case (D5) — simplification pass after proof compiles

### Architecture Approach

Five files in a strict DAG: `ProofLiveness.v` (new, standalone) feeds `RTLcolor.v` (1-line swap), which feeds both `RTLcolorcheck.v` (swap + complete Admitted proof) and `RTLtolerant.v` (swap + rebuild simulation) in parallel, which both feed `Complements.v` (rebuild only, no source changes). `Complements.v` requires no changes because `wc_program` and `check_program_sound` preserve their external type signatures regardless of which analysis they internally use.

**Major components:**
1. `backend/ProofLiveness.v` (NEW, ~100 lines) — conservative liveness transfer + Kildall solver + `analyze_solution` + membership helpers
2. `backend/RTLcolor.v` (trivial edit) — swap analysis reference in `wc_function` constructor
3. `backend/RTLcolorcheck.v` (medium effort) — swap analysis + prove `check_col_instr_sound` fresh (14 instruction cases)
4. `backend/RTLtolerant.v` (high effort, ~2600 lines) — swap analysis + add helper lemmas + rebuild proof cases
5. `driver/Complements.v` (rebuild only) — no source changes; verify composed signatures still type-check

### Critical Pitfalls

1. **Liveness source desynchronization (Pitfall 5)** — `wc_function` (`RTLcolor.v`) and `LIVE` in `match_states` (`RTLtolerant.v`) must both reference `ProofLiveness.analyze`. Change them atomically in a single edit session; grep for remaining `Liveness.analyze` occurrences before compiling.

2. **Do not uncomment old `check_col_instr_sound` proof (Pitfall 3)** — the old proof used `PTree_Properties.for_all_correct`; the current spec uses `Regset.For_all`. Structural mismatch causes 15+ type errors. Write fresh, one instruction case at a time, starting with `Inop`.

3. **Build helper lemmas before instruction cases (Pitfall 1, 7)** — prove `match_rs_weaken` and all `In_transfer` lemmas first. Then fix `step_simulation` before `faulty_progress` (the latter is weaker and gives false confidence).

4. **Fix type errors before proof content (Pitfall 4)** — `forall2_lessdef_match_rs_init_regs` and `maybe_zap_preserves_match_states` have arity mismatches from the `live` parameter addition. Compile the file first to surface all type errors; fix them before touching any proof scripts.

5. **`Regset.for_all` reflection bridge (Pitfall 10)** — the checker uses boolean `Regset.for_all`; the spec uses propositional `Regset.For_all`. Locate `Regset.for_all_spec` or prove a custom bridge `forall f s, Regset.for_all f s = true -> Regset.For_all (fun r => f r = true) s` as the first step of `check_col_instr_sound`.

## Implications for Roadmap

### Phase 1: ProofLiveness.v (standalone foundation)

**Rationale:** Everything else depends on this file. It has no dependencies on files that need changing and can be developed and compiled in isolation. Getting it right first validates the approach before touching any existing proofs.
**Delivers:** `ProofLiveness.analyze`, `analyze_solution`, `reg_list_live_in`, all `In_transfer` lemmas for all 11 instruction forms
**Addresses:** F1, F2, F3, F8 (table-stakes features)
**Avoids:** Pitfall 2 (transfer too weak) — test each instruction case manually before proceeding
**Build:** `make backend/ProofLiveness.vo`

### Phase 2: RTLcolor.v + RTLcolorcheck.v (checker soundness)

**Rationale:** `RTLcolor.v` is a 1-line change and enables Phase 3+4. `RTLcolorcheck.v` is independent of `RTLtolerant.v` and the Admitted proof blocks the entire theorem chain. These two files share the same analysis reference and must be changed together.
**Delivers:** `check_program_sound` backed by a real proof (no Admitteds in this part of the chain)
**Addresses:** F5 (switch wc_function), F6 (complete check_col_instr_sound)
**Avoids:** Pitfall 3 (do not uncomment old proof), Pitfall 5 (atomic analysis swap), Pitfall 10 (for_all reflection bridge)
**Build:** `make backend/RTLcolor.vo && make backend/RTLcolorcheck.vo`

### Phase 3: RTLtolerant.v (simulation proof rebuild)

**Rationale:** Longest and highest-risk phase. Can run in parallel with Phase 2 after Phase 1 completes. Must follow a strict internal order: fix type errors first, then helper lemmas, then `step_simulation` cases, then `faulty_progress`.
**Delivers:** `faulty_backward_simulation` with no Admitteds; all `Regset.In` obligations discharged via ProofLiveness
**Addresses:** F4 (match_rs transition helpers), all per-instruction proof cases
**Avoids:** Pitfall 1 (successor liveness transition), Pitfall 4 (arity mismatches), Pitfall 7 (Inop deceptively simple), Pitfall 8 (maybe_zap), Pitfall 13 (fix step_simulation before faulty_progress)
**Internal order:** (a) compile-pass: fix all type errors; (b) `match_rs_weaken` + `match_rs_from_all` + update `maybe_zap_preserves_match_states`; (c) `step_simulation` instruction cases; (d) `faulty_progress` cases
**Build:** `make backend/RTLtolerant.vo`

### Phase 4: Complements.v + Validation

**Rationale:** No source changes expected; rebuild verifies composed types still hold. Validation confirms no Admitteds remain and compiler binary still works.
**Delivers:** Top-level `transf_c_program_to_rtl_preservation_faulty` theorem fully grounded; `make check-admitted` clean; `ccomp -tmr` binary functional
**Build:** `make driver/Complements.vo && make check-admitted && make ccomp`

### Phase Ordering Rationale

- Phase 1 before all others: strict Coq dependency; `ProofLiveness.vo` must exist before any file that imports it
- Phase 2 and Phase 3 parallelizable: `RTLcolorcheck.v` and `RTLtolerant.v` depend on `RTLcolor.v` but not on each other
- `Complements.v` strictly last: transitively depends on all other `.vo` files
- Internal Phase 3 ordering (type errors before proof content) avoids wasted proof work on code that doesn't compile

### Research Flags

Phases with well-documented patterns (skip deeper research):
- **Phase 1:** Standard Kildall instantiation; four existing examples in codebase to copy from
- **Phase 4:** Mechanical rebuild with no source changes

Phases that may encounter unknowns during execution:
- **Phase 2 (RTLcolorcheck):** `Regset.for_all_spec` availability and exact `Proper` instance requirements are not fully known; may need a custom reflection lemma
- **Phase 3 (RTLtolerant):** The `Ibuiltin` vote cases (F3 item 8, 12) have sub-cases that may have different proof structure; the ~40 repeated `match_rs` discharge patterns may benefit from a tactic once the first few cases are proven

## Confidence Assessment

| Area | Confidence | Notes |
|------|------------|-------|
| Stack | HIGH | Four existing Kildall instantiations in codebase; pattern is mechanical |
| Features | HIGH | Direct inspection of `TODO` comments and proof obligations in `RTLtolerant.v` |
| Architecture | HIGH | Dependency graph verified by reading actual `Require Import` declarations |
| Pitfalls | HIGH | Most pitfalls observed from current broken state of the branch |

**Overall confidence:** HIGH

### Gaps to Address

- `Regset.for_all_spec` exact signature: check `lib/Lattice.v` and FSetAVL interface before writing `check_col_instr_sound`; may need a one-line custom bridge
- `Ibuiltin` vote case structure: lines 1492-1542 and 2078-2100 in `RTLtolerant.v` handle vote builtins; these may have a different `In_transfer` pattern than regular builtins
- Phase 3 compile time: `RTLtolerant.v` is already the longest-compiling file; adding lemmas may push it further; no mitigation needed but worth tracking

## Sources

### Primary (HIGH confidence — direct codebase inspection)

- `backend/RTLtolerant.v` — simulation proof, match relations, all proof obligations (lines 1-2612)
- `backend/RTLcolor.v` — well-coloredness spec, `wc_function` constructor (lines 101-247)
- `backend/RTLcolorcheck.v` — Boolean checker, `Admitted` soundness lemma (lines 1-523)
- `backend/Liveness.v` — reference instantiation, transfer function, `analyze_solution` (lines 68-127)
- `backend/Kildall.v` — `Backward_Dataflow_Solver`, `fixpoint_solution`, `NodeSetBackward`
- `backend/Deadcode.v` — second reference instantiation (different lattice, same solver pattern)
- `driver/Complements.v` — top-level theorem composition (lines 546-570)
- `plans/liveness-invariant-plan.md` — existing implementation plan

### Secondary (MEDIUM confidence)

- [CompCert backend correctness proofs](https://xavierleroy.org/publi/compcert-backend.pdf) — general simulation proof structure
- [Formally Verified Loop-Invariant Code Motion](https://hal.science/hal-03628646/document) — CompCert pass proof patterns

---
*Research completed: 2026-03-04*
*Ready for roadmap: yes*
