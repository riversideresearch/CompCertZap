# Plan: Remove Global Two/Three Vote Parameterization

## Goal
Eliminate global `vote_type`/`VoteSemantics` parameterization from CompCert IR semantics and proofs, while preserving the current fault-tolerance theorem structure.

Primary outcome:
1. Upstream-facing CompCert files use a single default semantics (2-vote behavior).
2. 3-vote semantics exist only in a small RTL-local fault-tolerance layer.
3. Rebase cost is reduced from many cross-cutting edits to a small set of fork-owned files.

## Non-goals
1. No change to TMR/DMR algorithm behavior.
2. No immediate asm-level tolerance proof migration in this plan.
3. No checker completeness improvements (soundness only, as today).

## Current pain to remove
Global parameterization currently touches many files across `common/`, `cfrontend/`, `backend/`, `x86/`, and `driver/`. This creates high merge conflict risk whenever upstream updates semantics/proofs.

## Target architecture
1. Keep canonical upstream-style semantics everywhere (`Two` behavior only).
2. Add a dedicated RTL module providing strict-3-vote semantics (or a semantics variant) used only for fault-tolerance proofs.
3. Prove a bridge theorem on no-vote programs:
   - `Beh(RTL2 p) = Beh(RTL3 p)` (or two refinement directions).
4. Recompose `Complements.v` proof chain using the bridge at the pre-TMR no-votes point.

## Phase 0: Baseline and safety net

### Actions
1. Record baseline build status:
   - `make backend/RTLtolerant.vo driver/Complements.vo`
2. Snapshot current theorem statements used in fault-tolerance composition.
3. Save a grep inventory of `Section VOTE`/`VoteSemantics` locations for tracking deletions.

### Exit criteria
1. Baseline build and theorem signatures are captured.
2. A checklist exists for files expected to be de-parameterized.

## Phase 1: Introduce RTL-local 3-vote semantics module

### Files
1. New: `backend/RTL3.v` (name can vary; keep fork-local)
2. Possibly small helpers in `backend/Builtins2.v` for explicit vote semantic selection.

### Actions
1. Define an RTL semantics variant where only vote builtin interpretation differs (strict-3-vote).
2. Keep this module independent from global language parameterization.
3. Reuse as much of existing `RTL.v` machinery as possible to minimize proof duplication.

### Proof obligations
1. Determinacy/basic semantic lemmas needed by later simulations.
2. Compatibility lemmas for external calls/builtins used in tolerant proofs.

### Exit criteria
1. `backend/RTL3.vo` builds.
2. Existing tolerant lemmas can import `RTL3` without global typeclass context.

## Phase 2: Prove no-votes bridge between RTL2 and RTL3

### Files
1. New: `backend/RTL23Bridge.v` (or integrate into `backend/RTLagreement.v`)
2. Existing: `backend/Novotes.v`, `backend/Novotesproof.v`

### Actions
1. State bridge theorem under no-votes:
   - behavior equivalence or mutual refinement between `RTL.semantics` (2-vote) and `RTL3.semantics`.
2. Prove step-level coincidence:
   - if current instruction is not vote builtin, `step2 <-> step3`.
3. Lift to whole-program behaviors.

### Key lemmas
1. Reachable states execute only instructions permitted by `no_votes`.
2. Vote-builtin case is unreachable under no-votes.
3. Therefore builtin semantic divergence is observationally irrelevant.

### Exit criteria
1. A theorem consumable by `driver/Complements.v` exists and builds.

## Phase 3: Rework fault-tolerance composition to use local bridge

### Files
1. `driver/Complements.v`
2. `backend/RTLagreement.v` (if used as theorem home)
3. `backend/RTLtolerant.v` (imports/signatures only as needed)

### Actions
1. Replace dependence on globally-parameterized semantics with explicit:
   - `RTL2` (canonical),
   - `RTL3` (local variant for tolerant simulation).
2. Keep proof decomposition:
   - standard C->RTL preservation (unchanged upstream path),
   - no-votes soundness,
   - bridge `RTL2 >= RTL3` at no-votes point,
   - TMR correctness and faulty backward simulation (`RTL3 nonfaulty >= RTL2 faulty`).

### Exit criteria
1. Fault-tolerance top theorem is restored with equivalent meaning.
2. No global `Section VOTE` dependency is required in `driver/Complements.v`.

## Phase 4: Remove global vote parameterization from upstream-facing files

### Scope
De-parameterize files in:
1. `common/`
2. `cfrontend/`
3. `backend/` (except fault-tolerance-local modules that truly need both semantics)
4. `x86/`/other backends
5. `driver/`

### Actions
1. Remove `Section VOTE` / `Context {VT ...}` wrappers where unnecessary.
2. Replace polymorphic uses with canonical 2-vote semantics.
3. Keep `Builtins2` vote definitions, but avoid requiring typeclass parameters outside local fault modules.

### Strategy
1. Do this in small batches (directory-by-directory) with compile checkpoints.
2. Prefer minimal textual edits to ease future rebases.

### Exit criteria
1. Global grep for `Section VOTE` and `VoteSemantics` is reduced to fault-local files only.
2. Full proof build succeeds.

## Phase 5: OCaml/extraction/driver cleanup

### Files
1. `extraction/extraction.v`
2. `driver/Driver.ml`
3. Any extracted OCaml impacted by removed parameters

### Actions
1. Remove no-longer-needed extracted polymorphism around vote semantics.
2. Ensure checker and pipeline entry points retain expected signatures.

### Exit criteria
1. `make extraction` and `make ccomp` succeed.
2. `./ccomp ... -tmr` path still executes checker and compilation flow.

## Suggested implementation order (low-risk)
1. Add `RTL3` module first.
2. Add/prove `RTL2 <-> RTL3` no-votes bridge.
3. Rewire `Complements.v` around the bridge.
4. Only then de-parameterize broad upstream-facing files.
5. Finish with extraction/driver cleanup.

## Testing and validation checkpoints
1. Proof checks:
   - `make backend/RTL3.vo`
   - `make backend/RTL23Bridge.vo`
   - `make backend/RTLtolerant.vo`
   - `make driver/Complements.vo`
   - `make check-admitted`
2. Build checks:
   - `make ccomp`
3. Smoke tests:
   - compile representative C files with and without `-tmr`
   - ensure no new pass-order regressions.

## Risk register

### Risk 1: Bridge proof needs stronger no-votes invariant than current checker provides
Mitigation:
1. Strengthen `Novotesproof` with reachability-preservation lemmas.
2. Keep theorem statements behavioral (refinement) to avoid over-constraining state invariants.

### Risk 2: Hidden dependency on polymorphic semantics in older proofs
Mitigation:
1. Keep a thin compatibility layer temporarily (notation wrappers) while migrating.
2. Remove wrappers only after full build passes.

### Risk 3: Large edit set causes temporary instability
Mitigation:
1. Land work as a series of small commits:
   - `RTL3`,
   - bridge,
   - composition,
   - de-parameterization batches,
   - extraction cleanup.

## Deliverables
1. New RTL-local 3-vote semantics module.
2. Proven no-votes bridge theorem (`RTL2` vs `RTL3`).
3. Restored/updated fault-tolerance theorem using the bridge.
4. Global removal of unnecessary vote typeclass parameterization.
5. Passing proof/build checks listed above.

