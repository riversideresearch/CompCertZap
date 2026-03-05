# Plan: Direct-Cut Removal of Vote Parameterization

## Objective
Refactor the fork so core CompCert semantics/proofs are fully unparameterized (no `vote_type`, no `VoteSemantics`), while preserving fault-tolerance results by isolating 3-vote behavior to fault-specific modules only.

## Hard constraints
1. No compatibility wrappers or bridge shims that exist only for migration.
2. No temporary architecture that must later be deleted.
3. Mainline semantics/proofs must not mention `Two`.
4. 3-vote semantics may appear only in fault-tolerance-local files.

## End-state architecture
1. Core builtin and external-call semantics are single, canonical definitions (current 2-vote behavior, but unnamed as `Two`).
2. `backend/RTL.v` and upstream-facing proofs are unparameterized.
3. Fault tolerance keeps an explicit strict-3 semantics path in fork-local files only (e.g. `RTL3` / tolerant proof helpers).
4. `driver/Complements.v` composes proofs without global typeclass parameter plumbing.

## Phase 0: Clean baseline (done)
1. Reset working tree to `HEAD`.
2. Remove prior migration artifacts (`RTL2/RTL3/bridge` temp files and phase logs).
3. Keep user side-experiment untracked files untouched.

Exit criteria:
1. `git status --short` shows no tracked modifications.
2. Only unrelated untracked user files remain.

## Phase 1: Remove parameterization at the source

Files:
1. `backend/Builtins2.v`
2. `common/Builtins.v`
3. `common/Events.v`
3. Any direct typeclass consumers exposed by these APIs.

Actions:
1. Delete `vote_type`, `vote_eqb`, `vote_type_sem`, `VoteSemantics` class and instances from core API surface.
2. Replace with concrete core vote semantics definitions.
3. Keep explicit 3-vote semantic operators as separate definitions for FT use (not via global typeclass).
4. Make `builtin_function_sem`, `known_builtin_sem`, and `external_call` non-polymorphic.

Exit criteria:
1. No `VoteSemantics` references in `common/`.
2. `common/Builtins.vo` and `common/Events.vo` build.

## Phase 2: Unparameterize all mainstream semantics/proofs

Scope:
1. `cfrontend/`, `backend/`, `x86/`, `driver/` files that currently use `Section VOTE` / `Context {VT ...}`.

Actions:
1. Remove section/context parameterization.
2. Update theorem statements and proof scripts to use concrete semantics directly.
3. Prefer minimal local proof edits; no stopgap aliases.

Build cadence:
1. Directory-local checkpoints (small batches).
2. Immediate compile after each batch to constrain breakage radius.

Exit criteria:
1. Global grep has no `Section VOTE`, `vote_type`, or `VoteSemantics` in mainstream files.
2. Standard preservation chain builds to RTL/Asm as before.

## Phase 3: Re-introduce FT-only strict-3 path (local)

Files:
1. FT-local modules only: `backend/RTLfault.v`, `backend/RTLtolerant.v`, `backend/RTLtmr*.v`, optional `backend/RTL3.v`.

Actions:
1. Define strict-3 semantics explicitly and locally (no global parameterization).
2. Provide only the lemmas required by tolerant simulation.
3. Keep all 3-vote machinery isolated from upstream-facing semantics.

Exit criteria:
1. `backend/RTLtolerant.vo` builds against unparameterized core.
2. 3-vote references are confined to FT-local files.

## Phase 4: Recompose top-level theorem and finalize

Files:
1. `driver/Complements.v`
2. Any FT theorem dependency files.

Actions:
1. Rewire theorem composition to new unparameterized core + FT-local strict-3 path.
2. Ensure theorem meaning remains unchanged.

Validation:
1. `make backend/RTLtolerant.vo driver/Complements.vo`
2. `make check-admitted`
3. `make ccomp` (if extraction surface changed)

Exit criteria:
1. Main FT theorem compiles.
2. No admitted proofs.
3. Build pipeline remains functional.

## Execution order
1. Core APIs first (`Builtins2`/`common`).
2. Mainstream de-parameterization sweep.
3. FT-local strict-3 reintegration.
4. Top-level theorem recomposition.

## Definition of done
1. Core compiler/proofs are fully unparameterized and never mention `Two`.
2. No migration-only wrappers remain.
3. FT theorem and build checks pass.
