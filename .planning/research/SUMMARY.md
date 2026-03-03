# Project Research Summary

**Project:** CompCert Fault-Tolerance Proof Cleanup
**Domain:** Large Coq proof base refactoring — compiler verification
**Researched:** 2026-03-03
**Confidence:** HIGH

## Executive Summary

This project cleans up approximately 11,000 lines of Coq across the fault-tolerance extension of CompCert (DMR/TMR + color checker). The core problems are structural duplication and accumulated technical debt: 57 of 70 lemma names in `RTLdmrproof.v` appear identically in `RTLtmrproof.v`, both spec files share 32 of 44 lemma names, 6 Ltac tactics are copy-pasted verbatim into both spec files, and commented-out abandoned proof blocks consume 244 lines in `RTLtolerant.v` and 133 of 208 lines in `RTLagreement.v`. The cleanup does not change any theorem statements visible to the outside pipeline — the goal is to make the proof base readable and maintainable without weakening any verified property.

The recommended approach is a strictly dependency-ordered sequence of eight stages: (1) delete untracked backup/dead files, (2) introduce two new shared modules (`RTLreplicateSpecCommon.v` and `RTLreplicateProofCommon.v`) to hold the genuinely identical content, (3) refactor `replication_map_wf_aux` in both spec files via a relational intermediate spec, (4) de-duplicate within-file repeated proof patterns, (5) unify the `no_votes` policy across `CSEproof.v`, `RTLagreement.v`, and `Complements.v`, and (6) finish with a comment and tactic hygiene pass. Each stage must be gated by targeted `make <file>.vo` builds and confirmed with `make check-admitted` before proceeding. Full `make proof -j$(nproc)` runs at phase boundaries.

The critical risk is cross-cutting signature changes that silently weaken the top-level preservation theorem. The `no_votes` policy alignment (Stage 5/Phase 4) is the highest-risk single change because it touches `CSEproof.v`, `RTLagreement.v`, and `driver/Complements.v` simultaneously and must be decided as an atomic policy choice (Option A: explicit hypothesis, or Option B: checker soundness discharges it) before any code is written. A secondary risk is the `RTLreplicateProofCommon.v` extraction: lemmas moved out of `Section VOTE` acquire explicit `VT`/`vsem` parameters that break all existing call sites if not updated in the same commit.

## Key Findings

### Recommended Stack

The full build toolchain (Coq 8.20.0, OCaml 4.14.2, `coqc`/`coqdep` via Makefile) is already in place and should not be changed. The workflow pattern is: `make backend/<file>.vo` for fast per-file verification after each change, and `make proof -j$(nproc)` at phase boundaries only. Full proof builds take 20+ minutes; targeted file builds take seconds.

Two additional analysis tools are worth installing. `coq-dpdgraph` (`opam install coq-dpdgraph`) provides semantic dead-definition detection — directly useful for confirming `AdvSem.v` and `Replicate3proof.v` have no surviving callers. `ripgrep` (`rg`) is already present and sufficient for the simpler "grep before deleting" workflow. `coq-tools minimize-requires.py` can clean up import lists after the shared modules are introduced. Proof General (Emacs) is the recommended interactive environment; coq-lsp/VSCode is a viable alternative with faster per-sentence feedback. Ltac2 should NOT be introduced — the existing Ltac1 proofs work and migration adds risk without cleanup value.

**Core technologies:**
- `coqc` 8.20.0: proof compilation — already in use, no change
- `make backend/<file>.vo`: per-file targeted rebuild — primary verification workflow
- `make check-admitted` + `grep -rn "^\s*Admitted"`: admitted proof detection — necessary after every phase
- `coqwc`: spec/proof/comment line counts — baseline measurement and phase-end progress tracking
- `coq-dpdgraph`: semantic dead-definition finder — install once, use for backup file deletion confidence
- `ripgrep` (`rg`): call-site enumeration before any lemma removal or rename

### Expected Features

The cleanup deliverables are organized as table stakes (the proof base must have these to be considered clean) and differentiators (improvements that substantially raise long-term maintainability).

**Must have (table stakes):**
- Delete all 13 backup and dead files (6 `.v` backups, 7 `.ml` backups, `AdvSem.v`, `Replicate3proof.v`) — none are in the build, all are untracked
- Remove large commented-out abandoned proof blocks from `RTLtolerant.v`, `Complements.v`, `RTLagreement.v` — design rationale comments stay, dead proof drafts go
- Resolve all 8 files with active TODO markers — each TODO requires a concrete resolution action
- Maintain build integrity at every commit — if it does not compile, the proof does not exist
- Establish a baseline health record before any refactoring begins

**Should have (differentiators):**
- `RTLreplicateSpecCommon.v`: centralize 6 shared Ltac tactics and 2 type definitions from both spec files
- `RTLreplicateProofCommon.v`: centralize globally-stated lemmas verbatim in both proof files
- Relational spec for `replication_map_wf_aux`: split monolithic "algorithm + invariant" proof into (1) relational inductive, (2) implementation => relational spec, (3) relational spec => `rm_wf`
- De-duplicate `no_votes_external_call` in `Novotesproof.v` (8 near-identical cases to 1 helper + 1 driver)
- Refactor four-type-case duplication in `maj_voteR_step` (RTLtmrproof) and `external_call_vote_lessdef` (RTLtolerant)
- Remove deprecated `external_call_Three_Two` once its 3 call sites are migrated to `external_call_Three_Two'`
- Break `check_col_instr_sound` (~269 lines, one case per instruction) into per-instruction lemmas
- Unify `no_votes` policy across `CSEproof.v`, `RTLagreement.v`, `Complements.v` as one atomic decision

**Defer (later milestones):**
- RTLtolerant.v file split into separate focused files — high complexity, moderate ROI relative to other changes
- Tactic and naming convention alignment between DMR/TMR (purely cosmetic, do last)
- Build time optimization — explicitly out of scope per PROJECT.md

### Architecture Approach

The fault-tolerance extension is structured as a 7-layer dependency stack from CompCert core (Layer 0) up to pipeline integration in `driver/Complements.v` (Layer 7). The proof files (Layer 6) are the heaviest and most duplicated. The proposed architecture adds two new shared modules at Layers 2.5 and 3.5 that contain the genuinely identical content; the `rm_wf` family and `match_regsets` definitions remain parallel-but-separate because DMR uses `PMap.t reg` while TMR uses `PMap.t (reg * reg)` — a structural difference that prevents direct unification without a typeclass or functor (both of which are anti-patterns for this codebase).

**Major components after reorganization:**
1. `RTLreplicateSpecCommon.v` (NEW, Layer 2.5) — shared Ltac tactics and type-agnostic definitions for both spec files; no dependency on RTLdmr or RTLtmr
2. `RTLreplicateProofCommon.v` (NEW, Layer 3.5) — globally-stated boilerplate lemmas verbatim in both proof files; does not reference `match_prog`, `transf_fundef`, or `match_regsets`
3. `RTLdmrspec.v` / `RTLtmrspec.v` (REFACTORED, Layer 3) — each gains a relational `replication_map_rel` inductive and two consequence lemmas replacing the monolithic `replication_map_wf_aux`
4. `RTLdmrproof.v` / `RTLtmrproof.v` (REFACTORED, Layer 6) — import common module; section-local match relations remain in their own files
5. `RTLagreement.v` (CLEANED) — dead comment mass removed; `no_votes` policy decided and documented
6. `RTLtolerant.v` (REFACTORED, Layer 6) — deprecated lemma removed; four-case duplication collapsed; comment blocks removed

### Critical Pitfalls

1. **Removing a lemma with active call sites** — `external_call_Three_Two` has 3 active call sites in `RTLtolerant.v` (lines 1706, 1766, 1856); deleting it without migrating them breaks the build immediately. Always run `rg '<lemma_name>'` before any deletion; migrate all call sites in the same commit.

2. **Moving lemmas out of `Section VOTE` without updating call sites** — any lemma moved from inside `Section VOTE` to a global-scope shared file gains explicit `{VT: vote_type} {vsem: VoteSemantics VT}` parameters. All `apply`/`eapply` call sites in `RTLtmrproof.v` and `RTLdmrproof.v` then see a type mismatch. Run `Check <lemma>.` in the new file after moving; update every call site in the same commit.

3. **Creating new files without adding them to the Makefile `BACKEND` variable** — `_CoqProject` is auto-generated; new `.v` files not in the Makefile's `BACKEND` list at line 166 silently compile in isolation but fail when imported by other files. Add the filename to `BACKEND` in the same commit that creates the file; verify with `make backend/<newfile>.vo`.

4. **Changing the `no_votes` theorem signature without an atomic decision** — `CSEproof.v`, `RTLagreement.v`, and `Complements.v` each carry conflicting design notes about `no_votes` handling. Patching them in separate commits without a prior policy decision creates a hybrid broken state. Decide Option A or Option B before any Phase 4 code changes; implement all three files in one commit.

5. **`make check-admitted` giving false confidence** — `check-admitted` is a grep heuristic that matches the string "Admitted" inside comments too. Supplement every phase-end check with `grep -rn "^\s*Admitted" backend/ driver/` to find only active (non-commented) admitted proofs.

## Implications for Roadmap

Based on the combined dependency structure from ARCHITECTURE.md, the feature ordering from FEATURES.md, and phase warnings from PITFALLS.md, the following 5-phase structure is recommended.

### Phase 0: Baseline and File System Cleanup

**Rationale:** No refactoring should begin without a clean file tree and a known-good health record. Backup files pollute `rg` results used in all subsequent phases. This phase has zero proof risk.

**Delivers:** Clean working directory; `make check-admitted` baseline; confirmed zero Admitted proofs; deleted untracked backups and dead stubs.

**Addresses:** Table-stakes features: delete all backup/dead files, establish baseline health record.

**Avoids:** Pitfall 8 (deleting backups containing undocumented ideas — skim each before deletion); Pitfall 5 (false `check-admitted` confidence — establish true baseline).

**Specific tasks:**
- Skim `DMRproof_backup.v`, `DMRproof_backup2.v`, `RTLfault_backup.v`, `RTLAgreement_backup.v`, `backup_Compiler.v` for any undocumented proof ideas; extract useful comments to active files
- `git rm` all 13 backup and dead files
- Delete `AdvSem.v` and `Replicate3proof.v` after `rg 'AdvSem\|Replicate3'` confirms zero references
- Run `make check-admitted` and `coqwc` on all 8 primary target files; record results

### Phase 1: Shared Module Introduction (Move-Only)

**Rationale:** The shared module files must exist before any de-duplication can proceed in Phase 2. This phase contains only verbatim moves — no proof changes, no theorem changes — which means zero semantic risk. Move-only commits are the safest class of Coq refactoring.

**Delivers:** `RTLreplicateSpecCommon.v` and `RTLreplicateProofCommon.v` compiling and importable; both spec files and both proof files still pass targeted builds.

**Addresses:** Centralize shared DMR/TMR tactics; centralize globally-stated boilerplate lemmas.

**Avoids:** Pitfall 2 (new files not in Makefile — add to `BACKEND` in same commit); Pitfall 3 (section variable leakage — only move lemmas that are already at global scope or have fully explicit arguments); Pitfall 6 (name collision — only move lemmas with identical types, do not merge arity-differing rm_wf family).

**Specific tasks:**
- Create `RTLreplicateSpecCommon.v` with 6 shared Ltac tactics, `comp_of_typ`, `is_actual_type`; add to Makefile BACKEND before RTLdmr.v
- Add `Require Import RTLreplicateSpecCommon` to both spec files; remove duplicated content
- Create `RTLreplicateProofCommon.v` with globally-scoped boilerplate lemmas; add to Makefile BACKEND after RTLtmrspec.v
- Add `Require Import RTLreplicateProofCommon` to both proof files; remove duplicated content
- Verify: `make backend/RTLdmrspec.vo backend/RTLtmrspec.vo backend/RTLdmrproof.vo backend/RTLtmrproof.vo`

### Phase 2: Spec Relational Decomposition

**Rationale:** The `replication_map_wf_aux` monolithic proof in both spec files is the acknowledged worst piece of the proof base. Fixing it before Phase 3 proof de-duplication means the de-duplicated proofs can reference the cleaner relational spec, not the messy monolith. The key constraint from FEATURES.md is explicit: Phase 3 (spec) must precede Phase 2 (proof de-dup) — hence this phase runs second in the roadmap.

**Delivers:** `replication_map_wf_aux` in both spec files replaced by a relational `replication_map_rel` inductive plus two clean consequence lemmas; both spec files still export the same `rm_wf` interface.

**Addresses:** Relational spec for replication-map construction (high-value differentiator).

**Avoids:** Pitfall 3 (section context changes — the relational spec additions are inside the existing file structure; no cross-file moves needed here).

**Specific tasks:**
- DMR spec first: add `replication_map_rel` inductive; prove `foldM_satisfies_rel` and `rel_implies_rm_wf`; replace `replication_map_wf_aux` with composition
- Verify: `make backend/RTLdmrspec.vo backend/RTLdmrproof.vo`
- Port to TMR spec (same pattern, different arity)
- Verify: `make backend/RTLtmrspec.vo backend/RTLtmrproof.vo`

### Phase 3: Within-File Proof De-duplication

**Rationale:** With shared modules in place (Phase 1) and cleaner specs (Phase 2), within-file proof repetition can be safely collapsed. Each change is contained within one file — no cross-file signature changes — keeping risk low.

**Delivers:** `maj_voteR_step` four-case duplication collapsed in `RTLtmrproof.v`; `external_call_vote_lessdef` four-case duplication collapsed in `RTLtolerant.v`; `no_votes_external_call` 8-repeat collapsed in `Novotesproof.v`; deprecated `external_call_Three_Two` removed; `check_col_instr_sound` split into per-instruction lemmas.

**Addresses:** Multiple "Should have" differentiators from FEATURES.md.

**Avoids:** Pitfall 1 (call sites — `rg 'external_call_Three_Two'` before removal, migrate all 3 sites in same commit); Pitfall 7 (vote type dispatch — parametric helper must take the vote_ok function as an argument, not re-dispatch on `ty`); Pitfall 12 (Boolean reflection chain in `RTLcolorcheck.v` — extract one instruction case at a time, verify after each).

**Specific tasks:**
- Remove `external_call_Three_Two` after migrating all 3 call sites to `external_call_Three_Two'` (RTLtolerant.v)
- Extract `vote_lessdef_of_type` parametric lemma for `external_call_vote_lessdef` four-type-case (RTLtolerant.v)
- Extract `lookup_builtin_not_vote` helper for `no_votes_external_call` 8-repeat (Novotesproof.v)
- Extract `maj_voteR_step_of_type` parametric helper for four-type-case (RTLtmrproof.v)
- Split `check_col_instr_sound` into per-instruction lemmas (RTLcolorcheck.v)
- Verify each file: `make backend/<file>.vo` after each change

### Phase 4: no_votes Policy Unification and Comment Hygiene

**Rationale:** The `no_votes` alignment is cross-file and requires an architectural decision before any code is written; it must come after the structural cleanup is stable. Comment hygiene has no proof risk and is the lowest-stakes change in the project — it comes last.

**Delivers:** Consistent `no_votes` handling across `CSEproof.v`, `RTLagreement.v`, `Complements.v`; large commented-out dead proof blocks removed from all files; `RTLagreement.v` design notes resolved and trimmed.

**Addresses:** `no_votes` policy unification (high-value cross-file change); comment and tactic hygiene pass; table-stakes TODO resolution.

**Avoids:** Pitfall 4 (theorem signature change silently weakens Complements.v — implement as one multi-file commit; prefer Option B where checker soundness discharges the hypothesis internally); Pitfall 11 (ambiguous design notes in RTLagreement.v — decide Option A or B before writing code); Pitfall 10 (tactic scoping — define extracted tactics at file scope, not inside Proof blocks).

**Specific tasks:**
- Decide `no_votes` policy (Option A: explicit hypothesis throughout; Option B: checker soundness discharges internally) — record decision in commit message
- Implement policy change as one atomic commit touching `CSEproof.v`, `RTLagreement.v`, `Complements.v`
- Remove commented-out abandoned proof blocks from `RTLtolerant.v`, `RTLagreement.v`, `Complements.v`, `Novotes.v`, `RTLfault.v`, `RTLcolorcheck.v`
- Resolve all remaining TODO markers (each needs a resolution comment or a concrete fix)
- Verify: `make proof -j$(nproc)`, `make check-admitted`, `grep -rn "^\s*Admitted" backend/ driver/`
- Run final `coqwc` on all 8 primary target files to document proof-line reduction

### Phase Ordering Rationale

- Phase 0 before everything: backup files pollute `rg` searches used in all subsequent phases; baseline is needed to detect regressions
- Phase 1 before Phase 2: the relational spec replacements in Phase 2 could theoretically reuse the shared tactics, so the common file should exist first
- Phase 2 before Phase 3: the de-duplicated proof patterns in Phase 3 will reference the cleaner relational spec; building on a clean spec first avoids reworking Phase 3 later
- Phase 3 before Phase 4: `no_votes` policy alignment should land on a stable, already-cleaned proof base; cross-file changes are easier to reason about when the files are already in good shape
- Comment hygiene at the end of Phase 4: zero proof risk but may reveal additional cleanup opportunities best handled after the structural work is done

### Research Flags

Phases with well-documented patterns (standard Coq refactoring — skip additional research):
- **Phase 0:** Purely mechanical; no uncertainty
- **Phase 1 (move-only):** Standard `Require Import` pattern; architecture research covers this completely

Phases that may need targeted micro-research during implementation:
- **Phase 2 (relational spec):** The `foldM` state monad threading is the tricky part; budget extra time for the ordering invariants. Verify the DMR version compiles before porting to TMR.
- **Phase 3 (parametric vote helpers):** The `VoteSemantics` typeclass dispatch must not collapse in the parametric helper. Verify the helper approach compiles before committing to it (Pitfall 7).
- **Phase 4 (no_votes alignment):** The policy decision has two valid options; the codebase has conflicting design notes. Before implementing, read `RTLagreement.v` lines 139-163 and `Complements.v` lines 433-477 together and make an explicit written decision.

## Confidence Assessment

| Area | Confidence | Notes |
|------|------------|-------|
| Stack | HIGH | All tools are either already in use or are standard Coq ecosystem tools with well-known behavior; no speculative technology |
| Features | HIGH | All features identified by direct source inspection; line numbers confirmed; TODO locations confirmed |
| Architecture | HIGH | Module dependency graph constructed from direct `Require Import` inspection; shared vs. unshared content verified by reading lemma bodies |
| Pitfalls | HIGH | All pitfalls grounded in actual source file line numbers; no speculative warnings |

**Overall confidence:** HIGH

### Gaps to Address

- **`no_votes` Option A vs. Option B decision:** This cannot be resolved purely from the research — it requires a design judgment call. The research documents both options and their consequences; the decision must be made before Phase 4 implementation begins. Recommendation: Option B (checker soundness discharges internally) because `Novotes.check_program` infrastructure already exists and Option B avoids threading the hypothesis through `Complements.v` call sites.

- **`RTLtolerant.v` file split scope:** The research documents that splitting is feasible but defers it due to ROI. If the file remains at 2849 lines after Phases 1-4, evaluate then whether the comment-section approach (adding clear delimited sections within the existing file) is sufficient or whether a true file split is warranted.

- **Backup file content value:** Each backup file must be skimmed before deletion (Pitfall 8). The research notes their contents are unknown until read. This is a task for Phase 0 execution, not something pre-decidable in research.

- **Parallel DMR/TMR phase execution:** Phases 2 and 3 work on both DMR and TMR files. The research recommends doing DMR first then porting to TMR. If the DMR version compiles, the port is low-risk; if it does not compile, the approach needs revision before touching TMR. Do not work on DMR and TMR simultaneously.

## Sources

### Primary (HIGH confidence — direct source inspection)
- `/home/alex/source/compcert/backend/RTLtolerant.v` (2849 lines) — lemma-removal risk, four-case duplication, comment blocks
- `/home/alex/source/compcert/backend/RTLtmrproof.v` (2633 lines) — Section VOTE, four-case duplication, parallel structure
- `/home/alex/source/compcert/backend/RTLdmrproof.v` (1681 lines) — parallel structure, shared boilerplate
- `/home/alex/source/compcert/backend/RTLtmrspec.v` (1450 lines) — replication_map_wf_aux TODO, shared tactics
- `/home/alex/source/compcert/backend/RTLdmrspec.v` (1294 lines) — replication_map_wf_aux TODO, shared tactics
- `/home/alex/source/compcert/backend/RTLagreement.v` (207 lines, 64% comments) — no_votes design notes
- `/home/alex/source/compcert/backend/Novotesproof.v` (380 lines) — 8-repeat external_call pattern
- `/home/alex/source/compcert/backend/RTLcolorcheck.v` (534 lines) — check_col_instr_sound structure
- `/home/alex/source/compcert/driver/Complements.v` (905 lines) — top-level theorem, no_votes integration
- `/home/alex/source/compcert/Makefile` lines 159-170 — BACKEND variable, build file registration
- `/home/alex/source/compcert/plans/cleanup-plan-codex.md` — authoritative cleanup plan with phase structure
- `/home/alex/source/compcert/.planning/PROJECT.md` — project requirements and out-of-scope items

### Secondary (MEDIUM confidence — ecosystem documentation)
- Coq 8.20.0 Ltac2 reference: https://rocq-prover.org/doc/V8.20.0/refman/proof-engine/ltac2.html
- Coq section mechanism: https://rocq-prover.org/doc/v8.14/refman/language/core/sections.html
- Coq Require/Import tutorial: https://coq.inria.fr/platform-docs/RequireImportTutorial.html
- coq-dpdgraph: https://github.com/rocq-community/coq-dpdgraph
- coq-tools (JasonGross): https://github.com/JasonGross/coq-tools
- QED at Large (proof engineering survey): https://verse-lab.org/papers/qed-at-large.pdf

### Tertiary (LOW confidence — cited but not verified for this version)
- ECOOP 2025 paper on automatic goal clone detection: https://drops.dagstuhl.de/storage/00lipics/lipics-vol333-ecoop2025/LIPIcs.ECOOP.2025.12/LIPIcs.ECOOP.2025.12.pdf

---
*Research completed: 2026-03-03*
*Ready for roadmap: yes*
