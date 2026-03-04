# Roadmap: CompCert Proof Cleanup and Reorganization

## Overview

This roadmap systematically cleans up the fault-tolerance proof extension of CompCert across five phases. The dependency-aware execution order is: establish a clean baseline and delete dead files first, then introduce shared modules (move-only, zero semantic risk), then strengthen replication-map specifications so the cleaned specs are available before proof de-duplication begins, then collapse repeated proof scripts using those cleaner specs and new shared modules, and finally remove all commented-out abandoned proof blocks and resolve TODO markers. Every phase must leave the proof buildable — `make backend/<file>.vo` verifies each individual change, and `make proof -j$(nproc)` verifies each phase boundary.

## Phases

**Phase Numbering:**
- Integer phases (1, 2, 3): Planned milestone work
- Decimal phases (2.1, 2.2): Urgent insertions (marked with INSERTED)

Decimal phases appear between their surrounding integers in numeric order.

- [ ] **Phase 1: Baseline and File Cleanup** - Capture health record, delete 13 backup files and 2 dead stubs
- [ ] **Phase 2: Shared Module Introduction** - Create RTLreplicateSpecCommon.v and RTLreplicateProofCommon.v (move-only)
- [ ] **Phase 3: Spec Strengthening** - Replace monolithic replication_map_wf_aux with relational spec + consequence lemmas
- [ ] **Phase 4: Proof De-duplication** - Collapse repeated proof patterns across Novotesproof, RTLtmrproof, RTLtolerant, RTLcolorcheck
- [ ] **Phase 5: Comment and Tactic Hygiene** - Remove abandoned proof blocks, resolve all TODO markers, align naming

## Phase Details

### Phase 1: Baseline and File Cleanup
**Goal**: A clean working directory with a verified health baseline before any proof refactoring begins
**Depends on**: Nothing (first phase)
**Requirements**: FILE-01, FILE-02, FILE-03, FILE-04
**Plans:** 2 plans
Plans:
- [x] 01-01-PLAN.md — Capture build baseline (make depend, targeted .vo builds, check-admitted)
- [x] 01-02-PLAN.md — Delete 16 dead files (14 backups + 2 dead stubs) and verify clean state
**Success Criteria** (what must be TRUE):
  1. `make check-admitted` and `grep -rn "^\s*Admitted" backend/ driver/` both report zero active admitted proofs — baseline recorded
  2. `make backend/Novotesproof.vo backend/RTLdmrproof.vo backend/RTLtmrproof.vo backend/RTLtolerant.vo` all succeed — targeted build baseline captured
  3. All 13 untracked backup files (`backup_RTLinfercolor*.ml`, `backup_Constpropproof.v`, `DMRproof_backup*.v`, `RTLfault_backup.v`, `RTLAgreement_backup.v`, `backup_Compiler.v`) are absent from `git status`
  4. `backend/AdvSem.v` and `backend/Replicate3proof.v` are absent and `rg 'AdvSem\|Replicate3'` returns no matches in active source files

### Phase 2: Shared Module Introduction
**Goal**: Two new shared modules exist, compile, and are imported by both DMR and TMR files — with no proof obligations changed
**Depends on**: Phase 1
**Requirements**: MOD-01, MOD-02, MOD-03, MOD-04
**Plans:** 2 plans
Plans:
- [x] 02-01-PLAN.md — Create RTLreplicateSpecCommon.v and RTLreplicateProofCommon.v, wire spec files to import from SpecCommon
- [x] 02-02-PLAN.md — Wire proof files to import from ProofCommon, full verification
**Success Criteria** (what must be TRUE):
  1. `backend/RTLreplicateSpecCommon.v` compiles independently (`make backend/RTLreplicateSpecCommon.vo` succeeds) and contains the 6 shared Ltac tactics and shared type definitions previously duplicated in both spec files
  2. `backend/RTLreplicateProofCommon.v` compiles independently and contains the globally-scoped boilerplate lemmas previously duplicated in both proof files
  3. `make backend/RTLdmrspec.vo backend/RTLtmrspec.vo` succeed with `Require Import RTLreplicateSpecCommon` in place and duplicated content removed
  4. `make backend/RTLdmrproof.vo backend/RTLtmrproof.vo` succeed with `Require Import RTLreplicateProofCommon` in place and duplicated content removed
  5. `make check-admitted` still reports zero admitted proofs after all module wiring is complete

### Phase 3: Spec Strengthening
**Goal**: The monolithic replication_map_wf_aux proofs in both spec files are replaced by a relational spec that separates algorithmic correctness from invariant consequences
**Depends on**: Phase 2
**Requirements**: SPEC-01, SPEC-02, SPEC-03, SPEC-04
**Plans:** 2 plans
Plans:
- [ ] 03-01-PLAN.md — Define relational spec and replace monolithic proof in RTLdmrspec.v (DMR)
- [ ] 03-02-PLAN.md — Define relational spec and replace monolithic proof in RTLtmrspec.v (TMR)
**Success Criteria** (what must be TRUE):
  1. `RTLdmrspec.v` defines a `replication_map_rel` inductive and two consequence lemmas (`foldM_satisfies_rel` and `rel_implies_rm_wf`), and the monolithic `replication_map_wf_aux` is replaced by their composition
  2. `RTLtmrspec.v` has the same parallel relational structure (different arity matching TMR's `PMap.t (reg * reg)`) with `replication_map_wf_aux` similarly replaced
  3. `make backend/RTLdmrspec.vo backend/RTLdmrproof.vo` succeed — the proof file still type-checks against the new spec interface
  4. `make backend/RTLtmrspec.vo backend/RTLtmrproof.vo` succeed — the proof file still type-checks against the new spec interface

### Phase 4: Proof De-duplication
**Goal**: Repeated proof patterns across four files are collapsed into parametric helpers, and the deprecated external_call_Three_Two lemma is removed after caller migration
**Depends on**: Phase 3
**Requirements**: DEDUP-01, DEDUP-02, DEDUP-03, DEDUP-04, DEDUP-05
**Success Criteria** (what must be TRUE):
  1. `Novotesproof.v`: the 8-repeat `no_votes_external_call` case expansion is replaced by a `lookup_builtin_not_vote` helper lemma plus a concise driver — `make backend/Novotesproof.vo` succeeds
  2. `RTLtmrproof.v`: the four-type-case `maj_voteR_step` duplication is replaced by a single `maj_voteR_step_of_type` parametric lemma — `make backend/RTLtmrproof.vo` succeeds
  3. `RTLtolerant.v`: the deprecated `external_call_Three_Two` is absent (all 3 call sites migrated to `external_call_Three_Two'`), and `external_call_vote_lessdef` four-case duplication is collapsed into a `vote_lessdef_of_type` helper — `make backend/RTLtolerant.vo` succeeds
  4. `RTLcolorcheck.v`: `check_col_instr_sound` is split into per-instruction lemmas — `make backend/RTLcolorcheck.vo` succeeds
  5. `make proof -j$(nproc)` and `make check-admitted` both pass cleanly after all de-duplication is complete
**Plans:** 3 plans
Plans:
- [ ] 04-01-PLAN.md — Collapse external_call_vote_lessdef + remove deprecated external_call_Three_Two in RTLtolerant.v
- [ ] 04-02-PLAN.md — Collapse no_votes_external_call (Novotesproof.v) + maj_voteR_step (RTLtmrproof.v)
- [ ] 04-03-PLAN.md — Split check_col_instr_sound into per-instruction lemmas (RTLcolorcheck.v) + full suite verification

### Phase 5: Comment and Tactic Hygiene
**Goal**: All abandoned commented-out proof blocks are removed from active files, all in-scope TODO markers are resolved, and DMR/TMR naming conventions are aligned
**Depends on**: Phase 4
**Requirements**: HYG-01, HYG-02, HYG-03, HYG-04, HYG-05, HYG-06, HYG-07, HYG-08, HYG-09
**Success Criteria** (what must be TRUE):
  1. `RTLtolerant.v`, `RTLagreement.v`, `RTLtmr.v`, `RTLcolorcheck.v`, `Novotes.v`, and `RTLfault.v` contain no large commented-out abandoned proof blocks — design-rationale comments are preserved, dead proof drafts are gone; `driver/Complements.v` retains only the two distilled design-note sketches
  2. `rg 'TODO' backend/ driver/` returns no unresolved TODO markers in any in-scope file (each is either removed as stale, replaced by a concrete fix, or recorded with a resolution rationale)
  3. DMR and TMR helper functions with matching semantics use aligned names — `rg` comparison of naming patterns between `RTLdmrproof.v` and `RTLtmrproof.v` shows no semantically-equivalent functions with divergent names
  4. `make proof -j$(nproc)`, `make check-admitted`, and `grep -rn "^\s*Admitted" backend/ driver/` all pass clean — zero regressions from the hygiene pass
**Plans**: TBD

## Progress

**Execution Order:**
Phases execute in dependency order: 1 -> 2 -> 3 -> 4 -> 5

Note: This order differs from the original plan's phase numbering (0,1,3,2,4,5) but preserves the dependency structure — spec strengthening (Phase 3) precedes proof de-duplication (Phase 4) so that de-duplicated proofs can reference the cleaner relational specs.

| Phase | Plans Complete | Status | Completed |
|-------|----------------|--------|-----------|
| 1. Baseline and File Cleanup | 2/2 | Complete | 2026-03-03 |
| 2. Shared Module Introduction | 2/2 | Complete | 2026-03-04 |
| 3. Spec Strengthening | 0/2 | Not started | - |
| 4. Proof De-duplication | 0/3 | Not started | - |
| 5. Comment and Tactic Hygiene | 0/TBD | Not started | - |
