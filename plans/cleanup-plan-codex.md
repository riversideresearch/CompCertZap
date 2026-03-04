# Proof Cleanup and Reorganization Plan

## Objectives
- Reduce duplicated proof scripts and ad-hoc tactics.
- Separate algorithmic facts from proof plumbing (especially replication-map invariants).
- Remove dead/commented proof blocks and stale backup artifacts from the active workflow.
- Make theorem dependencies explicit (notably around `no_votes`) so proof composition is easier to maintain.

## Scope (High-Value Targets)
Active files with explicit cleanup markers and/or significant duplication:
- `backend/Novotesproof.v` (TODO at line ~51)
- `backend/RTLdmrproof.v` (TODO at line ~3)
- `backend/RTLtmrproof.v` (TODO at line ~772)
- `backend/RTLtolerant.v` (TODOs at lines ~1164, ~1371)
- `backend/RTLdmrspec.v` (TODO at line ~926)
- `backend/RTLtmrspec.v` (TODO at line ~1043)
- `backend/CSEproof.v` (TODO at line ~1574; likely stale, requires architecture decision)
- `backend/RTLagreement.v` (design TODO at line ~139)

Secondary cleanup targets:
- `backend/AdvSem.v` (unreferenced experimental stub)
- `backend/Replicate3proof.v` (unreferenced legacy proof file)
- untracked backup files in `backend/` and `driver/`:
  - `backend/backup_RTLinfercolor*.ml`
  - `backend/backup_Constpropproof.v`
  - `backend/DMRproof_backup*.v`
  - `backend/RTLfault_backup.v`
  - `backend/RTLAgreement_backup.v`
  - `driver/backup_Compiler.v`

## Guiding Principles
- Keep theorem statements stable where possible; if statements must change, migrate all call sites directly in the same change (no compatibility wrappers).
- Prefer small reusable lemmas over long tactic-heavy scripts.
- Convert repeated case splits into parametric lemmas over vote type/value constructors.
- Keep comments that encode design rationale; delete commented-out failed proof drafts once replaced.

## Phase 0: Baseline and Safety Rails
1. Create a baseline branch for cleanup work.
2. Record current proof health:
   - `make check-admitted`
   - `make backend/Novotesproof.vo backend/RTLdmrproof.vo backend/RTLtmrproof.vo backend/RTLtolerant.vo`
3. Add a lightweight "proof cleanup" checklist document section in `backend/` notes (or this file) that tracks each TODO to closure.

Exit criteria:
- Baseline build state and targeted `.vo` compilation results are captured.

## Phase 1: File and Module Reorganization
1. Delete untracked backup files from active source directories (see list above) to reduce search and review noise.
2. Remove `backend/AdvSem.v` and `backend/Replicate3proof.v` from the tree after one final reference/build check.
3. Introduce shared helper modules for DMR/TMR proofs and specs:
   - Proposed new files:
     - `backend/RTLreplicateSpecCommon.v`
     - `backend/RTLreplicateProofCommon.v`
4. Move shared invariants/lemmas from:
   - `RTLdmrspec.v` + `RTLtmrspec.v` (replication map wf machinery)
   - `RTLdmrproof.v` + `RTLtmrproof.v` (shared match/memory/register helper lemmas)

Exit criteria:
- Shared helpers are centralized and both DMR/TMR files depend on common modules.
- Listed dead/backup files are removed from active directories.

## Phase 2: De-duplicate Repeated Proof Scripts
1. `backend/Novotesproof.v`:
   - Refactor `no_votes_external_call` by introducing helper lemmas for builtin lookup exclusion.
   - Replace repeated `do N (destruct ... )` blocks with one structured lemma and concise tactic.
2. `backend/RTLtmrproof.v`:
   - Refactor `maj_voteR_step` four-type-case duplication into one generic lemma parameterized by vote constructor facts.
3. `backend/RTLtolerant.v`:
   - Refactor `external_call_vote_lessdef` by extracting a type-parametric vote-lessdef lemma.
   - Remove superseded `external_call_Three_Two` once callers are switched to the stronger `external_call_Three_Two'`-style result.
   - Split file into focused modules (match relations, helper lemmas, main simulation theorem).
4. `backend/RTLcolorcheck.v`:
   - Break `check_col_instr_sound` into per-instruction lemmas.
   - Move reusable boolean-destruction tactics/macros to a small shared proof utility section/module.
5. Remove commented-out abandoned proof blocks from active files with large accumulations:
   - `backend/RTLtolerant.v`
   - `backend/RTLagreement.v`
   - `backend/RTLtmr.v`
   - `driver/Complements.v`
   - `backend/RTLcolorcheck.v`
   - `backend/Novotes.v`
   - `backend/RTLfault.v`
   - For `driver/Complements.v`, keep only distilled design notes (not commented proof scripts) for:
     - vote-parametric RTL->Asm forward-simulation idea (`transf_rtl_program'_forward_simulation` sketch),
     - asm weak-agreement proof direction (`compiled_asm_weak_agreement` sketch).
     Delete other commented proof blocks/stubs there.

Exit criteria:
- Each TODO about "four similar cases" and repeated scripts is removed.
- Net reduction in proof script size and repeated pattern count.
- Large commented-out blocks in active proof files are substantially reduced.

## Phase 3: Strengthen Specifications Before Proofs
1. `backend/RTLdmrspec.v` and `backend/RTLtmrspec.v`:
   - Define a relational spec for replication-map construction.
   - Prove: implementation satisfies relational spec.
   - Prove: relational spec implies `rm_wf` and range properties.
2. Replace monolithic `replication_map_wf_aux` proofs with composition through the relational spec.

Exit criteria:
- "messy" replication-map proofs are split into spec + implementation + consequence lemmas.
- DMR/TMR spec proofs have parallel structure.

## Phase 4: Clarify Cross-Pass Assumptions (`no_votes`)
1. `backend/CSEproof.v`:
   - Re-evaluate TODO at line ~1574 against current proof composition in `driver/Complements.v`.
   - If current architecture is kept (2-vote CSE proof + later `no_votes_weak_agreement'` bridge), mark TODO as stale and remove/update the comment.
   - Only add a `Novotes` hypothesis to CSE theorems if we intentionally reorder/reshape the pipeline to establish `no_votes` before CSE.
2. `backend/RTLagreement.v` + `driver/Complements.v`:
   - Decide one policy and apply consistently:
     - Option A: keep `no_votes` as explicit theorem hypothesis, or
     - Option B: require `Novotes.check_program` pass before replication and discharge assumption via checker soundness.
3. Remove obsolete commented proof attempts once the chosen policy is implemented.

Exit criteria:
- `CSEproof` TODO is either removed as stale (with rationale) or implemented as part of an explicit pipeline redesign.
- `no_votes` handling is uniform in theorem statements and pipeline proofs.
- No conflicting comments suggesting multiple unfinished proof architectures.

## Phase 5: Comment and Tactic Hygiene
1. Replace broad `inv`/`try solve` clusters with named local tactics only where they measurably improve readability.
2. Keep short comments that explain non-obvious architecture-specific branches (e.g., `Archi.ptr64` cases).
3. Delete commented-out abandoned lemmas/proofs that are no longer part of the strategy.
4. Align naming conventions between DMR and TMR helper functions where semantics match (e.g., type-to-builtin helper naming).

Exit criteria:
- Proof scripts read top-down without large commented-out blocks.
- Tactics are predictable and localized.

## Verification Strategy Per Phase
- Fast checks after each logical chunk:
  - `make backend/<changed-file>.vo`
- Integration checks after each phase:
  - `make proof -j$(nproc)` (or at minimum all touched dependency cones)
  - `make check-admitted`

## Suggested Execution Order (Dependency-Aware)
1. Phase 0 (baseline)
2. Phase 1 (module/file layout)
3. Phase 3 (spec cleanup for replication map)
4. Phase 2 (proof de-dup relying on new shared/spec lemmas)
5. Phase 4 (`no_votes` policy alignment)
6. Phase 5 (final hygiene pass)

## Risks and Mitigations
- Risk: theorem signature churn breaks many downstream proofs.
  - Mitigation: do signature changes in one dependency-aware pass, update all call sites immediately, and validate with targeted `.vo` builds before full proof rebuild.
- Risk: cleanup-only commits accidentally change proof obligations.
  - Mitigation: separate commits by type (move-only, lemma extraction, statement changes).
- Risk: removing "unused" files that are referenced externally.
  - Mitigation: verify via `rg` over repo + build before deletion; archive first if uncertain.

## Deliverables
- Reorganized DMR/TMR proof/spec modules with shared common files.
- TODO markers removed (or replaced with actionable issue IDs) in in-scope active files.
- Reduced dead commented proof code in `RTLtolerant.v`, `RTLagreement.v`, and `Novotesproof.v`.
- Clean build and admitted-proof checks passing.
