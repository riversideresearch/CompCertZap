# Feature Landscape: Coq Proof Cleanup for CompCert Fault Tolerance

**Domain:** Large Coq proof codebase maintenance and refactoring
**Researched:** 2026-03-03
**Project:** CompCert fault-tolerance extension (DMR/TMR + color checker)

---

## Table Stakes

Features users (future proof maintainers) expect. Missing = proof base degrades or becomes unmaintainable.

| Feature | Why Expected | Complexity | Notes |
|---------|--------------|------------|-------|
| Delete all backup/dead files | Untracked backup files pollute search, code review, and grep; they are not built and have no referents | Low | 6 `.v` backup files (~6,737 lines), 7 `.ml` backups (~146k chars), 2 dead stub files (`AdvSem.v` 52 lines, `Replicate3proof.v` 2,532 lines). All confirmed unreferenced by `rg` and absent from Makefile. |
| Remove commented-out abandoned proof blocks | Large blocks of dead commented code make it impossible to read the live proof strategy; they signal unresolved design choices | Medium | `RTLtolerant.v` has ~260 comment lines in 2,849 total; `Complements.v` has 264 comment lines in 905 total; `RTLagreement.v` has commented Admitted attempts. Must audit each block: design rationale comments stay, dead proof drafts go. |
| Resolve explicit TODO markers | TODOs in 8 active files are acknowledged technical debt. Leaving them in signals the file is not in a final state and makes it unclear what's complete. | Medium | 8 files with TODOs: `Novotesproof.v`, `RTLdmrproof.v`, `RTLtmrproof.v`, `RTLtolerant.v` (x2), `RTLdmrspec.v`, `RTLtmrspec.v`, `CSEproof.v`, `RTLagreement.v`. Each TODO requires a concrete resolution action (fix or document as out-of-scope). |
| Build integrity at every commit | Standard invariant for formal proof repos: if it doesn't compile, the proof doesn't exist | Low (process) | Use `make backend/<file>.vo` for fast per-file checks. Full `make proof -j$(nproc)` at phase boundaries. Non-negotiable. |
| Establish baseline health record | Before any refactoring, capture `make check-admitted` output and targeted `.vo` build results so regressions are detectable | Low | One-time task. Avoids "was that Admitted there before?" confusion during cleanup. |

---

## Differentiators

Features that significantly improve long-term maintainability. Not strictly required to keep the proof working, but substantially improve the quality of the proof base.

| Feature | Value Proposition | Complexity | Notes |
|---------|-------------------|------------|-------|
| Centralize shared DMR/TMR proof lemmas into common modules | DMR and TMR proof files (`RTLdmrproof.v` 1,681 lines, `RTLtmrproof.v` 2,633 lines) have parallel structure confirmed by structural diff. Both have the same `match_prog` pattern, same `transf_program_correct` theorem shape, same imports minus the spec file. Shared helpers eliminate the "fix it in two places" problem. | High | Requires new `RTLreplicateProofCommon.v` and `RTLreplicateSpecCommon.v`. The spec files differ structurally (DMR uses `PMap.t reg`, TMR uses `PMap.t (reg * reg)`) so abstraction requires care — likely via a type parameter or functor, not simple copy-elimination. |
| Centralize shared DMR/TMR spec lemmas | `RTLdmrspec.v` and `RTLtmrspec.v` both contain `rm_wf`, `rm_l`, `replication_map_wf_aux`, `replication_map_wf`, and structural proof machinery. The TODO in both files calls this out explicitly. | High | DMR spec is 1,294 lines; TMR spec is 1,450 lines. Common structure is visible in `diff` output but the specific type difference (`reg` vs `reg * reg`) means abstraction is non-trivial. Worth doing because both files will continue to diverge without it. |
| De-duplicate `no_votes_external_call` in Novotesproof | The TODO at line 51 explicitly says "8 repeats of almost the same proof script". Introducing a helper lemma for builtin lookup exclusion removes the repetition. | Low | Novotesproof.v is only 380 lines; the proof is self-contained. Low risk, high readability gain. |
| Refactor `maj_voteR_step` four-case duplication in RTLtmrproof | TODO at line 772 says "all four cases are very similar" — the cases differ only by the type argument to `vote`. A single generic lemma parameterized by vote constructor facts eliminates this. | Medium | RTLtmrproof.v is 2,633 lines. The duplication is within the proof of one lemma, so scope is contained. |
| Refactor `external_call_vote_lessdef` in RTLtolerant | TODO at line 1371 says "four cases in this proof are literally the same except the type argument". Same pattern as above — a type-parametric vote-lessdef lemma removes duplication. Also: remove deprecated `external_call_Three_Two` once callers are switched to `external_call_Three_Two'` (line 1164 TODO). | Medium | RTLtolerant.v is the largest file at 2,849 lines. The two changes are independent — removal of deprecated lemma is Low complexity, the four-case refactor is Medium. |
| Introduce relational spec for replication-map construction | Both spec files contain monolithic `replication_map_wf_aux` proofs that mix algorithm proof with consequence derivation. The TODOs in both files recommend the same fix: split into (1) relational spec, (2) proof that implementation satisfies spec, (3) proof that spec implies `rm_wf`. | High | This is architectural restructuring of the core invariant proof machinery. High payoff: enables parallel DMR/TMR structure and makes each piece independently auditable. High risk: must not change theorem signatures exported to proof files. |
| Unify `no_votes` handling across CSEproof and pipeline | `CSEproof.v` TODO says `transf_program_correct` should take `Novotes` as hypothesis. `RTLagreement.v` TODO documents two policy options. Currently the policy is inconsistent: `Complements.v` manually extracts `no_votes` from the pipeline result rather than threading it through as a typed assumption. Picking Option B (checker soundness discharges assumption) aligns with the existing `Novotes.check_program` infrastructure. | High | Cross-file change: `CSEproof.v`, `RTLagreement.v`, `driver/Complements.v`, `driver/Compiler.v` all touched. Must update all call sites atomically. High benefit: removes commented-out proof attempts in `Complements.v` lines 630-640. |
| Break `check_col_instr_sound` into per-instruction lemmas | The lemma in `RTLcolorcheck.v` (lines 266-534, ~269 lines) handles all instruction types in one 269-line proof. Per-instruction lemmas are independently checkable, faster to debug, and easier to extend for new instructions. | Medium | RTLcolorcheck.v is only 534 lines total. Splitting the one giant lemma is well-contained. Requires care that the top-level `check_program_sound` still assembles from the parts. |
| Tactic and naming convention alignment | DMR uses `check`, `checkR`, `check_regs`, while TMR uses `maj_vote`, `maj_voteR`, `maj_vote_regs`. Where semantics match (e.g., smove helpers), names should align. Naming divergence increases the cognitive overhead of reading both files. | Low | Purely cosmetic but high readability value. Risk: rename propagates to proof files that reference these names. Must audit call sites before renaming. |
| Split RTLtolerant.v into focused modules | At 2,849 lines, RTLtolerant.v contains: match relations (lines ~1-143), helper lemmas, and the main backward simulation theorem (the bulk). The cleanup plan proposes splitting into at least three focused files. | High | Highest-complexity refactor in the plan. RTLtolerant.v has only two sections: `match_states` (67 lines) and `TOLERANCE` (2,705 lines). Splitting requires identifying clean module boundaries within the giant `TOLERANCE` section. Defer if scope is a concern — the other changes provide more value per effort. |

---

## Anti-Features

Things to deliberately NOT do during this cleanup.

| Anti-Feature | Why Avoid | What to Do Instead |
|--------------|-----------|-------------------|
| Change theorem signatures without migrating all call sites | Any signature change creates a broken intermediate state that can fail to compile. Multiple broken files during cleanup is a debugging nightmare. | Change signatures only in commits that simultaneously update all call sites. Use `rg` to find all call sites before touching any theorem statement. |
| Add compatibility shim lemmas that wrap changed signatures | Shims double the proof surface, defeating the purpose of cleanup. The cleanup plan explicitly says "no compatibility wrappers." | Change signatures directly and migrate callers in the same commit. |
| Remove files without a prior `rg` + build verification pass | `AdvSem.v` and `Replicate3proof.v` are untracked and absent from the Makefile, but this must be confirmed with search before deletion. `Replicate3proof.v` is 2,532 lines and references `Replicate` and `Replicatespec` — these modules may or may not still exist. | Run `rg AdvSem` and `rg Replicate3proof` over the repo, and attempt `make backend/AdvSem.vo` before deleting. |
| Optimize build times | Scope creep. Build performance is declared out of scope in PROJECT.md. | Leave build performance for a separate dedicated effort. |
| Touch files outside the fault-tolerance extension | The cleanup targets are the 8 active files plus dead/backup files. CSEproof.v is the boundary case (it's a standard CompCert file with one TODO added by the fault-tolerance fork). Only touch CSEproof.v for the `no_votes` threading change, nothing else. | Treat standard CompCert files (Inlining, Selection, etc.) as read-only unless forced by a dependency. |
| Create new features or compiler passes | This is maintenance work. Any new functionality is out of scope. | File as a separate project/milestone after cleanup completes. |
| Use `Admitted` as a progress placeholder | Admitted proofs silently break the soundness guarantee. There are currently 0 active Admitted proofs (only commented-out Admitted lines in dead blocks). Maintain this invariant. | If a proof cannot be completed during cleanup, leave the original proof in place and do not land the cleanup for that item. |
| Rewrite proof scripts for style without functional verification | Style-only rewrites that change tactic order can break proofs in subtle ways (fragile `omega` calls, rewrite orientation dependencies). | Keep tactic rewrites small and immediately verify with `make backend/<file>.vo`. |

---

## Feature Dependencies

These dependencies determine the safe execution order for cleanup tasks.

```
Delete backup files                     (no dependencies - do first, low risk)
    |
    v
Baseline health record                  (depends on: clean file tree)
    |
    v
Introduce RTLreplicateSpecCommon.v      (depends on: baseline)
    |
    v
Refactor replication_map_wf (DMR+TMR)   (depends on: RTLreplicateSpecCommon.v)
    |
    v
De-duplicate DMR+TMR proof scripts      (depends on: RTLreplicateSpecCommon.v, RTLreplicateProofCommon.v)
    |
    v
Unify no_votes policy                   (depends on: de-duplication complete, optional but cleaner after)
    |
    v
Comment/tactic hygiene pass             (depends on: all structural changes done)

Independent tracks (no ordering constraint relative to each other):
  - De-duplicate Novotesproof
  - Break check_col_instr_sound into per-instruction lemmas
  - Remove external_call_Three_Two (deprecated lemma in RTLtolerant)
  - Tactic naming alignment DMR/TMR
```

Key constraint from cleanup plan: Phase 3 (spec relational spec) must precede Phase 2 (proof de-duplication) because the de-duplicated proof scripts will depend on the shared spec lemmas.

---

## MVP Recommendation

For a minimal but meaningful cleanup that leaves the proof base noticeably better:

**Must do (table stakes - do in Phase 0 and Phase 1):**
1. Delete all backup files and dead stubs (`AdvSem.v`, `Replicate3proof.v`, 13 backup files)
2. Capture baseline health (`make check-admitted`, targeted `.vo` builds)
3. Remove large commented-out abandoned proof blocks from `RTLtolerant.v`, `Complements.v`, `RTLagreement.v`

**High value, medium risk (Phase 2 work):**
4. De-duplicate `no_votes_external_call` (8 repeats → 1 helper + 1 driver lemma)
5. Refactor `external_call_vote_lessdef` four-case duplication (RTLtolerant.v TODO line 1371)
6. Remove deprecated `external_call_Three_Two` once callers use `external_call_Three_Two'` (RTLtolerant.v TODO line 1164)

**Defer to later milestones (high complexity, high payoff):**
- Relational spec for replication-map construction (Phase 3 - architectural, requires sustained focus)
- Full DMR/TMR centralization into common modules (Phase 1/3 - requires Coq module design)
- `no_votes` policy unification across CSEproof + pipeline (Phase 4 - cross-file, requires deciding architecture first)
- RTLtolerant.v file split (Phase 2 option - defer: other changes are higher ROI per effort)

---

## Sources

- Direct inspection of active source files (`RTLtolerant.v`, `RTLtmrproof.v`, `RTLdmrproof.v`, `RTLtmrspec.v`, `RTLdmrspec.v`, `RTLcolorcheck.v`, `Novotesproof.v`, `RTLagreement.v`, `CSEproof.v`, `driver/Complements.v`)
- `plans/cleanup-plan-codex.md` - authoritative cleanup plan with phase structure
- `.planning/PROJECT.md` - project requirements and constraints
- `Makefile` - confirmed which files are actually built (AdvSem, Replicate3proof absent)
- `git status` - confirmed which files are untracked (backup files, dead stubs)
- Structural comparison of DMR vs TMR files via `diff` on definition lists
- Line count analysis: total ~11,028 lines across 8 primary targets
