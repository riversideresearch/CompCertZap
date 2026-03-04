# Phase 5: Comment and Tactic Hygiene - Research

**Researched:** 2026-03-04
**Domain:** Coq source hygiene -- removing dead code comments, resolving TODO markers, aligning naming conventions
**Confidence:** HIGH

## Summary

Phase 5 is a pure cleanup phase that removes commented-out abandoned proof blocks, resolves or removes TODO markers, and aligns naming conventions between DMR and TMR helper functions. Unlike Phases 2-4, this phase makes no semantic changes to any proof -- it only removes dead comments, resolves markers, and renames identifiers. The primary risk is accidentally deleting design-rationale comments that look like dead code, or breaking the build by removing something that Coq still needs.

Seven files are in scope for comment removal (HYG-01 through HYG-07), spanning approximately 780 lines of commented-out code across 5,141 total lines. The largest concentrations are in `driver/Complements.v` (256 comment lines in a 905-line file) and `backend/RTLtolerant.v` (216 comment lines in a 2,822-line file). For HYG-08 (TODOs), there are 9 in-scope TODO markers across 7 files. For HYG-09 (naming alignment), the primary finding is that DMR/TMR naming divergences are largely justified by different semantics (check vs. vote), with only minor cosmetic inconsistencies.

**Primary recommendation:** Execute file-by-file, removing commented-out blocks first, then resolving TODOs, then doing any naming alignment -- building after each file to verify zero regressions. The Complements.v cleanup requires the most care due to the "retain two design-note sketches" requirement.

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|-----------------|
| HYG-01 | Large commented-out abandoned proof blocks removed from RTLtolerant.v | 10 comment blocks identified (216 lines), all are superseded proof drafts |
| HYG-02 | Large commented-out blocks removed from RTLagreement.v | 4 comment blocks (144 of 205 lines); most of file is dead code |
| HYG-03 | Commented-out blocks removed from RTLtmr.v | 2 comment blocks (72 lines); old `can_replicate_instr` and `transf_instr` drafts |
| HYG-04 | Commented-out blocks removed from Complements.v (keep two design notes) | 6 comment blocks (256 lines); retain vote-parametric RTL->Asm forward-sim sketch (lines 74-114) and asm weak-agreement sketch (lines 586-639); delete all others |
| HYG-05 | Commented-out blocks removed from RTLcolorcheck.v | 3 comment blocks (71 lines); old `check_col_instr` res-based version and completeness stubs |
| HYG-06 | Commented-out blocks removed from Novotes.v | 2 comment blocks (12 lines); old `check_function`/`check_fundef`/`check_program` res-based versions |
| HYG-07 | Commented-out blocks removed from RTLfault.v | 1 comment block (10 lines); abandoned `idfg` lemma + 1 design comment (keep) |
| HYG-08 | All TODO markers in in-scope files resolved or removed (excluding CSEproof.v) | 9 in-scope TODOs identified; each categorized with resolution strategy |
| HYG-09 | Naming conventions aligned between DMR and TMR helper functions | Primary inconsistency: `maj_vote_regR_star_step` should be `maj_vote_regsR_star_step` (singular->plural to match spec name) |
</phase_requirements>

## Standard Stack

### Core
| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| Coq/Rocq | 8.20.0 | Proof assistant | Already in use, unchanged |
| OCaml | 4.14.2 | Extraction target | Already in use, unchanged |
| GNU Make | system | Build system | Standard CompCert build |

### Supporting
No additional libraries needed. All changes are comment/naming cleanup within existing files.

## Architecture Patterns

### Pattern 1: Comment Block Classification
**What:** Before removing any commented-out block, classify it as one of three types:
1. **Dead proof draft** -- an abandoned attempt that has been superseded by active code (DELETE)
2. **Design-rationale comment** -- explains WHY a design decision was made, even if phrased in code-like terms (KEEP)
3. **Inline annotation** -- a single-line comment within active code explaining a choice (KEEP)

**When to use:** Every commented-out block in HYG-01 through HYG-07.

**Decision criteria:**
- Does active code below/near it serve the same purpose? -> Dead draft, DELETE
- Does it explain a design decision or future direction that isn't obvious from the active code? -> Design rationale, KEEP
- Is it a single-line note inside working code (e.g., `(* ::: mkpass Novotesproof.match_prog *)`)? -> Inline annotation, KEEP

### Pattern 2: TODO Resolution Categories
**What:** Each TODO marker gets one of three resolutions:
1. **Remove as stale** -- the concern has been addressed or is no longer relevant
2. **Replace with concrete fix** -- implement the change the TODO describes
3. **Record resolution rationale** -- convert TODO to a design-note comment explaining why it was kept/deferred

**When to use:** Every TODO in HYG-08.

### Pattern 3: Build-After-Each-File
**What:** After modifying each file, run `make backend/<file>.vo` (or `make driver/<file>.vo`) to verify compilation. Run full suite at phase end.

**Why:** Comment removal is low-risk but accidental deletion of active code disguised as comments would break the build immediately. Per-file builds catch errors early.

### Anti-Patterns to Avoid
- **Removing design-rationale comments:** The Complements.v "two design-note sketches" are specifically called out for retention. Be extra careful with comments that explain proof strategies even if they look like dead code.
- **Bulk regex deletion:** Don't use sed/regex to mass-remove `(* ... *)` blocks -- manual classification is required per Pattern 1.
- **Renaming without updating all references:** For HYG-09, any renamed lemma must have ALL call sites updated in the same commit.

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Finding TODOs | Manual file reading | `rg 'TODO' backend/ driver/` | Grep catches all occurrences, manual review misses some |
| Finding commented blocks | Visual scanning | Script-based detection of `(*` block runs | 5+ line blocks easily missed in 2800-line files |
| Verifying no regressions | Spot-checking | `make proof -j$(nproc) && make check-admitted` | Full build is the only reliable regression test |

## Common Pitfalls

### Pitfall 1: Deleting Design Comments That Look Like Dead Code
**What goes wrong:** A commented-out proof sketch that records design rationale gets deleted, losing institutional knowledge.
**Why it happens:** Coq comments use `(* ... *)` for both dead code and design notes, making them visually identical.
**How to avoid:** Read context around each block. If the comment explains a decision or future direction (not just an old proof attempt), keep it. The two Complements.v sketches are the primary examples.
**Warning signs:** Comment mentions "sketch", "direction", "future", "could", "might want to" -- these are often design notes, not dead code.

### Pitfall 2: Accidentally Removing Active Inline Comments
**What goes wrong:** Single-line comments within active code get swept up in cleanup.
**Why it happens:** `(* ::: mkpass Novotesproof.match_prog *)` on line 131 of Complements.v looks like dead code but is actually an intentional annotation within the active `c_to_rtl_passes` definition.
**How to avoid:** Only remove multi-line comment blocks that are completely standalone (not embedded within active definitions/proofs).

### Pitfall 3: TODO in Variable Names
**What goes wrong:** `rg 'TODO'` matches variable names like `w_todo` in Unusedglobproof.v.
**Why it happens:** The string "TODO" appears in CompCert's own variable names (workset fields).
**How to avoid:** Verify each grep hit manually. The `Unusedglobproof.v:83` hit and `CSEproof.v:1574` hit are both out-of-scope.

### Pitfall 4: Renaming Breaking Build
**What goes wrong:** Renaming a lemma in a proof file but missing a call site in another file.
**Why it happens:** Coq doesn't have IDE-level rename refactoring; must grep for all uses.
**How to avoid:** Before renaming, `rg 'old_name' backend/ driver/` to find ALL references. Update all in one commit.

### Pitfall 5: RTL.v TODOs -- Scope Boundary
**What goes wrong:** Modifying RTL.v (a core CompCert file) for TODO cleanup, violating the "don't touch non-fault-tolerance files" principle.
**Why it happens:** RTL.v contains fault-tolerance additions (is_protected, vote builtins) alongside core RTL definitions.
**How to avoid:** The TODOs in RTL.v lines 895-904 are design-rationale comments for the fault-tolerance extension. They should be treated as design notes (convert from TODO to plain comment), not as items requiring code changes. Since they're in a core file, the lightest touch is appropriate.

## Code Examples

### Removing a Dead Proof Block (HYG-01 example)

The block at RTLtolerant.v lines 958-1041 is a dead draft:
```coq
(* Before: 84 lines of commented-out lemmas *)
(* Lemma rs_eq_eval_addressing sp addr rs1 rs2 args a : *)
(*   (forall r, rs1 # r = rs2 # r) -> *)
(*   ... *)

(* After: block deleted, no replacement needed *)
(* The active Ltac inv_Forall at line 953 and subsequent active code serve the purpose *)
```

### Resolving a TODO as Design Note (RTLtolerant.v line 1344)

```coq
(* Before: *)
(* TODO: the four cases in this proof are literally the same except
   the type argument to [vote]. *)

(* After -- Phase 4 decided to keep the four cases (DEDUP-03 abandoned): *)
(* Note: The four cases below are structurally identical modulo the type
   argument to [vote]. Deduplication via Ltac was attempted in Phase 4
   but abandoned due to hypothesis name instability across inversion chains. *)
```

### Resolving a TODO by Removing Stale Comment (RTLtmr.v lines 161-170)

```coq
(* Before: 15 lines of commented-out can_replicate_instr with embedded TODO *)
(* Definition can_replicate_instr (instr : instruction) : bool := *)
(*   ... *)
(*   (* TODO: return true for some builtins *) *)
(*   ... *)

(* After: entire block deleted -- superseded by the active transf_instr *)
```

## Detailed Inventory

### HYG-01: RTLtolerant.v Comment Blocks (10 blocks, 216 lines)

| Lines | Content | Classification | Action |
|-------|---------|----------------|--------|
| 54-60 | Old `match_rs_fault` lemma | Dead draft (superseded by `match_rs_upto_fault` at line 63) | DELETE |
| 482-489 | Incomplete `dfgd` lemma | Dead draft (superseded by `val_compat_shl_imm` at line 490) | DELETE |
| 932-952 | Two incomplete addressing lemmas | Dead drafts (no proof body, superseded by active addressing lemmas) | DELETE |
| 958-1041 | 84-line block of rs_eq lemmas | Dead drafts (superseded by Forall-based approach in active code) | DELETE |
| 1049-1070 | `inv_match_rs` Ltac + lemma | Dead draft (old tactic approach abandoned) | DELETE |
| 1102-1117 | `builtin_or_external_sem_Three_Two` | Dead draft (superseded by active `external_call_Three_Two'`) | DELETE |
| 1162-1170 | `list_eq_mod_1` inductive | Dead draft (superseded by `list_lessdef_mod_1` at line 1171) | DELETE |
| 1182-1195 | `lessdef_vote3_vote` (old signature) | Dead draft (superseded by active `lessdef_vote3_vote` at line 1196 with `ty` param) | DELETE |
| 1300-1315 | `external_call_smove_res` | Dead draft (incomplete, superseded) | DELETE |
| 1802-1819 | `external_call_mem_extends` (old sig) | Dead draft (superseded by active version at line 1820) | DELETE |

### HYG-02: RTLagreement.v Comment Blocks (4 blocks, 144 lines)

| Lines | Content | Classification | Action |
|-------|---------|----------------|--------|
| 18-71 | `RTL_STRONG_AGREEMENT` section | Dead draft (strong agreement approach abandoned for weak agreement) | DELETE |
| 89-93 | `weak_agreement'` definition | Dead draft (5 lines) | DELETE |
| 96-137 | `agree_forever_silent` + `strong_agreement_implies_weak_agreement` | Dead drafts (strong agreement approach abandoned) | DELETE |
| 163-205 | `AGREEMENT_PRESERVATION` section | Dead draft (forward sim preservation approach superseded) | DELETE |

**Note:** The design comment at lines 137-161 (TODO about `no_votes` + Addendum) is a design-rationale block. It should be converted from TODO to design note, not deleted.

### HYG-03: RTLtmr.v Comment Blocks (2 blocks, 72 lines)

| Lines | Content | Classification | Action |
|-------|---------|----------------|--------|
| 161-175 | `can_replicate_instr` + embedded TODO | Dead draft (superseded by `transf_instr`) | DELETE |
| 225-281 | Old `transf_instr` definition | Dead draft (superseded by active `transf_instr` above) | DELETE (including embedded TODO at 238) |

### HYG-04: Complements.v Comment Blocks (6 blocks, 256 lines)

| Lines | Content | Classification | Action |
|-------|---------|----------------|--------|
| 74-114 | Vote-parametric RTL->Asm forward-sim sketch | **Design note** (per HYG-04 requirement) | **KEEP** (distill to concise comment) |
| 131 | `(* ::: mkpass Novotesproof.match_prog *)` | Inline annotation | **KEEP** (within active code) |
| 137-187 | First `compiled_rtl_safe` (unparameterized) | Dead draft (two versions, both dead) | DELETE |
| 189-248 | Second `compiled_rtl_safe` (vote-parameterized) + End VOTE | Dead draft (second attempt, also dead) | DELETE |
| 280-284, 301-308 | `compiled_rtl_weak_agreement` + `idfg` stubs | Dead stubs | DELETE |
| 572-579 | Old proof ending for `transf_c_program_to_rtl_preservation_faulty` | Dead draft | DELETE |
| 581-584 | Empty `Section VOTE` | Dead stub | DELETE |
| 586-639 | `compiled_asm_weak_agreement` sketch | **Design note** (per HYG-04 requirement) | **KEEP** (distill to concise comment) |

### HYG-05: RTLcolorcheck.v Comment Blocks (3 blocks, 71 lines)

| Lines | Content | Classification | Action |
|-------|---------|----------------|--------|
| 78-118 | Old res-based `check_col_instr` | Dead draft (superseded by bool-based version at line 120) | DELETE |
| 173-188 | Old smove checker (single smove, before green/blue split) | Dead draft (superseded by green/blue split at line 189) | DELETE |
| 619-631 | `check_col_function_complete` + `check_col_function_spec` stubs | Dead stubs (can't prove completeness without `infer_coloring` spec) | DELETE |
| 649-650 | `(* check_function_complete not possible because... *)` | Design note | **KEEP** |

### HYG-06: Novotes.v Comment Blocks (2 blocks, 12 lines)

| Lines | Content | Classification | Action |
|-------|---------|----------------|--------|
| 24-29 | Old res-based `check_function` | Dead draft (superseded by active bool-based version) | DELETE |
| 42-47 | Old `check_fundef` + `check_program` (res-based) | Dead draft | DELETE |

### HYG-07: RTLfault.v Comment Blocks (1 block, 10 lines)

| Lines | Content | Classification | Action |
|-------|---------|----------------|--------|
| 50-57 | Incomplete `idfg` lemma | Dead draft (no complete proof, superseded by `maybe_zap_val_compat`) | DELETE |
| 59-60 | `(* Technically we could/should allow faults... *)` | Design note | **KEEP** |

### HYG-08: TODO Resolution Map

| Location | TODO Text | Resolution | Rationale |
|----------|-----------|------------|-----------|
| RTLtolerant.v:1344 | "the four cases in this proof are literally the same" | Convert to design note | Phase 4 abandoned DEDUP-03 due to hypothesis name instability; record decision |
| Novotesproof.v:51 | "cleanup. This proof is 8 repeats" | Convert to design note | Phase 4 abandoned DEDUP-01 due to infinite memory consumption; record decision |
| RTLagreement.v:137 | "get rid of no_votes at the C level" | Convert to design note | Design decision recorded; no_votes at RTL level is the chosen approach; remove "TODO" prefix |
| RTLcolorcheck.v:117 | `assert false "TODO"` inside commented-out block | Delete with block | Entire block is deleted under HYG-05 |
| RTLinfercolor.ml:210 | `"TODO"` inside commented-out block | Delete with block | Commented-out debug code |
| RTLtmr.v:168 | "return true for some builtins" inside commented-out block | Delete with block | Entire block deleted under HYG-03 |
| RTLtmr.v:238 | "treat most builtins like this" inside commented-out block | Delete with block | Entire block deleted under HYG-03 |
| RTL.v:895 | "maybe we can just assume faulted floats aren't NaN" | Convert to design note | Remove "TODO:" prefix, keep as design rationale; minimal touch on core file |
| RTL.v:903 | "Also TODO: this might need to go into backend specific Op.v" | Convert to design note | Same block as above; remove "TODO:" prefix |

### HYG-09: Naming Convention Analysis

**Finding:** Most DMR/TMR naming divergences reflect genuine semantic differences between 2-way checking (DMR) and 3-way majority voting (TMR). These are NOT misalignment -- they are correct domain-specific naming.

**Genuine inconsistency found:**
| DMR | TMR | Issue | Fix |
|-----|-----|-------|-----|
| `check_regsR_star_step` | `maj_vote_regR_star_step` | TMR uses singular "reg" but spec name `maj_vote_regsR` uses plural "regs" | Rename TMR to `maj_vote_regsR_star_step` |

**Intentionally different (no change needed):**
| DMR Name | TMR Name | Reason for Difference |
|----------|----------|----------------------|
| `checkR_step` | `maj_voteR_step` | Different operations (check vs. vote) |
| `check_regsR_star_step` | `maj_vote_regsR_star_step` (after fix) | Different operations |
| `smove_step` | `green_smove_step` / `blue_smove_step` | TMR has two shadow colors |
| `rm_wf_neq_1_2`, `rm_wf_neq_2_2` | Same + `rm_wf_neq_1_3`, `rm_wf_neq_2_3`, etc. | TMR has 3rd shadow register |

**Shared names (already aligned):** 55 lemmas share identical names across both files (e.g., `symbols_preserved`, `functions_translated`, `match_regsets_eval_addressing`, `step_simulation`, `transf_program_correct`).

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| res-based checkers (Novotes, RTLcolorcheck) | bool-based checkers | During initial development | Old res-based versions are all in comments now |
| Single smove builtin | Green/Blue smove split | During color system refinement | Old single-smove code in comments |
| Strong agreement | Weak agreement (no_votes based) | Design evolution | RTLagreement.v strong_agreement section is dead |

## Open Questions

1. **RTL.v TODO scope**
   - What we know: RTL.v lines 895-904 contain fault-tolerance TODOs. The file is technically a "core CompCert file" but the TODO is in fault-tolerance-specific code.
   - What's unclear: Whether modifying this file violates the "don't touch non-fault-tolerance CompCert files" principle.
   - Recommendation: Minimal touch -- convert "TODO:" to a plain design comment. This is a 2-word change (removing "TODO:" prefix) in fault-tolerance-specific code within RTL.v.

2. **Complements.v design sketch distillation**
   - What we know: HYG-04 says "keep distilled design notes" for two proof sketches.
   - What's unclear: How much to distill. The raw proof sketches are 42 and 70 lines respectively.
   - Recommendation: Replace each with a 5-10 line comment block that summarizes the proof strategy without full Coq syntax, since the sketches are incomplete anyway.

3. **HYG-09 rename scope**
   - What we know: Only one genuine naming inconsistency found (`maj_vote_regR_star_step` -> `maj_vote_regsR_star_step`).
   - What's unclear: Whether the requirement expects more extensive naming alignment.
   - Recommendation: Fix the one inconsistency. Document that remaining differences are semantically justified. This satisfies the requirement ("no semantically-equivalent functions with divergent names") since the divergent names reflect genuinely different semantics.

## Validation Architecture

### Test Framework
| Property | Value |
|----------|-------|
| Framework | Coq 8.20.0 proof checking (make proof) |
| Config file | Makefile + _CoqProject |
| Quick run command | `make backend/<file>.vo` (per-file) |
| Full suite command | `make proof -j$(nproc) && make check-admitted` |

### Phase Requirements -> Test Map
| Req ID | Behavior | Test Type | Automated Command | File Exists? |
|--------|----------|-----------|-------------------|-------------|
| HYG-01 | RTLtolerant.v compiles without commented blocks | build | `make backend/RTLtolerant.vo` | N/A (build check) |
| HYG-02 | RTLagreement.v compiles without commented blocks | build | `make backend/RTLagreement.vo` | N/A |
| HYG-03 | RTLtmr.v compiles without commented blocks | build | `make backend/RTLtmr.vo` | N/A |
| HYG-04 | Complements.v compiles, retains 2 design notes | build + manual | `make driver/Complements.vo` | N/A |
| HYG-05 | RTLcolorcheck.v compiles without commented blocks | build | `make backend/RTLcolorcheck.vo` | N/A |
| HYG-06 | Novotes.v compiles without commented blocks | build | `make backend/Novotes.vo` | N/A |
| HYG-07 | RTLfault.v compiles without commented blocks | build | `make backend/RTLfault.vo` | N/A |
| HYG-08 | No unresolved TODOs in scope | grep | `rg 'TODO' backend/ driver/ --glob '!CSEproof.v' --glob '!Unusedglobproof.v'` | N/A |
| HYG-09 | No divergent names for equivalent functions | grep | `rg 'maj_vote_regR_star_step' backend/` returns 0 hits after rename | N/A |

### Sampling Rate
- **Per task commit:** `make backend/<file>.vo` for each modified file
- **Per wave merge:** `make proof -j$(nproc) && make check-admitted`
- **Phase gate:** Full suite green + `rg 'TODO' backend/ driver/` clean + `grep -rn '^\s*Admitted' backend/ driver/` clean

### Wave 0 Gaps
None -- existing build infrastructure covers all phase requirements. No new test files or fixtures needed.

## Sources

### Primary (HIGH confidence)
- Direct file inspection of all 7 in-scope files (RTLtolerant.v, RTLagreement.v, RTLtmr.v, RTLcolorcheck.v, Novotes.v, RTLfault.v, Complements.v)
- Direct file inspection of RTLdmrproof.v and RTLtmrproof.v for naming comparison
- Direct file inspection of RTLdmr.v and RTLtmr.v for spec-level naming
- REQUIREMENTS.md for requirement definitions
- STATE.md for Phase 4 decisions (DEDUP-01/DEDUP-03 abandonment rationale)

### Secondary (MEDIUM confidence)
- Phase 4 research and plan documents for context on abandoned dedup decisions

## Metadata

**Confidence breakdown:**
- Comment block inventory: HIGH - direct file inspection, every block manually classified
- TODO inventory: HIGH - `rg 'TODO'` exhaustive search + manual classification
- Naming alignment: HIGH - automated name extraction + manual semantic comparison
- Design note identification: MEDIUM - requires judgment calls on comment intent

**Research date:** 2026-03-04
**Valid until:** 2026-04-04 (stable -- no external dependencies)
