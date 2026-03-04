---
phase: 05-comment-tactic-hygiene
verified: 2026-03-04T16:30:00Z
status: passed
score: 9/9 must-haves verified (human approved retention decisions 2026-03-04)
human_verification:
  - test: "Confirm RTLagreement.v retained blocks are intentional reference material (HYG-02)"
    expected: "4 comment blocks (RTL_STRONG_AGREEMENT, agree_forever_silent, strong_agreement_implies_weak_agreement, AGREEMENT_PRESERVATION) are legitimate design-history reference, not dead code that should be removed"
    why_human: "The RESEARCH.md classified these as DELETE candidates. The plans recorded a user-approved decision to retain them. Verification requires human judgment that the retention decision was correct and the blocks serve ongoing value as reference material."
  - test: "Confirm RTLtmr.v retained blocks are intentional reference material (HYG-03)"
    expected: "2 comment blocks (can_replicate_instr ~lines 161-175 and old transf_instr ~lines 225-281) are legitimate reference material, not dead drafts that should be removed"
    why_human: "Same situation as HYG-02. RESEARCH.md recommended DELETE; plans recorded user-approved KEEP decision. Human must confirm the retention is correct."
  - test: "Confirm RTLcolorcheck.v retained blocks are intentional (HYG-05)"
    expected: "3 comment blocks (old res-based check_col_instr, old smove checker, completeness stubs) are legitimate reference material"
    why_human: "Same pattern. RESEARCH.md recommended DELETE; plans recorded user-approved KEEP decision."
  - test: "Confirm Novotes.v retained blocks are intentional (HYG-06)"
    expected: "2 comment blocks (old res-based check_function/check_fundef/check_program) are legitimate reference material"
    why_human: "Same pattern. RESEARCH.md recommended DELETE; plans recorded user-approved KEEP decision."
  - test: "Confirm Complements.v full-retention is intentional (HYG-04)"
    expected: "All 6 comment blocks retained (not just the 2 design-note sketches the requirement named); the full retention is an accepted scope change from the requirement's original 'keep 2, delete 4' intent"
    why_human: "HYG-04 originally said 'keep distilled design notes for vote-parametric RTL->Asm sketch and asm weak-agreement sketch; delete other stubs'. All 6 blocks were retained. This is a scope change that requires human confirmation it is acceptable."
---

# Phase 05: Comment and Tactic Hygiene — Verification Report

**Phase Goal:** Remove abandoned proof blocks, resolve all TODO markers, align naming
**Verified:** 2026-03-04T16:30:00Z
**Status:** human_needed
**Re-verification:** No — initial verification

---

## Goal Achievement

### Observable Truths

| # | Truth | Status | Evidence |
|---|-------|--------|----------|
| 1 | RTLtolerant.v has no remaining commented-out abandoned proof blocks | VERIFIED | 10 blocks (~217 lines) removed in commit 88e5550e; grep for commented Lemma/Proof/Definition patterns returns 0 matches |
| 2 | RTLagreement.v comment blocks intentionally retained (user-approved) | HUMAN NEEDED | 4 blocks confirmed present; user decision documented in commit cc4756f6 and plan frontmatter — requires human to validate decision quality |
| 3 | TODO at RTLtolerant.v:~1344 converted to design note | VERIFIED | "Note: The four cases below are structurally identical modulo the type argument to [vote]..." present at line 1147 |
| 4 | TODO at RTLagreement.v:~137 converted to design note | VERIFIED | "Design note: An alternative approach would be to remove no_votes at the C level..." present at line 137 |
| 5 | RTLtmr.v comment blocks retained (user-approved) | HUMAN NEEDED | 2 blocks confirmed present (can_replicate_instr at line 161, old transf_instr at line 229); user decision documented in plan 02 frontmatter |
| 6 | Complements.v comment blocks retained (user-approved) | HUMAN NEEDED | All 6 blocks confirmed present (compiled_rtl_safe x2, compiled_rtl_weak_agreement, compiled_asm_weak_agreement, etc.); user decision documented in commit 7fdee6e6 |
| 7 | RTLcolorcheck.v comment blocks retained (user-approved) | HUMAN NEEDED | Blocks confirmed present (old res-based check_col_instr, completeness stubs); user decision documented in plan 03 frontmatter |
| 8 | Novotes.v comment blocks retained (user-approved) | HUMAN NEEDED | Blocks confirmed present (old res-based check_function/check_program); user decision documented in plan 03 frontmatter |
| 9 | RTLfault.v dead idfg block removed, design note preserved | VERIFIED | Dead block gone (9 lines removed in commit 0f61c2f8); "Technically we could/should allow faults..." design note at line 50 confirmed present |
| 10 | All in-scope TODO markers resolved (excluding user-retained blocks) | VERIFIED | grep for "TODO" in backend/ and driver/ *.v *.ml files (excluding CSEproof.v, Unusedglobproof.v, RTLtmr.v, RTLcolorcheck.v, RTLinfercolor.ml, Novotes.v) returns zero hits |
| 11 | maj_vote_regR_star_step renamed to maj_vote_regsR_star_step in RTLtmrproof.v | VERIFIED | Old name returns 0 hits; new name maj_vote_regsR_star_step returns exactly 9 hits (1 definition at line 789, 8 call sites at lines 1866, 1932, 1986, 2033, 2117, 2201, 2244, 2312) |
| 12 | No Admitted proofs introduced in any modified file | VERIFIED | grep for "^\s*Admitted" across all 6 modified files returns zero hits |
| 13 | RTL.v TODO markers converted to design notes | VERIFIED | "Design note: maybe we can just assume faulted floats aren't NaN..." at line 895; "Also: this might need to go into backend specific Op.v..." at line 903 (both "TODO:" prefixes removed) |
| 14 | Novotesproof.v TODO converted to design note | VERIFIED | "Note: The 8 cases below follow a near-identical pattern..." at line 51; full Phase 4 abandonment rationale documented |

**Score:** 9 directly verified, 5 require human judgment on user-approved retention decisions

---

### Required Artifacts

| Artifact | Expected | Status | Details |
|----------|----------|--------|---------|
| `backend/RTLtolerant.v` | Cleaned proof file, no dead comment blocks | VERIFIED | Contains match_rs_upto_fault; 10 dead blocks removed; no TODO; no Admitted |
| `backend/RTLagreement.v` | Comment blocks retained, TODO converted | VERIFIED (content); HUMAN (retention decision) | Contains weak_agreement; TODO converted to Design note at line 137 |
| `backend/RTLtmr.v` | Comment blocks retained per user review | VERIFIED (exists + content); HUMAN (retention decision) | Contains transf_instr at line 179 |
| `driver/Complements.v` | Comment blocks retained per user review | VERIFIED (exists + content); HUMAN (full-retention scope change) | Contains transf_c_program_to_rtl_preservation_faulty at line 546 |
| `backend/RTLcolorcheck.v` | Comment blocks retained per user review | VERIFIED (exists + content); HUMAN (retention decision) | Contains check_col_instr_sound at line 574 |
| `backend/Novotes.v` | Comment blocks retained per user review | VERIFIED (exists + content); HUMAN (retention decision) | Contains check_program at line 33 |
| `backend/RTLfault.v` | Dead block removed, design note preserved | VERIFIED | Contains maybe_zap at line 63; idfg block removed; design note at line 50 preserved |
| `backend/RTLtmrproof.v` | maj_vote_regsR_star_step present (9 occurrences) | VERIFIED | All 9 occurrences confirmed; old name fully eliminated |
| `backend/RTL.v` | TODO prefixes removed, design notes remain | VERIFIED | Lines 895 and 903 converted from TODO to design notes |
| `backend/Novotesproof.v` | TODO converted to Phase-4-rationale design note | VERIFIED | Line 51 has "Note: The 8 cases below follow a near-identical pattern..." |

---

### Key Link Verification

| From | To | Via | Status | Details |
|------|----|-----|--------|---------|
| backend/RTLtolerant.v | Coq build | make backend/RTLtolerant.vo | VERIFIED | Commit 88e5550e documents clean build; no structural code removed |
| backend/RTLagreement.v | Coq build | make backend/RTLagreement.vo | VERIFIED | Commit 32b59eeb documents clean build; only comment wording changed |
| backend/RTLtmrproof.v | RTLtmrspec.v | lemma name matching spec name maj_vote_regsR | VERIFIED | RTLtmrspec.v defines maj_vote_regsR at lines 55-64; RTLtmrproof.v uses maj_vote_regsR_star_step (matching plural "regs") at all 9 sites |
| backend/RTLfault.v | Coq build | make backend/RTLfault.vo | VERIFIED | Commit 0f61c2f8 documents clean build after idfg block removal |
| backend/RTLtmrproof.v | Coq build | make backend/RTLtmrproof.vo | VERIFIED | Commit 5e9443ce documents clean build after rename |
| All modified files | Full proof suite | make proof -j$(nproc) | VERIFIED (per SUMMARY) | 05-03-SUMMARY.md reports "Full `make proof -j$(nproc)` passes, `make check-admitted` returns 'Nothing admitted.'" — human re-run required to confirm |

---

### Requirements Coverage

| Requirement | Source Plan | Description | Status | Evidence |
|-------------|-------------|-------------|--------|----------|
| HYG-01 | 05-01 | Large commented-out abandoned proof blocks removed from RTLtolerant.v | VERIFIED | 10 blocks removed in commit 88e5550e; verified by grep — 0 commented-out Lemma/Proof patterns remain |
| HYG-02 | 05-01 | Large commented-out blocks removed from RTLagreement.v | HUMAN NEEDED | Blocks retained by user-approved decision (commit cc4756f6); 4 blocks still present; REQUIREMENTS.md checked as complete |
| HYG-03 | 05-02 | Commented-out blocks removed from RTLtmr.v | HUMAN NEEDED | Blocks retained by user-approved decision; 2 blocks still present; REQUIREMENTS.md checked as complete |
| HYG-04 | 05-02 | Commented-out blocks removed from driver/Complements.v (keep 2 design notes, delete others) | HUMAN NEEDED | All 6 blocks retained (not just the 2 the requirement named); full-retention scope change; REQUIREMENTS.md checked as complete |
| HYG-05 | 05-03 | Commented-out blocks removed from RTLcolorcheck.v | HUMAN NEEDED | Blocks retained by user-approved decision; 3 blocks still present; REQUIREMENTS.md checked as complete |
| HYG-06 | 05-03 | Commented-out blocks removed from Novotes.v | HUMAN NEEDED | Blocks retained by user-approved decision; 2 blocks still present; REQUIREMENTS.md checked as complete |
| HYG-07 | 05-03 | Commented-out blocks removed from RTLfault.v | VERIFIED | 1 dead block (idfg lemma) removed in commit 0f61c2f8; design note preserved |
| HYG-08 | 05-01, 05-03 | All TODO markers in in-scope files resolved or removed | VERIFIED | grep "TODO" across backend/ driver/ (excluding approved exceptions) returns 0 hits; all 9 catalogued TODOs accounted for |
| HYG-09 | 05-03 | Naming conventions aligned between DMR and TMR helper functions | VERIFIED | maj_vote_regR_star_step renamed to maj_vote_regsR_star_step; old name has 0 hits; new name has 9 hits in RTLtmrproof.v; aligns with RTLtmrspec.v spec name |

**Orphaned requirements:** None. All 9 HYG-01 through HYG-09 appear in plan frontmatter and are accounted for.

---

### Anti-Patterns Found

| File | Pattern | Severity | Assessment |
|------|---------|----------|------------|
| backend/RTLagreement.v | 4 multi-line commented-out proof blocks still present | Info | User-approved retention decision documented in plans and commits; not an accidental omission |
| backend/RTLtmr.v | 2 multi-line commented-out proof blocks still present | Info | Same — user-approved retention |
| driver/Complements.v | 6 multi-line commented-out proof blocks still present | Info | Scope change from "keep 2, delete 4" to "keep all 6" — needs human confirmation |
| backend/RTLcolorcheck.v | 3 multi-line commented-out proof blocks still present | Info | User-approved retention |
| backend/Novotes.v | 2 multi-line commented-out proof blocks still present | Info | User-approved retention |

No blockers found. The retained blocks all appear inside `(* ... *)` delimiters and cannot affect Coq compilation. The concern is governance (were the retention decisions correct), not functionality.

---

### Human Verification Required

#### 1. RTLagreement.v Block Retention (HYG-02)

**Test:** Open `backend/RTLagreement.v` and review the 4 commented-out blocks: `RTL_STRONG_AGREEMENT` (lines 18-70), `weak_agreement'` definition (line 89), `agree_forever_silent` + `strong_agreement_implies_weak_agreement` (lines 96-122), and `AGREEMENT_PRESERVATION` (lines 163-204).

**Expected:** These blocks constitute legitimate historical reference for the design evolution from strong-agreement to weak-agreement. They help future maintainers understand why the current weak-agreement approach was chosen over the stronger formulation.

**Why human:** The RESEARCH.md classified all 4 as DELETE candidates (superseded dead drafts). The plans changed this to KEEP based on a user review decision. Only the original reviewer can confirm that decision was correct.

#### 2. RTLtmr.v Block Retention (HYG-03)

**Test:** Open `backend/RTLtmr.v` and review blocks at lines ~161-175 (`can_replicate_instr` with embedded TODO) and ~225-281 (old `transf_instr` definition with embedded TODO at line 238).

**Expected:** Both blocks are kept as reference for the design evolution of the instruction replication logic.

**Why human:** RESEARCH.md recommended DELETE (both superseded by active transf_instr). Plans changed to KEEP. Note: the embedded TODOs at lines 168 and 238 remain, meaning the "no TODO markers" goal is not achieved for this file — but this was explicitly scoped out in plan 03's verification clause which excluded RTLtmr.v from the grep check.

#### 3. Complements.v Full Retention vs. Selective Retention (HYG-04)

**Test:** Open `driver/Complements.v` and review whether the "delete" candidates (lines ~137-248 compiled_rtl_safe drafts, lines ~280-308 weak_agreement + idfg stubs, lines ~572-584 old proof ending + empty Section VOTE) were actually deleted or retained.

**Expected per original requirement:** Delete the 4 "delete" blocks; keep the 2 design-sketch blocks (vote-parametric forward-sim at lines 74-114 and asm weak-agreement at lines 586-639).

**Actual state:** All 6 blocks retained. The SUMMARY for plan 02 claims "Complements.v comment blocks (6 blocks, ~256 lines) kept as intentional reference material per user review."

**Why human:** The requirement (HYG-04) had a specific two-tier directive: keep 2 specific design notes, delete 4 stubs. The execution kept all 6. This is the most concrete gap between requirement intent and delivered state. Human must confirm this is an acceptable scope change.

#### 4. RTLcolorcheck.v Block Retention (HYG-05)

**Test:** Open `backend/RTLcolorcheck.v` and review the old res-based `check_col_instr` block (~lines 78-118), old smove checker (~lines 173-188), and completeness stubs (~lines 619-631).

**Expected:** Retained as reference for the bool-vs-res design decision.

**Why human:** RESEARCH.md recommended DELETE; plans changed to KEEP. Note that line 649-650 "check_function_complete not possible because..." design note is correctly kept in both plans.

#### 5. Novotes.v Block Retention (HYG-06)

**Test:** Open `backend/Novotes.v` and review blocks at lines ~24-29 (old res-based `check_function`) and ~42-47 (old `check_fundef` + `check_program`).

**Expected:** Retained as reference for the bool-vs-res design decision parallel to RTLcolorcheck.v.

**Why human:** RESEARCH.md recommended DELETE; plans changed to KEEP.

#### 6. Full Proof Suite Re-run (optional but recommended)

**Test:** Run `make proof -j$(nproc) && make check-admitted` from `/home/alex/source/compcert`.

**Expected:** Build succeeds with zero errors and zero Admitted proofs.

**Why human:** The SUMMARY reports this passed at plan execution time, but no independent post-execution build verification exists in the verification trail. The proof suite takes ~120 seconds.

---

## Summary

### What Was Definitively Achieved

- **HYG-01 (RTLtolerant.v)**: 10 dead proof blocks (~217 lines) removed. Clean. No TODO. No Admitted. Commit 88e5550e.
- **HYG-07 (RTLfault.v)**: Dead idfg lemma block removed. Design note preserved. Commit 0f61c2f8.
- **HYG-08 (TODO resolution)**: All 9 catalogued in-scope TODO markers accounted for. RTLtolerant.v, RTLagreement.v, RTL.v, Novotesproof.v TODOs converted to design notes. TODOs inside user-retained blocks (RTLtmr.v, RTLinfercolor.ml) correctly excluded. Zero TODO hits across all non-excepted files.
- **HYG-09 (Naming alignment)**: maj_vote_regR_star_step renamed to maj_vote_regsR_star_step across all 9 occurrences in RTLtmrproof.v. Aligns with RTLtmrspec.v canonical name. Commit 5e9443ce.

### What Requires Human Judgment

HYG-02, HYG-03, HYG-04, HYG-05, HYG-06 all involved user-approved decisions to **retain** comment blocks that the RESEARCH.md and original REQUIREMENTS.md intended to be **removed**. The REQUIREMENTS.md traceability table marks all five as "Complete," indicating the project owner accepted the outcome. However, since the delivered state differs from the literal requirement text ("removed from"), human confirmation is needed that:

1. The retained blocks constitute legitimate reference material (not laziness or oversight).
2. For HYG-04 specifically: the scope change from "keep 2, delete 4" to "keep all 6" is intentional.
3. The embedded TODOs in RTLtmr.v (lines 168 and 238) inside the retained blocks are acceptable exceptions to the "no TODO" goal.

The automated record is clear: these retention decisions were made deliberately, documented in three git commits before execution, and reflected in the plan frontmatter. The human judgment required is whether those decisions were correct, not whether they were made.

---

_Verified: 2026-03-04T16:30:00Z_
_Verifier: Claude (gsd-verifier)_
