---
phase: 06-pipeline-simplification
verified: 2026-03-05T17:00:07Z
status: passed
score: 4/4 must-haves verified
re_verification: false
---

# Phase 6: Pipeline Simplification Verification Report

**Phase Goal:** Compiler.v no longer applies Novotes.transf_program in either transf_rtl_program or transf_rtl_program_to_rtl, and all pass-match/correctness lemmas in Compiler.v still compile
**Verified:** 2026-03-05T17:00:07Z
**Status:** passed
**Re-verification:** No -- initial verification

## Goal Achievement

### Observable Truths

| # | Truth | Status | Evidence |
|---|-------|--------|----------|
| 1 | transf_rtl_program in Compiler.v does not mention Novotes.transf_program | VERIFIED | `grep -c "Novotes.transf_program" driver/Compiler.v` returns 0; definition ends at `Unusedglob.transform_program.` on line 174 |
| 2 | transf_rtl_program_to_rtl in Compiler.v does not mention Novotes.transf_program | VERIFIED | `grep -c "Novotes.transf_program" driver/Compiler.v` returns 0; definition ends at `Unusedglob.transform_program.` on line 227 |
| 3 | Compiler.vo compiles successfully with zero Admitted | VERIFIED | Compiler.vo exists (timestamp 1772729703), newer than Compiler.v (1772729691); `grep -n "Admitted" driver/Compiler.v` returns no matches |
| 4 | Complements.vo compiles successfully (match proofs adjusted, unused no_votes lemmas deleted) | VERIFIED | Complements.vo exists (timestamp 1772729778), newer than Complements.v (1772729760); only Admitted is pre-existing `transf_c_program_to_rtl_preservation_faulty` at line 513 (Phase 7 scope) |

**Score:** 4/4 truths verified

### Required Artifacts

| Artifact | Expected | Status | Details |
|----------|----------|--------|---------|
| `driver/Compiler.v` | Pipeline definitions and match/correctness proofs without Novotes pass | VERIFIED | Contains `transf_rtl_program` (both variants), zero active Novotes references, no Admitted, .vo compiles |
| `driver/Complements.v` | Match proofs cleaned of Novotes; unused no_votes lemmas deleted | VERIFIED | `transf_c_to_rtl_match_prog` proof ends at Unusedglob (line 331 `inv T`), deleted lemmas confirmed absent (grep count 0 for both `transf_c_program_to_rtl'_no_votes` and `transf_c_program_to_rtl'_preservation'`) |

### Key Link Verification

| From | To | Via | Status | Details |
|------|----|-----|--------|---------|
| `driver/Compiler.v` | `backend/Unusedglob.v` | Unusedglob is now last RTL optimization pass (no Novotes after) | WIRED | Line 174: `transf_rtl_program` terminates with `Unusedglob.transform_program.`; Line 227: `transf_rtl_program_to_rtl` terminates with `Unusedglob.transform_program.`; next step in full pipeline is `transf_rtl_program'` (DMR/TMR), confirming Novotes is absent from the chain |

### Requirements Coverage

| Requirement | Source Plan | Description | Status | Evidence |
|-------------|------------|-------------|--------|----------|
| PIPE-01 | 06-01-PLAN.md | Remove Novotes.transf_program from transf_rtl_program in Compiler.v | SATISFIED | Definition on lines 157-174 has no Novotes; ends at Unusedglob |
| PIPE-02 | 06-01-PLAN.md | Remove Novotes.transf_program from transf_rtl_program_to_rtl in Compiler.v | SATISFIED | Definition on lines 209-227 has no Novotes; ends at Unusedglob |
| PIPE-03 | 06-01-PLAN.md | Update pass-match and correctness proofs in Compiler.v for simplified pipeline | SATISFIED | `transf_c_program_match` (line 377), `transf_c_program_to_rtl_match` (line 443), `cstrategy_semantic_preservation` (line 529), `cstrategy_semantic_preservation_rtl` (line 605) all compile with Novotes steps removed; no Require Novotes or Require Novotesproof imports remain |

No orphaned requirements -- REQUIREMENTS.md maps exactly PIPE-01, PIPE-02, PIPE-03 to Phase 6, all claimed by 06-01-PLAN.md.

### Anti-Patterns Found

| File | Line | Pattern | Severity | Impact |
|------|------|---------|----------|--------|
| `driver/Compiler.v` | 330, 358, 429, 487, 573, 643 | Commented-out Novotes references `(* ... Novotesproof ... *)` | Info | Harmless comments serving as historical markers; not active code |
| `driver/Complements.v` | 130, 173, 230, 393, 572, 574 | Commented-out Novotes references in legacy code blocks | Info | All inside large commented-out sections (`(* ... *)`); no active code impact |
| `driver/Complements.v` | 513 | `Admitted.` for `transf_c_program_to_rtl_preservation_faulty` | Info | Pre-existing; explicitly Phase 7 scope (THERM-01). Not introduced by this phase |

No blockers or warnings found.

### Human Verification Required

None. All truths are programmatically verifiable via grep, file existence, and timestamp checks. The Coq type checker (which produced the .vo files) provides stronger guarantees than human review for proof correctness.

### Gaps Summary

No gaps found. All four must-have truths are verified. Both pipeline definitions terminate at Unusedglob with no Novotes step. Both .vo files compile successfully. The deleted lemmas (`transf_c_program_to_rtl'_no_votes` and `transf_c_program_to_rtl'_preservation'`) are confirmed absent. No active Novotes imports remain. Commits `1966bc6a` and `14607078` are verified in git history.

---

_Verified: 2026-03-05T17:00:07Z_
_Verifier: Claude (gsd-verifier)_
