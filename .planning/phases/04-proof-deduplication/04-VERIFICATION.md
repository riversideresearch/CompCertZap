---
phase: 04-proof-deduplication
verified: 2026-03-04T06:00:00Z
status: gaps_found
score: 3/5 success criteria verified
gaps:
  - truth: "Novotesproof.v: the 8-repeat no_votes_external_call case expansion is replaced by a lookup_builtin_not_vote helper lemma plus a concise driver"
    status: failed
    reason: "Deliberately abandoned due to Coq infinite memory consumption from repeat+destruct tactic. The 8-repeat proof remains unchanged (~170 lines, lines 62-222). TODO comment at line 51 persists. No lookup_builtin_not_vote helper exists."
    artifacts:
      - path: "backend/Novotesproof.v"
        issue: "no_votes_external_call proof is still ~170 lines with 8 repeat blocks and do N counting (do 8, do 9, do 10, do 11). TODO comment at line 51 not removed."
    missing:
      - "lookup_builtin_not_vote helper lemma (required by ROADMAP SC-1 and DEDUP-01)"
      - "Concise driver proof for no_votes_external_call"
      - "Removal of TODO comment at line 51"

  - truth: "RTLtmrproof.v: the four-type-case maj_voteR_step duplication is replaced by a single maj_voteR_step_of_type parametric lemma"
    status: partial
    reason: "Four-case duplication was collapsed into a single unified inline proof using first [...] dispatch (~39 lines, down from ~80). However, the ROADMAP Success Criterion specifies a named maj_voteR_step_of_type parametric lemma, which does not exist. The TODO comment was removed. The file compiles."
    artifacts:
      - path: "backend/RTLtmrproof.v"
        issue: "maj_voteR_step proof is deduplicated inline but no separate maj_voteR_step_of_type lemma exists (ROADMAP SC-2 requires this specific named helper)"
    missing:
      - "Named maj_voteR_step_of_type parametric lemma (required by ROADMAP SC-2)"

  - truth: "RTLtolerant.v: external_call_vote_lessdef four-case duplication is collapsed into a vote_lessdef_of_type helper"
    status: failed
    reason: "Deliberately abandoned due to Ltac hypothesis name instability across inversion chains. The four-case proof was reverted to original state (commit 2e16f1f7). The proof body remains ~132 lines with four identical cases (Tint/Tlong/Tsingle/Tfloat). TODO comment at line 1344 persists."
    artifacts:
      - path: "backend/RTLtolerant.v"
        issue: "external_call_vote_lessdef proof is still ~132 lines (lines 1353-1484) with four copy-paste branches. TODO comment at line 1344 persists. No vote_lessdef_of_type helper."
    missing:
      - "vote_lessdef_of_type helper lemma (required by ROADMAP SC-3 and DEDUP-03)"
      - "Removal of TODO comment at line 1344"
human_verification: []
---

# Phase 4: Proof De-duplication Verification Report

**Phase Goal:** Repeated proof patterns across four files are collapsed into parametric helpers, and the deprecated external_call_Three_Two lemma is removed after caller migration
**Verified:** 2026-03-04T06:00:00Z
**Status:** gaps_found
**Re-verification:** No — initial verification

## Context: Deliberate Abandonment Decisions

The user deliberately approved abandoning two of the five deduplication tasks during execution. This report records what was completed versus what the ROADMAP specifies. The gaps are factual deviations from the phase goal, not execution failures — they represent conscious cost-benefit decisions:

- **DEDUP-01 (Novotesproof.v)**: Abandoned — tactic caused infinite Coq memory consumption
- **DEDUP-03 (RTLtolerant.v vote_lessdef)**: Abandoned — Ltac hypothesis name instability across nested inversions
- **DEDUP-02 partial**: Collapsed to inline proof but no named parametric lemma as ROADMAP specifies

## Goal Achievement

### Observable Truths (from ROADMAP Success Criteria)

| # | Truth | Status | Evidence |
|---|-------|--------|----------|
| SC-1 | `no_votes_external_call` replaced by `lookup_builtin_not_vote` helper + driver, `make backend/Novotesproof.vo` succeeds | FAILED | 8-repeat proof unchanged (~170 lines), TODO at line 51 persists, no `lookup_builtin_not_vote` exists |
| SC-2 | `maj_voteR_step` duplication replaced by `maj_voteR_step_of_type` parametric lemma, `make backend/RTLtmrproof.vo` succeeds | PARTIAL | Inline proof consolidated to ~39 lines using `first [...]` dispatch; file compiles; but no separate named `maj_voteR_step_of_type` lemma |
| SC-3 | `external_call_Three_Two` absent + `external_call_vote_lessdef` collapsed into `vote_lessdef_of_type` helper, `make backend/RTLtolerant.vo` succeeds | PARTIAL | Deprecated lemma removed (DEDUP-04 satisfied); vote_lessdef dedup reverted — 4-case ~132-line proof remains, TODO at 1344 persists, no `vote_lessdef_of_type` |
| SC-4 | `check_col_instr_sound` split into per-instruction lemmas, `make backend/RTLcolorcheck.vo` succeeds | VERIFIED | 14 per-instruction lemmas extracted (lines 266-572); 21-line dispatcher (lines 574-597); commit cacc8821 |
| SC-5 | `make proof -j$(nproc)` and `make check-admitted` both pass cleanly | VERIFIED | Reported in 04-03-SUMMARY.md as passing; zero Admitted proofs found in all four modified files |

**Score:** 2.5/5 success criteria fully verified (SC-4, SC-5 complete; SC-3 half-satisfied due to DEDUP-04)

### Required Artifacts

| Artifact | Expected | Status | Details |
|----------|----------|--------|---------|
| `backend/RTLtolerant.v` | deprecated lemma removed + vote_lessdef deduped | PARTIAL | Deprecated lemma removed (commit ef156da2); vote_lessdef 4-case proof unchanged (~132 lines); TODO at line 1344 remains |
| `backend/Novotesproof.v` | no_votes_external_call collapsed to helper + driver | STUB | File exists and compiles; proof unchanged from pre-phase state; TODO at line 51 remains |
| `backend/RTLtmrproof.v` | maj_voteR_step collapsed to parametric lemma | PARTIAL | File exists, compiles (commit a5e935af), proof consolidated to ~39 lines; no named `maj_voteR_step_of_type` lemma |
| `backend/RTLcolorcheck.v` | check_col_instr_sound decomposed into per-instruction lemmas | VERIFIED | 14 named lemmas (check_col_Inop_sound, check_col_Iop_protected_sound, etc.); dispatcher is 21 lines; commit cacc8821 |

### Key Link Verification

| From | To | Via | Status | Details |
|------|----|-----|--------|---------|
| `check_col_instr_sound` | 14 per-instruction lemmas | `destruct instr; apply check_col_*_sound` | WIRED | Dispatcher at lines 578-596 calls each lemma; `check_col_instr_sound` used at line 616 |
| `maj_voteR_step` | `vote_sem_int_ok, vote_sem_float_ok, vote_sem_long_ok, vote_sem_single_ok` | `first [apply ...]` inline dispatch | WIRED | Lines 758-761; proof compiles |
| call sites in RTLtolerant.v | `external_call_Three_Two'` | `apply external_call_Three_Two' in Hext` | WIRED | Lines 1679, 1739, 1792, 1829 (and more); deprecated form absent |
| `external_call_vote_lessdef` | `lessdef_vote3_vote, lessdef_vote3_vote', lessdef_vote3_vote''` | 4 repeated case blocks | WIRED (but un-deduped) | Lines 1369-1483; all four cases call through; dedup was the goal |
| `no_votes_external_call` | `Builtins.lookup_builtin_function` | 8-repeat `do N` destruct chains | WIRED (but un-deduped) | Lines 77, 95, 113, 131, 156, 174, 192, 210; proof works but dedup was goal |

### Requirements Coverage

| Requirement | Source Plan | Description | Status | Evidence |
|-------------|------------|-------------|--------|---------|
| DEDUP-01 | 04-02 | `no_votes_external_call` refactored from 8 repeats to helper lemma + driver | NOT SATISFIED | Proof unchanged; REQUIREMENTS.md shows checkbox unchecked; plan SUMMARY documents abandonment |
| DEDUP-02 | 04-02 | `maj_voteR_step` refactored from four-case to parametric lemma | PARTIALLY SATISFIED | Inline proof consolidated (no separate parametric lemma); plan marks DEDUP-02 as completed but ROADMAP SC-2 requires named lemma; REQUIREMENTS.md shows checkbox unchecked |
| DEDUP-03 | 04-01 | `external_call_vote_lessdef` refactored from four identical cases to type-parametric lemma | NOT SATISFIED | Proof reverted to 4-case form; REQUIREMENTS.md shows checkbox unchecked; plan SUMMARY documents abandonment |
| DEDUP-04 | 04-01 | Deprecated `external_call_Three_Two` removed after migrating call sites | SATISFIED | Confirmed absent from RTLtolerant.v; only `external_call_Three_Two'` remains; commit ef156da2; REQUIREMENTS.md shows checkbox checked |
| DEDUP-05 | 04-03 | `check_col_instr_sound` broken into per-instruction lemmas | SATISFIED | 14 per-instruction lemmas (check_col_Inop_sound through check_col_Ireturn_sound); 21-line dispatcher; commit cacc8821; REQUIREMENTS.md shows checkbox checked |

**Note on REQUIREMENTS.md tracking state:** The REQUIREMENTS.md file still shows DEDUP-01, DEDUP-02, DEDUP-03 checkboxes as unchecked (`[ ]`), accurately reflecting that these were not completed. DEDUP-04 and DEDUP-05 are checked. The tracking is correct.

### Anti-Patterns Found

| File | Line | Pattern | Severity | Impact |
|------|------|---------|----------|--------|
| `backend/RTLtolerant.v` | 1344 | `(* TODO: the four cases in this proof are literally the same... *)` | Warning | Documents unresolved duplication in external_call_vote_lessdef; DEDUP-03 was specifically supposed to resolve this |
| `backend/Novotesproof.v` | 51 | `(* TODO: cleanup. This proof is 8 repeats of almost the same proof script. *)` | Warning | Documents unresolved duplication in no_votes_external_call; DEDUP-01 was specifically supposed to resolve this |
| `backend/RTLcolorcheck.v` | 117 | `assert false "TODO"` | Info | Inside commented-out OCaml extraction block; not an active proof concern |

### Human Verification Required

None — all findings are programmatically verifiable. The `make proof` and `make check-admitted` results from 04-03-SUMMARY.md are trusted based on the zero Admitted proofs confirmed in the four modified files.

### Gaps Summary

Phase 4 achieved partial goal completion. Two of the five ROADMAP success criteria are fully satisfied (SC-4: RTLcolorcheck decomposition; SC-5: full suite passes). One is half-satisfied (SC-3: deprecated lemma removal done, but vote_lessdef dedup abandoned). Two are not satisfied (SC-1: Novotesproof unchanged; SC-2: maj_voteR_step inline consolidation done but no named parametric lemma as required).

The root causes were all Coq proof automation limitations:
- Infinite memory: `repeat+destruct (string_dec _ _ && signature_eq _ _)` causes exponential search space in Novotesproof.v
- Hypothesis name instability: `inv` tactic generates context-dependent names across the four branches in external_call_vote_lessdef, making robust Ltac automation impractical

**What the phase goal required vs what was delivered:**

The phase goal stated: "Repeated proof patterns across four files are collapsed into parametric helpers"

- RTLtolerant.v: deprecated lemma removed (done), vote_lessdef NOT collapsed
- Novotesproof.v: no_votes_external_call NOT collapsed
- RTLtmrproof.v: maj_voteR_step consolidated inline (done, substantively), no named parametric lemma (gap from ROADMAP spec)
- RTLcolorcheck.v: check_col_instr_sound fully decomposed (done)

**Two TODO comments remain** from tasks that were completed (DEDUP-04 TODO was removed correctly), but two others from abandoned tasks were not removed:
- `backend/RTLtolerant.v:1344` — vote_lessdef TODO
- `backend/Novotesproof.v:51` — no_votes_external_call TODO

These TODO comments will be visible to Phase 5 (Comment and Tactic Hygiene), which targets TODO resolution.

---

_Verified: 2026-03-04T06:00:00Z_
_Verifier: Claude (gsd-verifier)_
