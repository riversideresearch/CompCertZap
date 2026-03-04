---
phase: 03-spec-strengthening
verified: 2026-03-04T00:00:00Z
status: passed
score: 10/10 must-haves verified
re_verification: false
---

# Phase 3: Spec Strengthening Verification Report

**Phase Goal:** The monolithic replication_map_wf_aux proofs in both spec files are replaced by a relational spec that separates algorithmic correctness from invariant consequences
**Verified:** 2026-03-04
**Status:** passed
**Re-verification:** No — initial verification

## Goal Achievement

### Observable Truths

| #  | Truth                                                                                    | Status     | Evidence                                                                                      |
|----|------------------------------------------------------------------------------------------|------------|-----------------------------------------------------------------------------------------------|
| 1  | RTLdmrspec.v defines `replication_map_rel` inductive with `rmr_nil` and `rmr_cons`      | VERIFIED   | Line 813: `Inductive replication_map_rel : list reg -> PMap.t reg -> positive -> positive -> Prop` with both constructors present |
| 2  | RTLtmrspec.v defines `replication_map_rel` inductive (TMR arity: pairs) with `rmr_nil` and `rmr_cons` | VERIFIED | Line 931: `Inductive replication_map_rel : list reg -> PMap.t (reg * reg) -> positive -> positive -> Prop`; `rmr_cons` uses `(mid, Pos.succ mid)` and advances by 2 |
| 3  | `foldM_satisfies_rel` defined and used in both spec files                                | VERIFIED   | RTLdmrspec.v line 857 (definition), line 985 (used in `replication_map_wf`); RTLtmrspec.v line 991 (definition), line 1173 (used) |
| 4  | `rel_implies_rm_wf` defined and used in both spec files                                  | VERIFIED   | RTLdmrspec.v line 919 (definition), line 984 (used); RTLtmrspec.v line 1077 (definition), line 1172 (used) |
| 5  | Monolithic `replication_map_wf_aux` absent from RTLdmrspec.v                            | VERIFIED   | grep count = 0; commit `bfd54aee` deleted ~102-line monolithic proof |
| 6  | Monolithic `replication_map_wf_aux` absent from RTLtmrspec.v                            | VERIFIED   | grep count = 0; commit `26748e39` deleted ~128-line monolithic proof |
| 7  | `replication_map_wf` in RTLdmrspec.v: type signature unchanged, proof uses composition  | VERIFIED   | Line 979-990: signature `f rm s pf -> replication_map f (init_state f) = RTLgen.OK rm s pf -> rm_wf rm (fun_regs_list f)` matches plan exactly; proof calls `eapply rel_implies_rm_wf` then `eapply foldM_satisfies_rel` |
| 8  | `replication_map_wf` in RTLtmrspec.v: type signature unchanged, proof uses composition  | VERIFIED   | Line 1167-1178: identical structure to DMR; proof composes `rel_implies_rm_wf` and `foldM_satisfies_rel` |
| 9  | RTLdmrproof.v compiles against new interface (no Admitted)                               | VERIFIED   | `RTLdmrproof.vo` timestamp 19:46:02 matches commit `bfd54aee` at 19:46:36; zero Admitted in file |
| 10 | RTLtmrproof.v compiles against new interface (no Admitted)                               | VERIFIED   | `RTLtmrproof.vo` timestamp 19:57:05 matches commit `26748e39` at 19:57:29; zero Admitted in file |

**Score:** 10/10 truths verified

### Required Artifacts

| Artifact                        | Expected                                              | Status     | Details                                                                              |
|---------------------------------|-------------------------------------------------------|------------|--------------------------------------------------------------------------------------|
| `backend/RTLdmrspec.v`          | Relational spec + decomposed proof for DMR            | VERIFIED   | 25 occurrences of `replication_map_rel`; all key lemmas present; no `Admitted`       |
| `backend/RTLtmrspec.v`          | Relational spec + decomposed proof for TMR            | VERIFIED   | 35 occurrences of `replication_map_rel`; all key lemmas present; no `Admitted`       |
| `backend/RTLdmrspec.vo`         | Compiled Coq object (proof passes type-checker)       | VERIFIED   | File exists, 485 KB, timestamp consistent with source commits                        |
| `backend/RTLtmrspec.vo`         | Compiled Coq object (proof passes type-checker)       | VERIFIED   | File exists, 689 KB, timestamp consistent with source commits                        |
| `backend/RTLdmrproof.vo`        | Proof file unchanged, compiles against new spec       | VERIFIED   | File exists, 431 KB, timestamp consistent with source commits                        |
| `backend/RTLtmrproof.vo`        | Proof file unchanged, compiles against new spec       | VERIFIED   | File exists, 762 KB, timestamp consistent with source commits                        |

### Key Link Verification

| From                                          | To                                                      | Via                                      | Status   | Details                                                                                                 |
|-----------------------------------------------|---------------------------------------------------------|------------------------------------------|----------|---------------------------------------------------------------------------------------------------------|
| `RTLdmrspec.v (replication_map_wf)`           | `foldM_satisfies_rel` + `rel_implies_rm_wf`             | composition in Proof block               | WIRED    | Line 984: `eapply rel_implies_rm_wf`; line 985: `eapply foldM_satisfies_rel` — both called in 3-line proof |
| `RTLtmrspec.v (replication_map_wf)`           | `foldM_satisfies_rel` + `rel_implies_rm_wf`             | composition in Proof block               | WIRED    | Line 1172: `eapply rel_implies_rm_wf`; line 1173: `eapply foldM_satisfies_rel` — same pattern           |
| `RTLdmrproof.v`                               | `RTLdmrspec.v`                                          | `Require Import RTLdmrspec.`             | WIRED    | Line 4 of RTLdmrproof.v; proof file compiled successfully against new interface                          |
| `RTLtmrproof.v`                               | `RTLtmrspec.v`                                          | `Require Import RTLtmrspec.`             | WIRED    | Line 4 of RTLtmrproof.v; proof file compiled successfully against new interface                          |

### Requirements Coverage

| Requirement | Source Plan    | Description                                                                      | Status    | Evidence                                                                                         |
|-------------|---------------|----------------------------------------------------------------------------------|-----------|--------------------------------------------------------------------------------------------------|
| SPEC-01     | 03-01-PLAN.md | Relational spec defined for DMR replication-map construction in RTLdmrspec.v     | SATISFIED | `Inductive replication_map_rel` at line 813 with `rmr_nil`/`rmr_cons`; 25 occurrences            |
| SPEC-02     | 03-02-PLAN.md | Relational spec defined for TMR replication-map construction in RTLtmrspec.v     | SATISFIED | `Inductive replication_map_rel` at line 931 with pair arity; 35 occurrences                      |
| SPEC-03     | 03-01-PLAN.md | Monolithic `replication_map_wf_aux` in RTLdmrspec.v replaced with composition   | SATISFIED | Zero occurrences of `replication_map_wf_aux` in RTLdmrspec.v; `replication_map_wf` re-proved    |
| SPEC-04     | 03-02-PLAN.md | Monolithic `replication_map_wf_aux` in RTLtmrspec.v replaced with composition   | SATISFIED | Zero occurrences of `replication_map_wf_aux` in RTLtmrspec.v; `replication_map_wf` re-proved    |

All four requirements are SATISFIED. No orphaned requirements — REQUIREMENTS.md maps SPEC-01 through SPEC-04 exclusively to Phase 3, and all are covered by the two plans.

### Anti-Patterns Found

| File                      | Line | Pattern        | Severity | Impact |
|---------------------------|------|----------------|----------|--------|
| None found                | —    | —              | —        | —      |

- Zero `Admitted` proofs in RTLdmrspec.v, RTLtmrspec.v, RTLdmrproof.v, RTLtmrproof.v
- Zero TODO/FIXME markers in either spec file (the TODO comment addressed in plan was removed per commit `6b8028e5` and `1adced11`)
- No placeholder implementations detected

### Human Verification Required

None. All checks are programmatically verifiable:
- Existence of inductive definitions confirmed by grep
- Absence of monolithic proof confirmed by grep (count = 0)
- Type signatures of `replication_map_wf` match plan specification exactly
- Compiled `.vo` files exist with timestamps consistent with source commits
- Zero `Admitted` proofs across all four files

### Additional Observations

Both plans introduced helper lemmas beyond what was originally specified. These are substantive, not scope creep:

**DMR (03-01):**
- `replication_map_rel_set`: PMap.set stability — necessary for `foldM_satisfies_rel` induction step
- `replication_map_rel_injective`: shadow injectivity — needed for the `NoDup` goals in `rel_implies_rm_wf`
- `NoDup4_of_ranges`: generic 4-element NoDup from range separation
- `elements_NoDup`: NoDup from `Regset.elements_3w`

**TMR (03-02):**
- `replication_map_rel_consecutive`: `r3 = Pos.succ r2` for each pair — needed for NoDup6 cross-register proof
- `replication_map_rel_disjoint_shadows`: non-overlapping shadow intervals — provides full range separation for all 15 pairwise distinctness conditions in `NoDup [r1;r2;r3;r1';r2';r3']`

The deviation from the plan (adding `replication_map_rel_consecutive` and `replication_map_rel_disjoint_shadows` instead of using pair inequality alone) was a correct bug-fix: pair inequality only gives `r2 <> r2' \/ r3 <> r3'`, which is insufficient for 6-element NoDup. The stronger range-separation approach is sound.

### Gaps Summary

No gaps. All must-haves verified.

---

_Verified: 2026-03-04_
_Verifier: Claude (gsd-verifier)_
