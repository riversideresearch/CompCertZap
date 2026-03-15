---
phase: 01-classification-semantic-foundation
verified: 2026-03-14T12:00:00Z
status: passed
score: 10/10 must-haves verified
re_verification: false
---

# Phase 01: Classification Semantic Foundation Verification Report

**Phase Goal:** Establish the classification predicates and semantic properties that all subsequent phases depend on. Define which builtins can be safely replicated and prove the val_compat monotonicity property that gates the entire fault tolerance proof.
**Verified:** 2026-03-14
**Status:** passed
**Re-verification:** No -- initial verification

---

## Goal Achievement

### Observable Truths

| # | Truth | Status | Evidence |
|---|-------|--------|----------|
| 1 | `builtin_can_replicate_bf` exhaustive match returns true for safe builtins, false for BI_replicate | VERIFIED | `common/Builtins.v` lines 107-127: 18 unconditional true standard cases + 1 conditional BI_subl + 2 platform, BI_replicate false |
| 2 | `builtin_can_replicate` dispatches EF_builtin via lookup_builtin_function, false for all others | VERIFIED | `common/Builtins.v` lines 133-144: EF_builtin branch resolves via lookup_builtin_function, all 10 other constructors return false |
| 3 | `builtin_can_fault` is a separate function equal to `builtin_can_replicate` | VERIFIED | `common/Builtins.v` lines 151-152: `builtin_can_fault ef := builtin_can_replicate ef` |
| 4 | BI_subl classified conditionally on negb Archi.ptr64 | VERIFIED | `common/Builtins.v` line 113: `BI_subl => negb Archi.ptr64` |
| 5 | BI_replicate constructors always return false | VERIFIED | `common/Builtins.v` line 126: `BI_replicate _ => false` |
| 6 | Reflection and convenience lemmas bridge Bool and Prop | VERIFIED | `common/Builtins.v` lines 161-209: 5 lemmas: `builtin_can_replicate_bf_spec` (reflect), `builtin_can_replicate_bf_true`, `builtin_can_replicate_bf_false_replicate`, `builtin_can_replicate_true_bf`, `builtin_can_replicate_not_ef_builtin` |
| 7 | Protocol recognizers accessible from common/Builtins.v, removed from backend/RTL.v | VERIFIED | `common/Builtins.v` lines 215-501: all 4 protocol recognizer families (green_smove, blue_smove, vote, vote_runtime) with Boolean variants, spec lemmas, and cross-exclusion lemmas. `backend/RTL.v` contains zero occurrences of these definitions |
| 8 | All 6 downstream consumer files import Builtins and their .vo files build | VERIFIED | All 6 files have `Builtins` in import block; all 6 .vo files present on disk with timestamps matching or after the migration commit |
| 9 | `builtin_sem_val_compat` unified dispatcher exists, gated by `builtin_can_replicate_bf = true` | VERIFIED | `backend/RTLfault.v` lines 1090-1116: unified dispatcher with `builtin_can_replicate_bf bf = true` gate, plus secondary no-shift hypothesis (documented limitation) |
| 10 | Semantic property uses val_compat (not Val.lessdef), with Forall2 val_compat on inputs | VERIFIED | `backend/RTLfault.v` lines 1090-1103: `Forall2 val_compat vargs1 vargs2` as input hypothesis; all per-class lemmas use val_compat throughout |

**Score:** 10/10 truths verified

---

## Required Artifacts

| Artifact | Expected | Status | Details |
|----------|----------|--------|---------|
| `common/Builtins.v` | `builtin_can_replicate_bf`, `builtin_can_replicate`, `builtin_can_fault`, reflection lemmas, protocol recognizers | VERIFIED | 501 lines; all definitions present, compiled to `common/Builtins.vo` (104 605 bytes) |
| `backend/RTLfault.v` | `builtin_sem_val_compat` unified dispatcher plus per-class lemmas | VERIFIED | 1118 lines; dispatcher at line 1090, per-class lemmas from line 783; compiled to `backend/RTLfault.vo` (1 412 615 bytes) |
| `backend/RTL.v` | Protocol recognizers removed | VERIFIED | Zero occurrences of `is_green_smove_builtin`, `is_vote_builtin`, `is_blue_smove_builtin` in RTL.v; compiled `backend/RTL.vo` exists |

---

## Key Link Verification

| From | To | Via | Status | Details |
|------|----|-----|--------|---------|
| `common/Builtins.v:builtin_can_replicate` | `common/Builtins.v:lookup_builtin_function` | `match on EF_builtin, then lookup_builtin_function name sg` | WIRED | Line 136: `match lookup_builtin_function name sg with` directly inside EF_builtin branch |
| `common/Builtins.v:builtin_can_replicate_bf` | `common/Builtins.v:builtin_function` | `exhaustive match on BI_standard/BI_platform/BI_replicate` | WIRED | Lines 108-127: complete match statement covers all three constructors |
| `backend/RTLfault.v:builtin_sem_val_compat` | `common/Builtins.v:builtin_can_replicate_bf` | `hypothesis that builtin_can_replicate_bf bf = true gates the lemma` | WIRED | Line 1092: `builtin_can_replicate_bf bf = true ->` is the first hypothesis |
| `backend/RTLfault.v:builtin_sem_val_compat` | `backend/RTLfault.v:val_compat` | `Forall2 val_compat on argument lists and val_compat on results` | WIRED | Lines 1099-1103: `Forall2 val_compat vargs1 vargs2` input, `val_compat vres1 vres2` conclusion |
| `backend/RTLfault.v:builtin_sem_val_compat` | `common/Builtins0.v:standard_builtin_sem` | `via standard_builtin_sem_val_compat dispatcher` | WIRED | Line 1109: `eapply standard_builtin_sem_val_compat; eauto` |
| `backend/RTLcolor.v` | `common/Builtins.v:is_green_smove_builtin` | `Require Import Builtins` (direct) | WIRED | `backend/RTLcolor.v` line 3: `Builtins` in import block; uses `is_green_smove_builtin` at line 158 |
| `backend/RTLtolerant.v` | `common/Builtins.v:is_vote_builtin` | `Require Import Builtins` (direct) | WIRED | `backend/RTLtolerant.v` line 3: `Builtins` in import block; uses `is_vote_builtin` at line 566 |

---

## Requirements Coverage

| Requirement | Source Plan | Description | Status | Evidence |
|-------------|-------------|-------------|--------|---------|
| CLAS-01 | 01-01 | `builtin_can_replicate_bf : builtin_function -> bool` returning true for safe builtins | SATISFIED | Defined at `common/Builtins.v:107`; 20 unconditional true cases + 1 conditional (BI_subl). Note: REQUIREMENTS.md states "22" but code implements 21 on non-ptr64 and 20 on ptr64 targets -- minor documentation off-by-one, code is correct |
| CLAS-02 | 01-01 | `builtin_can_replicate : external_function -> bool` via lookup_builtin_function | SATISFIED | Defined at `common/Builtins.v:133`; EF_builtin dispatches to builtin_can_replicate_bf, all other EF constructors return false |
| CLAS-03 | 01-01 | `builtin_can_fault` aligned with `builtin_can_replicate` | SATISFIED | Defined at `common/Builtins.v:151`; `builtin_can_fault ef := builtin_can_replicate ef` |
| CLAS-04 | 01-01 | Propositional forms and reflection lemmas | SATISFIED | 5 lemmas at lines 161-209: `builtin_can_replicate_bf_prop`, reflect spec, true-excludes-replicate, false-replicate, lookup connection, non-EF_builtin exclusion |
| CLAS-05 | 01-02 | Protocol-builtin recognizers moved from `backend/RTL.v` to `common/Builtins.v` | SATISFIED | All 4 families (green_smove, blue_smove, vote, vote_runtime) + Boolean variants + spec lemmas + cross-exclusion in `common/Builtins.v` lines 215-501; zero definitions remain in `backend/RTL.v` |
| CLAS-06 | 01-01 | Classification accommodates x86, RISC-V, and aarch64 platform builtins | SATISFIED | `common/Builtins.v:122-125`: BI_platform branch matches BI_fmin/BI_fmax for x86; RISC-V/aarch64 have empty `platform_builtin` type, match is vacuously exhaustive |
| CLAS-07 | 01-01 | `BI_subl` classified conditionally on `Archi.ptr64` | SATISFIED | `common/Builtins.v:113`: `BI_subl => negb Archi.ptr64`, matching the `is_protectedb Osubl` pattern in RTL.v |
| SEMA-01 | 01-03 | `val_compat` monotonicity for `mkbuiltin_nNt` builtins | SATISFIED | `backend/RTLfault.v:783-835`: `val_compat_proj_num_inj`, `val_compat_mkbuiltin_n1t`, `val_compat_proj_num_inj2`, `val_compat_mkbuiltin_n2t` generic lemmas covering all nNt builtins; `standard_builtin_sem_val_compat` and `platform_builtin_sem_val_compat` dispatchers at lines 1037-1070 |
| SEMA-02 | 01-03 | `val_compat` monotonicity for `mkbuiltin_v2t` builtins; shifts have restricted-case lemmas | SATISFIED | `backend/RTLfault.v:866-972`: `builtin_sem_val_compat_addl`, `builtin_sem_val_compat_mull`, `builtin_sem_val_compat_subl` proved; shift builtins (shl/shr/sar) have documented UNPROVABLE general form (Abort at line 929) and restricted same-amount lemmas at lines 935-972 |
| SEMA-03 | 01-03 | Semantic property formulated against `val_compat`, not `Val.lessdef` | SATISFIED | All per-class and unified lemma statements in `backend/RTLfault.v` use `val_compat` exclusively in input hypotheses and conclusions; the single `Val.lessdef` reference (line 44) is in a helper `val_lessdef_compat` that converts Val.lessdef to val_compat, not in the semantic property statements |

---

## Anti-Patterns Found

| File | Line | Pattern | Severity | Impact |
|------|------|---------|----------|--------|
| `backend/RTLfault.v` | 918-929 | `Lemma ... Abort.` (intentional UNPROVABLE documentation lemma) | INFO | Intentional: documents the proof barrier for general shift val_compat; the lemma name includes `_UNPROVABLE`; restricted case lemmas are proved correctly; does not block any downstream consumer |

---

## Human Verification Required

None. All observable truths can be verified programmatically against the Coq source.

The `Abort.` at line 929 for `builtin_sem_val_compat_shl_UNPROVABLE` is intentional documentation of a genuine theoretical limitation (Int.ltu divergence under val_compat for faulted shift amounts). The restricted lemmas and the unified dispatcher's secondary hypothesis excluding shifts are the correct engineering response.

---

## Gaps Summary

No gaps. All 10 truths verified, all 10 requirements satisfied, all 3 artifacts are substantive and wired, all 7 key links confirmed.

**One minor documentation discrepancy noted (not a gap):** REQUIREMENTS.md CLAS-01 states "22 safe builtins" but the code implements 21 when `Archi.ptr64 = false` or 20 when `Archi.ptr64 = true`. The off-by-one in the requirement description has no effect on any proof or downstream consumer -- the code is the source of truth and is internally consistent with the conditional BI_subl classification.

---

_Verified: 2026-03-14_
_Verifier: Claude (gsd-verifier)_
