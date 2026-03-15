---
phase: 1
slug: classification-semantic-foundation
status: draft
nyquist_compliant: false
wave_0_complete: false
created: 2026-03-14
---

# Phase 1 — Validation Strategy

> Per-phase validation contract for feedback sampling during execution.

---

## Test Infrastructure

| Property | Value |
|----------|-------|
| **Framework** | Coq proof checker (coqc) + `make check-admitted` |
| **Config file** | `_CoqProject` (includes `-R` flags for all directories) |
| **Quick run command** | `make common/Builtins.vo` or `make backend/RTLfault.vo` |
| **Full suite command** | `make proof` (compiles all .v files) |
| **Estimated runtime** | ~60 seconds (quick), ~600 seconds (full suite) |

---

## Sampling Rate

- **After every task commit:** Run `make common/Builtins.vo` or `make backend/RTLfault.vo` (whichever file was modified)
- **After every plan wave:** Run `make common/Builtins.vo backend/RTLfault.vo backend/RTLcolor.vo backend/RTLcolorcheck.vo backend/Novotes.vo backend/RTLtolerant.vo`
- **Before `/gsd:verify-work`:** Full `make proof` + `make check-admitted` must be green
- **Max feedback latency:** 60 seconds

---

## Per-Task Verification Map

| Task ID | Plan | Wave | Requirement | Test Type | Automated Command | File Exists | Status |
|---------|------|------|-------------|-----------|-------------------|-------------|--------|
| 1-01-01 | 01 | 1 | CLAS-01 | unit (Coq type-check) | `make common/Builtins.vo` | File exists, defs to add | ⬜ pending |
| 1-01-02 | 01 | 1 | CLAS-02 | unit (Coq type-check) | `make common/Builtins.vo` | File exists, defs to add | ⬜ pending |
| 1-01-03 | 01 | 1 | CLAS-03 | unit (Coq type-check) | `make common/Builtins.vo` | File exists, defs to add | ⬜ pending |
| 1-01-04 | 01 | 1 | CLAS-04 | unit (Coq proof-check) | `make common/Builtins.vo` | File exists, lemmas to add | ⬜ pending |
| 1-01-05 | 01 | 1 | CLAS-06 | unit (Coq type-check) | `make common/Builtins.vo` | File exists | ⬜ pending |
| 1-01-06 | 01 | 1 | CLAS-07 | unit (Coq type-check) | `make common/Builtins.vo` | File exists | ⬜ pending |
| 1-02-01 | 02 | 1 | CLAS-05 | integration (downstream) | `make backend/RTLcolor.vo backend/RTLcolorcheck.vo backend/Novotes.vo` | Files exist, imports to update | ⬜ pending |
| 1-03-01 | 03 | 2 | SEMA-01 | unit (Coq proof-check) | `make backend/RTLfault.vo` | File exists, lemma to add | ⬜ pending |
| 1-03-02 | 03 | 2 | SEMA-02 | unit (Coq proof-check) | `make backend/RTLfault.vo` | File exists, lemma to add | ⬜ pending |
| 1-03-03 | 03 | 2 | SEMA-03 | unit (Coq proof-check) | `make backend/RTLfault.vo` | File exists, lemma to add | ⬜ pending |

*Status: ⬜ pending · ✅ green · ❌ red · ⚠️ flaky*

---

## Wave 0 Requirements

*Existing infrastructure covers all phase requirements.* The Coq build system (`make *.vo`) and `make check-admitted` provide all needed verification. No additional test framework or config needed.

---

## Manual-Only Verifications

| Behavior | Requirement | Why Manual | Test Instructions |
|----------|-------------|------------|-------------------|
| Shift builtins val_compat decision | SEMA-02 | Design decision on whether to include/exclude shifts | Review proof attempt; if val_compat fails for shifts, remove from whitelist |

---

## Validation Sign-Off

- [ ] All tasks have `<automated>` verify or Wave 0 dependencies
- [ ] Sampling continuity: no 3 consecutive tasks without automated verify
- [ ] Wave 0 covers all MISSING references
- [ ] No watch-mode flags
- [ ] Feedback latency < 60s
- [ ] `nyquist_compliant: true` set in frontmatter

**Approval:** pending
