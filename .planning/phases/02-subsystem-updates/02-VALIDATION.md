---
phase: 2
slug: subsystem-updates
status: draft
nyquist_compliant: false
wave_0_complete: false
created: 2026-03-14
---

# Phase 2 — Validation Strategy

> Per-phase validation contract for feedback sampling during execution.

---

## Test Infrastructure

| Property | Value |
|----------|-------|
| **Framework** | Coq proof checker (coqc) + make |
| **Config file** | `Makefile`, `_CoqProject` |
| **Quick run command** | `make backend/RTLtmr.vo` |
| **Full suite command** | `make -j$(nproc) all` |
| **Estimated runtime** | ~120 seconds (single .vo), ~600 seconds (full) |

---

## Sampling Rate

- **After every task commit:** Run `make backend/{modified_file}.vo`
- **After every plan wave:** Run `make -j$(nproc) proof`
- **Before `/gsd:verify-work`:** Full suite must be green
- **Max feedback latency:** 120 seconds

---

## Per-Task Verification Map

| Task ID | Plan | Wave | Requirement | Test Type | Automated Command | File Exists | Status |
|---------|------|------|-------------|-----------|-------------------|-------------|--------|
| 02-01-01 | 01 | 1 | TMR-01 | proof/build | `make backend/RTLtmr.vo` | ✅ | ⬜ pending |
| 02-01-02 | 01 | 1 | TMR-02 | proof/build | `make backend/RTLtmr.vo` | ✅ | ⬜ pending |
| 02-01-03 | 01 | 1 | TMR-03 | proof/build | `make backend/RTLtmr.vo` | ✅ | ⬜ pending |
| 02-01-04 | 01 | 1 | TMR-04 | code review | Manual | N/A | ⬜ pending |
| 02-01-05 | 01 | 1 | TMR-05 | proof/build | `make backend/RTLtmrspec.vo` | ✅ | ⬜ pending |
| 02-01-06 | 01 | 1 | TMR-06 | proof/build | `make backend/RTLtmrproof.vo` | ✅ | ⬜ pending |
| 02-02-01 | 02 | 1 | COLR-01 | proof/build | `make backend/RTLcolor.vo` | ✅ | ⬜ pending |
| 02-02-02 | 02 | 1 | COLR-02 | proof/build | `make backend/RTLcolorcheck.vo` | ✅ | ⬜ pending |
| 02-02-03 | 02 | 1 | COLR-03 | build/test | `make ccomp && ./ccomp test.c -tmr` | ✅ | ⬜ pending |
| 02-02-04 | 02 | 1 | COLR-04 | proof/build | `make backend/RTLcolorcheck.vo` | ✅ | ⬜ pending |
| 02-02-05 | 02 | 1 | FALT-01 | proof/build | `make backend/RTLfault.vo` | ✅ | ⬜ pending |
| 02-02-06 | 02 | 1 | FALT-02 | proof/build | `make backend/RTLfault.vo` | ✅ | ⬜ pending |
| 02-03-01 | 01 | 2 | INTG-01 | build | `make backend/RTLtmr.vo` | ✅ | ⬜ pending |
| 02-03-02 | 01 | 2 | INTG-02 | build | `make backend/RTLtmrproof.vo` | ✅ | ⬜ pending |
| 02-03-03 | 02 | 2 | INTG-03 | build | `make backend/RTLcolor.vo` | ✅ | ⬜ pending |
| 02-03-04 | 02 | 2 | INTG-04 | build | `make backend/RTLcolorcheck.vo` | ✅ | ⬜ pending |

*Status: ⬜ pending · ✅ green · ❌ red · ⚠️ flaky*

---

## Wave 0 Requirements

Existing infrastructure covers all phase requirements. All files to be modified already exist and build.

---

## Manual-Only Verifications

| Behavior | Requirement | Why Manual | Test Instructions |
|----------|-------------|------------|-------------------|
| map_builtin_arg/res used | TMR-04 | Code pattern not checkable by build | Review `transf_instr` Ibuiltin safe branch for `map_builtin_arg`/`map_builtin_res` usage |

---

## Validation Sign-Off

- [ ] All tasks have `<automated>` verify or Wave 0 dependencies
- [ ] Sampling continuity: no 3 consecutive tasks without automated verify
- [ ] Wave 0 covers all MISSING references
- [ ] No watch-mode flags
- [ ] Feedback latency < 120s
- [ ] `nyquist_compliant: true` set in frontmatter

**Approval:** pending
