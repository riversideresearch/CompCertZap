---
phase: 2
slug: shared-module-introduction
status: draft
nyquist_compliant: false
wave_0_complete: false
created: 2026-03-03
---

# Phase 2 — Validation Strategy

> Per-phase validation contract for feedback sampling during execution.

---

## Test Infrastructure

| Property | Value |
|----------|-------|
| **Framework** | Coq proof checker (coqc) + grep-based check-admitted |
| **Config file** | Makefile (coqdep-based dependency resolution) |
| **Quick run command** | `make backend/RTLreplicateSpecCommon.vo` |
| **Full suite command** | `make check-admitted && make backend/RTLdmrspec.vo backend/RTLtmrspec.vo backend/RTLdmrproof.vo backend/RTLtmrproof.vo` |
| **Estimated runtime** | ~120 seconds |

---

## Sampling Rate

- **After every task commit:** Run `make backend/RTLreplicateSpecCommon.vo && make backend/RTLdmrspec.vo backend/RTLtmrspec.vo`
- **After every plan wave:** Run `make check-admitted && make backend/RTLdmrspec.vo backend/RTLtmrspec.vo backend/RTLdmrproof.vo backend/RTLtmrproof.vo`
- **Before `/gsd:verify-work`:** Full suite must be green
- **Max feedback latency:** 120 seconds

---

## Per-Task Verification Map

| Task ID | Plan | Wave | Requirement | Test Type | Automated Command | File Exists | Status |
|---------|------|------|-------------|-----------|-------------------|-------------|--------|
| 02-01-01 | 01 | 1 | MOD-01 | build | `make backend/RTLreplicateSpecCommon.vo` | ❌ W0 | ⬜ pending |
| 02-01-02 | 01 | 1 | MOD-02 | build | `make backend/RTLreplicateProofCommon.vo` | ❌ W0 | ⬜ pending |
| 02-01-03 | 01 | 1 | MOD-03 | build | `make backend/RTLdmrspec.vo backend/RTLtmrspec.vo` | ✅ | ⬜ pending |
| 02-01-04 | 01 | 1 | MOD-04 | build | `make backend/RTLdmrproof.vo backend/RTLtmrproof.vo` | ✅ | ⬜ pending |
| 02-01-05 | 01 | 1 | ALL | grep | `make check-admitted` | ✅ | ⬜ pending |

*Status: ⬜ pending · ✅ green · ❌ red · ⚠️ flaky*

---

## Wave 0 Requirements

- [ ] `backend/RTLreplicateSpecCommon.v` — new file with shared Ltac tactics + type defs
- [ ] `backend/RTLreplicateProofCommon.v` — new file with shared proof boilerplate
- [ ] Makefile `BACKEND` variable — add both new files
- [ ] `make depend` — regenerate `.depend` with new files

*These are created as part of Phase 2 execution, not pre-existing infrastructure.*

---

## Manual-Only Verifications

*All phase behaviors have automated verification.*

---

## Validation Sign-Off

- [ ] All tasks have `<automated>` verify or Wave 0 dependencies
- [ ] Sampling continuity: no 3 consecutive tasks without automated verify
- [ ] Wave 0 covers all MISSING references
- [ ] No watch-mode flags
- [ ] Feedback latency < 120s
- [ ] `nyquist_compliant: true` set in frontmatter

**Approval:** pending
