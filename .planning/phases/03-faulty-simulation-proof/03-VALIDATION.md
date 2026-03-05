---
phase: 3
slug: faulty-simulation-proof
status: draft
nyquist_compliant: false
wave_0_complete: false
created: 2026-03-04
---

# Phase 3 — Validation Strategy

> Per-phase validation contract for feedback sampling during execution.

---

## Test Infrastructure

| Property | Value |
|----------|-------|
| **Framework** | Coq proof checker (coqc) |
| **Config file** | `_CoqProject` |
| **Quick run command** | `make backend/RTLtolerant.vo` |
| **Full suite command** | `make backend/RTLtolerant.vo && make check-admitted` |
| **Estimated runtime** | ~60 seconds |

---

## Sampling Rate

- **After every task commit:** Run `make backend/RTLtolerant.vo`
- **After every plan wave:** Run `make backend/RTLtolerant.vo && make check-admitted`
- **Before `/gsd:verify-work`:** Full suite must be green
- **Max feedback latency:** 60 seconds

---

## Per-Task Verification Map

| Task ID | Plan | Wave | Requirement | Test Type | Automated Command | File Exists | Status |
|---------|------|------|-------------|-----------|-------------------|-------------|--------|
| 03-01-01 | 01 | 1 | FSIM-01 | unit (coqc) | `grep -c 'ProofLiveness.analyze' backend/RTLtolerant.v` | N/A | ⬜ pending |
| 03-01-02 | 01 | 1 | FSIM-02 | unit (coqc) | `make backend/RTLtolerant.vo` | N/A | ⬜ pending |
| 03-01-03 | 01 | 1 | FSIM-03 | unit (coqc) | `make backend/RTLtolerant.vo` | N/A | ⬜ pending |
| 03-01-04 | 01 | 1 | FSIM-04 | unit (coqc) | `make backend/RTLtolerant.vo` | N/A | ⬜ pending |
| 03-01-05 | 01 | 1 | FSIM-05 | unit (coqc) | `make backend/RTLtolerant.vo` | N/A | ⬜ pending |
| 03-01-06 | 01 | 1 | FSIM-06 | unit (coqc) | `make backend/RTLtolerant.vo` | N/A | ⬜ pending |
| 03-01-07 | 01 | 1 | FSIM-07 | unit (coqc) | `make backend/RTLtolerant.vo` | N/A | ⬜ pending |
| 03-01-08 | 01 | 1 | FSIM-08 | integration | `make backend/RTLtolerant.vo && grep -c Admitted backend/RTLtolerant.v` | N/A | ⬜ pending |

*Status: ⬜ pending · ✅ green · ❌ red · ⚠️ flaky*

---

## Wave 0 Requirements

Existing infrastructure covers all phase requirements. Phase 1 and Phase 2 are already complete, providing `ProofLiveness.vo` and updated `RTLcolor.vo` / `RTLcolorcheck.vo`.

---

## Manual-Only Verifications

All phase behaviors have automated verification.

---

## Validation Sign-Off

- [ ] All tasks have `<automated>` verify or Wave 0 dependencies
- [ ] Sampling continuity: no 3 consecutive tasks without automated verify
- [ ] Wave 0 covers all MISSING references
- [ ] No watch-mode flags
- [ ] Feedback latency < 60s
- [ ] `nyquist_compliant: true` set in frontmatter

**Approval:** pending
