---
phase: 2
slug: color-system-update
status: draft
nyquist_compliant: false
wave_0_complete: false
created: 2026-03-04
---

# Phase 2 — Validation Strategy

> Per-phase validation contract for feedback sampling during execution.

---

## Test Infrastructure

| Property | Value |
|----------|-------|
| **Framework** | Coq 8.20.0 proof checker |
| **Config file** | _CoqProject |
| **Quick run command** | `make backend/RTLcolor.vo && make backend/RTLcolorcheck.vo` |
| **Full suite command** | `make proof` |
| **Estimated runtime** | ~120 seconds |

---

## Sampling Rate

- **After every task commit:** Run `make backend/RTLcolor.vo && make backend/RTLcolorcheck.vo`
- **After every plan wave:** Run `make backend/RTLcolor.vo && make backend/RTLcolorcheck.vo`
- **Before `/gsd:verify-work`:** Full suite must be green
- **Max feedback latency:** 120 seconds

---

## Per-Task Verification Map

| Task ID | Plan | Wave | Requirement | Test Type | Automated Command | File Exists | Status |
|---------|------|------|-------------|-----------|-------------------|-------------|--------|
| 02-01-01 | 01 | 1 | COLR-01 | unit (build) | `make backend/RTLcolor.vo` | ✅ | ⬜ pending |
| 02-01-02 | 01 | 1 | COLR-02 | unit (build) | `make backend/RTLcolorcheck.vo` | ✅ | ⬜ pending |
| 02-01-03 | 01 | 1 | COLR-03 | unit (build + grep) | `make backend/RTLcolorcheck.vo && ! grep -q '^[^(]*Admitted' backend/RTLcolorcheck.v` | ✅ | ⬜ pending |
| 02-01-04 | 01 | 1 | COLR-04 | integration | `make backend/RTLcolor.vo && make backend/RTLcolorcheck.vo && ! grep '^[^(]*Admitted' backend/RTLcolor.v backend/RTLcolorcheck.v` | ✅ | ⬜ pending |

*Status: ⬜ pending · ✅ green · ❌ red · ⚠️ flaky*

---

## Wave 0 Requirements

*Existing infrastructure covers all phase requirements.*

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
