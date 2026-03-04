---
phase: 3
slug: spec-strengthening
status: draft
nyquist_compliant: false
wave_0_complete: false
created: 2026-03-03
---

# Phase 3 — Validation Strategy

> Per-phase validation contract for feedback sampling during execution.

---

## Test Infrastructure

| Property | Value |
|----------|-------|
| **Framework** | Coq (make) |
| **Config file** | Makefile + _CoqProject |
| **Quick run command** | `make backend/RTLdmrspec.vo backend/RTLtmrspec.vo -j4` |
| **Full suite command** | `make backend/RTLdmrspec.vo backend/RTLtmrspec.vo backend/RTLdmrproof.vo backend/RTLtmrproof.vo -j4` |
| **Estimated runtime** | ~120 seconds |

---

## Sampling Rate

- **After every task commit:** Run `make backend/RTLdmrspec.vo backend/RTLtmrspec.vo -j4`
- **After every plan wave:** Run `make backend/RTLdmrspec.vo backend/RTLtmrspec.vo backend/RTLdmrproof.vo backend/RTLtmrproof.vo -j4`
- **Before `/gsd:verify-work`:** Full suite must be green
- **Max feedback latency:** 120 seconds

---

## Per-Task Verification Map

| Task ID | Plan | Wave | Requirement | Test Type | Automated Command | File Exists | Status |
|---------|------|------|-------------|-----------|-------------------|-------------|--------|
| 03-01-01 | 01 | 1 | SPEC-01 | compilation | `make backend/RTLdmrspec.vo` | N/A (source mod) | ⬜ pending |
| 03-01-02 | 01 | 1 | SPEC-03 | compilation | `make backend/RTLdmrspec.vo backend/RTLdmrproof.vo -j4` | N/A | ⬜ pending |
| 03-02-01 | 02 | 1 | SPEC-02 | compilation | `make backend/RTLtmrspec.vo` | N/A (source mod) | ⬜ pending |
| 03-02-02 | 02 | 1 | SPEC-04 | compilation | `make backend/RTLtmrspec.vo backend/RTLtmrproof.vo -j4` | N/A | ⬜ pending |

*Status: ⬜ pending · ✅ green · ❌ red · ⚠️ flaky*

---

## Wave 0 Requirements

*Existing infrastructure covers all phase requirements. No new test files needed.*

---

## Manual-Only Verifications

*All phase behaviors have automated verification (Coq type-checking).*

---

## Validation Sign-Off

- [ ] All tasks have `<automated>` verify or Wave 0 dependencies
- [ ] Sampling continuity: no 3 consecutive tasks without automated verify
- [ ] Wave 0 covers all MISSING references
- [ ] No watch-mode flags
- [ ] Feedback latency < 120s
- [ ] `nyquist_compliant: true` set in frontmatter

**Approval:** pending
