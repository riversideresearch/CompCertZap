---
phase: 1
slug: proofliveness-analysis
status: draft
nyquist_compliant: false
wave_0_complete: false
created: 2026-03-04
---

# Phase 1 — Validation Strategy

> Per-phase validation contract for feedback sampling during execution.

---

## Test Infrastructure

| Property | Value |
|----------|-------|
| **Framework** | Coq 8.20.0 proof checker |
| **Config file** | `_CoqProject` (R flags for all directories) |
| **Quick run command** | `make backend/ProofLiveness.vo` |
| **Full suite command** | `make proof` |
| **Estimated runtime** | ~30 seconds (single file), ~minutes (full suite) |

---

## Sampling Rate

- **After every task commit:** Run `make backend/ProofLiveness.vo`
- **After every plan wave:** Run `make backend/ProofLiveness.vo && ! grep -w 'Admitted' backend/ProofLiveness.v`
- **Before `/gsd:verify-work`:** Full suite must be green
- **Max feedback latency:** 30 seconds

---

## Per-Task Verification Map

| Task ID | Plan | Wave | Requirement | Test Type | Automated Command | File Exists | Status |
|---------|------|------|-------------|-----------|-------------------|-------------|--------|
| 1-01-01 | 01 | 1 | PLIV-01 | unit (Coq type-check) | `make backend/ProofLiveness.vo` | ❌ W0 | ⬜ pending |
| 1-01-02 | 01 | 1 | PLIV-02 | unit (Coq type-check) | `make backend/ProofLiveness.vo` | ❌ W0 | ⬜ pending |
| 1-01-03 | 01 | 1 | PLIV-03 | unit (Coq proof-check) | `make backend/ProofLiveness.vo` | ❌ W0 | ⬜ pending |
| 1-01-04 | 01 | 1 | PLIV-04 | unit (Coq proof-check) | `make backend/ProofLiveness.vo` | ❌ W0 | ⬜ pending |
| 1-01-05 | 01 | 1 | PLIV-05 | integration | `make backend/ProofLiveness.vo && ! grep -w 'Admitted' backend/ProofLiveness.v` | ❌ W0 | ⬜ pending |

*Status: ⬜ pending · ✅ green · ❌ red · ⚠️ flaky*

---

## Wave 0 Requirements

- [ ] `backend/ProofLiveness.v` — the entire file (PLIV-01 through PLIV-05)
- [ ] `Makefile` BACKEND list update — add ProofLiveness.v
- [ ] `.depend` regeneration — `make depend`

*All verification commands target the single file being created in this phase.*

---

## Manual-Only Verifications

*All phase behaviors have automated verification.*

---

## Validation Sign-Off

- [ ] All tasks have `<automated>` verify or Wave 0 dependencies
- [ ] Sampling continuity: no 3 consecutive tasks without automated verify
- [ ] Wave 0 covers all MISSING references
- [ ] No watch-mode flags
- [ ] Feedback latency < 30s
- [ ] `nyquist_compliant: true` set in frontmatter

**Approval:** pending
