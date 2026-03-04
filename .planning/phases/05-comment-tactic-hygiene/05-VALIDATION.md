---
phase: 5
slug: comment-tactic-hygiene
status: draft
nyquist_compliant: false
wave_0_complete: false
created: 2026-03-04
---

# Phase 5 — Validation Strategy

> Per-phase validation contract for feedback sampling during execution.

---

## Test Infrastructure

| Property | Value |
|----------|-------|
| **Framework** | Coq 8.20.0 proof checking (make proof) |
| **Config file** | Makefile + _CoqProject |
| **Quick run command** | `make backend/<file>.vo` |
| **Full suite command** | `make proof -j$(nproc) && make check-admitted` |
| **Estimated runtime** | ~120 seconds (full suite) |

---

## Sampling Rate

- **After every task commit:** Run `make backend/<file>.vo` for each modified file
- **After every plan wave:** Run `make proof -j$(nproc) && make check-admitted`
- **Before `/gsd:verify-work`:** Full suite must be green + `rg 'TODO' backend/ driver/` clean
- **Max feedback latency:** ~30 seconds (single file build)

---

## Per-Task Verification Map

| Task ID | Plan | Wave | Requirement | Test Type | Automated Command | File Exists | Status |
|---------|------|------|-------------|-----------|-------------------|-------------|--------|
| 05-01-01 | 01 | 1 | HYG-01 | build | `make backend/RTLtolerant.vo` | N/A (build) | ⬜ pending |
| 05-01-02 | 01 | 1 | HYG-02 | build | `make backend/RTLagreement.vo` | N/A (build) | ⬜ pending |
| 05-01-03 | 01 | 1 | HYG-03 | build | `make backend/RTLtmr.vo` | N/A (build) | ⬜ pending |
| 05-01-04 | 01 | 1 | HYG-04 | build+manual | `make driver/Complements.vo` | N/A (build) | ⬜ pending |
| 05-01-05 | 01 | 1 | HYG-05 | build | `make backend/RTLcolorcheck.vo` | N/A (build) | ⬜ pending |
| 05-01-06 | 01 | 1 | HYG-06 | build | `make backend/Novotes.vo` | N/A (build) | ⬜ pending |
| 05-01-07 | 01 | 1 | HYG-07 | build | `make backend/RTLfault.vo` | N/A (build) | ⬜ pending |
| 05-02-01 | 02 | 1 | HYG-08 | grep | `rg 'TODO' backend/ driver/ --glob '!CSEproof.v' --glob '!Unusedglobproof.v'` | N/A (grep) | ⬜ pending |
| 05-02-02 | 02 | 1 | HYG-09 | grep | `rg 'maj_vote_regR_star_step' backend/` returns 0 | N/A (grep) | ⬜ pending |

*Status: ⬜ pending · ✅ green · ❌ red · ⚠️ flaky*

---

## Wave 0 Requirements

*Existing infrastructure covers all phase requirements. No new test files or fixtures needed.*

---

## Manual-Only Verifications

| Behavior | Requirement | Why Manual | Test Instructions |
|----------|-------------|------------|-------------------|
| Complements.v retains 2 design-note sketches | HYG-04 | Requires human judgment on content quality | Verify vote-parametric RTL->Asm sketch and asm weak-agreement sketch are retained as concise design notes |
| Design-rationale comments preserved across all files | HYG-01-07 | Requires judgment to distinguish design notes from dead code | Review each deletion to confirm no design rationale was lost |

---

## Validation Sign-Off

- [ ] All tasks have `<automated>` verify or Wave 0 dependencies
- [ ] Sampling continuity: no 3 consecutive tasks without automated verify
- [ ] Wave 0 covers all MISSING references
- [ ] No watch-mode flags
- [ ] Feedback latency < 30s
- [ ] `nyquist_compliant: true` set in frontmatter

**Approval:** pending
