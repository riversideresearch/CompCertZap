---
phase: 1
slug: baseline-and-file-cleanup
status: draft
nyquist_compliant: false
wave_0_complete: false
created: 2026-03-03
---

# Phase 1 — Validation Strategy

> Per-phase validation contract for feedback sampling during execution.

---

## Test Infrastructure

| Property | Value |
|----------|-------|
| **Framework** | Coq 8.20.0 proof checker (coqc) + shell commands |
| **Config file** | `Makefile` + `Makefile.config` (both present) |
| **Quick run command** | `make check-admitted` |
| **Full suite command** | `make backend/Novotesproof.vo backend/RTLdmrproof.vo backend/RTLtmrproof.vo backend/RTLtolerant.vo && make check-admitted` |
| **Estimated runtime** | ~600-1800 seconds (first build from clean state) |

---

## Sampling Rate

- **After every task commit:** Run `make check-admitted`
- **After every plan wave:** Run `make backend/Novotesproof.vo backend/RTLdmrproof.vo backend/RTLtmrproof.vo backend/RTLtolerant.vo && make check-admitted`
- **Before `/gsd:verify-work`:** Full suite must be green
- **Max feedback latency:** 1800 seconds (first build only; subsequent <30 seconds)

---

## Per-Task Verification Map

| Task ID | Plan | Wave | Requirement | Test Type | Automated Command | File Exists | Status |
|---------|------|------|-------------|-----------|-------------------|-------------|--------|
| 01-01-01 | 01 | 1 | FILE-04 | integration | `make depend` | N/A | ⬜ pending |
| 01-01-02 | 01 | 1 | FILE-04 | integration | `make backend/Novotesproof.vo backend/RTLdmrproof.vo backend/RTLtmrproof.vo backend/RTLtolerant.vo` | N/A | ⬜ pending |
| 01-01-03 | 01 | 1 | FILE-04 | smoke | `make check-admitted && ! grep -rn "^\s*Admitted" backend/ driver/` | N/A | ⬜ pending |
| 01-02-01 | 02 | 1 | FILE-01 | smoke | `git status --porcelain \| grep -cE 'backup_\|DMRproof_backup\|RTLfault_backup\|RTLAgreement_backup\|RTLinfercolor_unify' \| test $(cat) -eq 0` | N/A | ⬜ pending |
| 01-02-02 | 02 | 1 | FILE-02, FILE-03 | smoke | `test ! -f backend/AdvSem.v && test ! -f backend/Replicate3proof.v && ! rg -q 'AdvSem\|Replicate3' backend/ driver/` | N/A | ⬜ pending |

*Status: ⬜ pending · ✅ green · ❌ red · ⚠️ flaky*

---

## Wave 0 Requirements

- [ ] `.depend` file — generate via `make depend` before any `.vo` build

*Existing infrastructure covers all other phase requirements.*

---

## Manual-Only Verifications

| Behavior | Requirement | Why Manual | Test Instructions |
|----------|-------------|------------|-------------------|
| Verify 13-vs-14 file count | FILE-01 | Judgment call on RTLinfercolor_unify.ml inclusion | Review git status, confirm all backup-pattern files removed |

---

## Validation Sign-Off

- [ ] All tasks have `<automated>` verify or Wave 0 dependencies
- [ ] Sampling continuity: no 3 consecutive tasks without automated verify
- [ ] Wave 0 covers all MISSING references
- [ ] No watch-mode flags
- [ ] Feedback latency < 1800s
- [ ] `nyquist_compliant: true` set in frontmatter

**Approval:** pending
