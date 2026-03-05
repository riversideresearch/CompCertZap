---
phase: 4
slug: integration-and-validation
status: draft
nyquist_compliant: false
wave_0_complete: false
created: 2026-03-04
---

# Phase 4 — Validation Strategy

> Per-phase validation contract for feedback sampling during execution.

---

## Test Infrastructure

| Property | Value |
|----------|-------|
| **Framework** | Coq 8.20.0 proof checker + GNU Make + OCaml 4.14.2 compiler |
| **Config file** | `Makefile`, `Makefile.extr`, `_CoqProject` |
| **Quick run command** | `make driver/Complements.vo` |
| **Full suite command** | `make driver/Complements.vo && make check-admitted && make ccomp` |
| **Estimated runtime** | ~300 seconds |

---

## Sampling Rate

- **After every task commit:** Run `make driver/Complements.vo`
- **After every plan wave:** Run `make driver/Complements.vo && make check-admitted && make ccomp`
- **Before `/gsd:verify-work`:** Full suite must be green
- **Max feedback latency:** 300 seconds

---

## Per-Task Verification Map

| Task ID | Plan | Wave | Requirement | Test Type | Automated Command | File Exists | Status |
|---------|------|------|-------------|-----------|-------------------|-------------|--------|
| 04-01-01 | 01 | 1 | INTG-01 | integration (build) | `make driver/Complements.vo` | Source exists; .vo pending | pending |
| 04-01-02 | 01 | 1 | INTG-02 | integration (grep) | `make check-admitted` | N/A - Makefile target | pending |
| 04-01-03 | 01 | 1 | INTG-03 | integration (build+run) | `make ccomp && echo 'int main(){return 0;}' > /tmp/t.c && ./ccomp /tmp/t.c -tmr -S -o /tmp/t.s` | ccomp binary exists (rebuild) | pending |

*Status: pending / green / red / flaky*

---

## Wave 0 Requirements

Existing infrastructure covers all phase requirements. No new test files, no new Makefile targets needed.

---

## Manual-Only Verifications

All phase behaviors have automated verification.

---

## Validation Sign-Off

- [ ] All tasks have `<automated>` verify or Wave 0 dependencies
- [ ] Sampling continuity: no 3 consecutive tasks without automated verify
- [ ] Wave 0 covers all MISSING references
- [ ] No watch-mode flags
- [ ] Feedback latency < 300s
- [ ] `nyquist_compliant: true` set in frontmatter

**Approval:** pending
