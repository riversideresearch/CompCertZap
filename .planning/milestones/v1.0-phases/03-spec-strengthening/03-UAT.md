---
status: complete
phase: 03-spec-strengthening
source: [03-01-SUMMARY.md, 03-02-SUMMARY.md]
started: 2026-03-03T12:00:00Z
updated: 2026-03-03T12:05:00Z
---

## Current Test

[testing complete]

## Tests

### 1. DMR relational spec compiles
expected: `make backend/RTLdmrspec.vo` completes without errors. The file should contain `replication_map_rel` inductive, `foldM_satisfies_rel`, and `rel_implies_rm_wf`.
result: pass

### 2. TMR relational spec compiles
expected: `make backend/RTLtmrspec.vo` completes without errors. The file should contain TMR-specific `replication_map_rel` inductive with two shadows per register, `foldM_satisfies_rel`, and `rel_implies_rm_wf`.
result: pass

### 3. DMR downstream proof unchanged
expected: `make backend/RTLdmrproof.vo` compiles without any modifications to RTLdmrproof.v. The existing proof should work against the new relational spec interface since `replication_map_wf` has the same type signature.
result: pass

### 4. TMR downstream proof unchanged
expected: `make backend/RTLtmrproof.vo` compiles without any modifications to RTLtmrproof.v. The existing proof should work against the new TMR relational spec interface.
result: pass

### 5. Monolithic proofs removed
expected: `replication_map_wf_aux` no longer appears in either `backend/RTLdmrspec.v` or `backend/RTLtmrspec.v`. The old ~102-line (DMR) and ~128-line (TMR) monolithic proofs should be fully replaced by the decomposed relational spec approach.
result: pass

### 6. No admitted proofs
expected: `make check-admitted` passes (or `grep -r "Admitted" backend/RTLdmrspec.v backend/RTLtmrspec.v` returns nothing). No proof obligations left unfinished.
result: pass

## Summary

total: 6
passed: 6
issues: 0
pending: 0
skipped: 0

## Gaps

[none yet]
