# Requirements: Improved Builtin Treatment in TMR

**Defined:** 2026-03-14
**Core Value:** A single shared builtin classification consumed by TMR, faulty semantics, coloring spec, checker, and oracle, with all proofs rebuilding.

## v1 Requirements

### Classification

- [x] **CLAS-01**: `builtin_can_replicate_bf : builtin_function -> bool` defined in `common/Builtins.v`, returning `true` for all 22 safe builtins (14 standard `mkbuiltin_nNt` + 2 x86 platform + 6 `mkbuiltin_v2t`)
- [x] **CLAS-02**: `builtin_can_replicate : external_function -> bool` defined in `common/Builtins.v`, recognizing `EF_builtin name sg` via `lookup_builtin_function` and dispatching to `builtin_can_replicate_bf`
- [x] **CLAS-03**: `builtin_can_fault : external_function -> bool` aligned with `builtin_can_replicate` for first implementation
- [x] **CLAS-04**: Propositional forms and reflection lemmas for classification predicates
- [x] **CLAS-05**: Protocol-builtin recognizers (`smove`, `vote`, `check`) moved from `backend/RTL.v` to `common/Builtins.v`
- [x] **CLAS-06**: Classification accommodates x86, RISC-V, and aarch64 platform builtins (RISC-V and aarch64 are vacuously empty)
- [x] **CLAS-07**: `BI_subl` classified conditionally on `Archi.ptr64` (matching `is_protected` pattern for `Osubl`)

### Semantic Validation

- [x] **SEMA-01**: `val_compat` monotonicity property proved for `mkbuiltin_nNt` builtins (pure numerical, pointer-free)
- [x] **SEMA-02**: `val_compat` monotonicity property proved for `mkbuiltin_v2t` builtins (`BI_mull`, `BI_addl`, `BI_subl`, `BI_i64_shl/shr/sar`) -- shifts have restricted-case lemmas only due to Int.ltu divergence
- [x] **SEMA-03**: Semantic property formulated against actual `val_compat`-based fault model, not just `Val.lessdef`

### TMR Pass

- [ ] **TMR-01**: `transf_instr` in `RTLtmr.v` emits per-color copies for safe builtins (green/blue/regular), analogous to safe `Iop` triplication
- [ ] **TMR-02**: White-only builtins keep current "vote arguments, run once, copy result" path unchanged
- [ ] **TMR-03**: Protocol builtins (`smove`, `vote`) retain dedicated handling unchanged
- [ ] **TMR-04**: Safe builtin argument/result remapping uses existing `AST.map_builtin_arg` and `map_builtin_res`
- [ ] **TMR-05**: `match_Ibuiltin_safe` case added to `RTLtmrspec.v`
- [ ] **TMR-06**: TMR proof in `RTLtmrproof.v` generalized with safe-builtin case using `eval_builtin_arg` remapping facts

### Color System

- [x] **COLR-01**: `wc_Ibuiltin_safe` rule added to `RTLcolor.v` analogous to `wc_Iop_safe`
- [x] **COLR-02**: `check_col_instr` in `RTLcolorcheck.v` accepts replicated safe builtins with basic colors
- [x] **COLR-03**: `RTLinfercolor.ml` oracle assigns basic colors to safe builtins instead of forcing White
- [x] **COLR-04**: Non-replicable builtins (including `check`) remain on White-only rule

### Faulty Semantics

- [x] **FALT-01**: `zap_allowed` in `RTLfault.v` returns `builtin_can_fault ef` for `Ibuiltin ef args res s`
- [x] **FALT-02**: Protocol and White-only builtins remain non-faultable

### Tolerant Proof

- [ ] **TOLR-01**: New safe-replicated-builtin proof case added to `RTLtolerant.v`
- [ ] **TOLR-02**: `exec_Ibuiltin` reasoning split into safe replicated / protocol / White-only cases
- [ ] **TOLR-03**: Helper lemmas and case splits audited for compatibility with new `wc_Ibuiltin_safe` rule

### Integration

- [ ] **INTG-01**: `backend/RTLtmr.vo` rebuilds successfully
- [ ] **INTG-02**: `backend/RTLtmrproof.vo` rebuilds successfully
- [x] **INTG-03**: `backend/RTLcolor.vo` rebuilds successfully
- [x] **INTG-04**: `backend/RTLcolorcheck.vo` rebuilds successfully
- [ ] **INTG-05**: `backend/RTLtolerant.vo` rebuilds successfully
- [ ] **INTG-06**: `driver/Complements.vo` rebuilds successfully
- [ ] **INTG-07**: `make check-admitted` passes (no Admitted proofs)

## v2 Requirements

### Extended Whitelist

- **EXTW-01**: Evaluate whether `BI_select` could become safe with a refined fault model
- **EXTW-02**: Evaluate `BR_splitlong` builtin argument support for 32-bit targets

### Naming Cleanup

- **NAME-01**: Rename `is_protected` to `op_must_run_white` or similar
- **NAME-02**: Audit and consolidate remaining builtin classification scattered across modules

## Out of Scope

| Feature | Reason |
|---------|--------|
| Load instruction treatment | Different instruction kind, interacts with memory directly, separate design needed |
| DMR+TMR mixed usage | Plan assumes TMR-only theorem path |
| `check` as replicable builtin | DMR-specific, kept conservative |
| Merging with `is_protected` | Different types (`operation` vs `external_function`), semantically overloaded |
| `BI_unreachable` as safe | Always returns `None` — execution always stuck |
| Partial builtins (`_p` family) as safe | Can return `None` on faulted inputs |

## Traceability

| Requirement | Phase | Status |
|-------------|-------|--------|
| CLAS-01 | Phase 1 | Complete |
| CLAS-02 | Phase 1 | Complete |
| CLAS-03 | Phase 1 | Complete |
| CLAS-04 | Phase 1 | Complete |
| CLAS-05 | Phase 1 | Complete |
| CLAS-06 | Phase 1 | Complete |
| CLAS-07 | Phase 1 | Complete |
| SEMA-01 | Phase 1 | Complete |
| SEMA-02 | Phase 1 | Complete |
| SEMA-03 | Phase 1 | Complete |
| TMR-01 | Phase 2 | Pending |
| TMR-02 | Phase 2 | Pending |
| TMR-03 | Phase 2 | Pending |
| TMR-04 | Phase 2 | Pending |
| TMR-05 | Phase 2 | Pending |
| TMR-06 | Phase 2 | Pending |
| COLR-01 | Phase 2 | Complete |
| COLR-02 | Phase 2 | Complete |
| COLR-03 | Phase 2 | Complete |
| COLR-04 | Phase 2 | Complete |
| FALT-01 | Phase 2 | Complete |
| FALT-02 | Phase 2 | Complete |
| TOLR-01 | Phase 3 | Pending |
| TOLR-02 | Phase 3 | Pending |
| TOLR-03 | Phase 3 | Pending |
| INTG-01 | Phase 2 | Pending |
| INTG-02 | Phase 2 | Pending |
| INTG-03 | Phase 2 | Complete |
| INTG-04 | Phase 2 | Complete |
| INTG-05 | Phase 3 | Pending |
| INTG-06 | Phase 3 | Pending |
| INTG-07 | Phase 3 | Pending |

**Coverage:**
- v1 requirements: 32 total
- Mapped to phases: 32
- Unmapped: 0

---
*Requirements defined: 2026-03-14*
*Last updated: 2026-03-15 after Phase 1 completion*
