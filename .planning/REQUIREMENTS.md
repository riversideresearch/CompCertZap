# Requirements: CompCertZAP Liveness-Bounded Proof

**Defined:** 2026-03-04
**Core Value:** Faulty backward simulation proof compiles with no Admitted using liveness-bounded register match invariant

## v1 Requirements

### ProofLiveness Analysis

- [x] **PLIV-01**: ProofLiveness.v defines conservative transfer function that always includes Iop/Iload args regardless of result liveness
- [x] **PLIV-02**: ProofLiveness.v instantiates Kildall backward solver and exposes `analyze : function -> option (PMap.t Regset.t)`
- [x] **PLIV-03**: ProofLiveness.v proves `analyze_solution` theorem (fixpoint property at every CFG edge)
- [x] **PLIV-04**: ProofLiveness.v provides `reg_list_live_in` membership lemma: `In r args -> Regset.In r (reg_list_live args s)`
- [x] **PLIV-05**: ProofLiveness.v builds standalone (`make backend/ProofLiveness.vo`)

### Color System Update

- [x] **COLR-01**: RTLcolor.v references ProofLiveness.analyze instead of Liveness.analyze in wc_function
- [x] **COLR-02**: RTLcolorcheck.v references ProofLiveness.analyze instead of Liveness.analyze in check_function and check_col_function_sound
- [x] **COLR-03**: check_col_instr_sound proof completed (no Admitted) in RTLcolorcheck.v
- [x] **COLR-04**: RTLcolor.vo and RTLcolorcheck.vo compile with zero Admitted

### Faulty Simulation Proof

- [x] **FSIM-01**: RTLtolerant.v references ProofLiveness.analyze in match_stackframes and match_states
- [x] **FSIM-02**: Per-instruction membership helper lemmas prove args are in live set for all RTL instruction forms
- [x] **FSIM-03**: match_rs_weaken lemma: Regset.Subset s1 s2 -> match_rs s2 ... -> match_rs s1 ...
- [x] **FSIM-04**: forall2_lessdef_match_rs_init_regs updated for live parameter
- [x] **FSIM-05**: step_simulation proof complete for all instruction cases
- [x] **FSIM-06**: faulty_progress proof complete for all instruction cases
- [x] **FSIM-07**: faulty_backward_simulation theorem proved
- [x] **FSIM-08**: RTLtolerant.vo compiles with zero Admitted

### Integration and Validation

- [x] **INTG-01**: driver/Complements.vo rebuilds successfully (no source changes expected)
- [x] **INTG-02**: `make check-admitted` passes for all touched files
- [x] **INTG-03**: `make ccomp` succeeds (compiler binary builds end-to-end)

## v2 Requirements

### Proof Quality

- **PQLTY-01**: Unified solve_match_rs Ltac tactic for repetitive proof patterns
- **PQLTY-02**: Auto hint database for Regset.In membership goals

## Out of Scope

| Feature | Reason |
|---------|--------|
| Extending fault tolerance proof to assembly level | Separate research problem; different color system needed per backend |
| Modifying Liveness.v | Used by DCE, register allocation; changing it breaks those passes |
| Proving check_col_instr_sound completeness | Only soundness needed; completeness requires oracle axioms |
| Redesigning RTLinfercolor.ml | Already functional with sparse liveness-bounded inference |
| Changing DMR pass or DMR proof | TMR path only for this milestone |

## Traceability

| Requirement | Phase | Status |
|-------------|-------|--------|
| PLIV-01 | Phase 1 | Complete |
| PLIV-02 | Phase 1 | Complete |
| PLIV-03 | Phase 1 | Complete |
| PLIV-04 | Phase 1 | Complete |
| PLIV-05 | Phase 1 | Complete |
| COLR-01 | Phase 2 | Complete |
| COLR-02 | Phase 2 | Complete |
| COLR-03 | Phase 2 | Complete |
| COLR-04 | Phase 2 | Complete |
| FSIM-01 | Phase 3 | Complete |
| FSIM-02 | Phase 3 | Complete |
| FSIM-03 | Phase 3 | Complete |
| FSIM-04 | Phase 3 | Complete |
| FSIM-05 | Phase 3 | Complete |
| FSIM-06 | Phase 3 | Complete |
| FSIM-07 | Phase 3 | Complete |
| FSIM-08 | Phase 3 | Complete |
| INTG-01 | Phase 4 | Complete |
| INTG-02 | Phase 4 | Complete |
| INTG-03 | Phase 4 | Complete |

**Coverage:**
- v1 requirements: 20 total
- Mapped to phases: 20
- Unmapped: 0 ✓

---
*Requirements defined: 2026-03-04*
*Last updated: 2026-03-04 after initial definition*
