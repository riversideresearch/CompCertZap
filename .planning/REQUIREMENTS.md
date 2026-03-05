# Requirements: CompCertZAP No-Novotes Proof Composition

**Defined:** 2026-03-05
**Core Value:** Faulty backward simulation proof compiles with no Admitted using liveness-bounded register match invariant

## v2.0 Requirements

Requirements for removing novotes dependency from the RTL fault-tolerance proof composition.

### Bridge Proof

- [x] **BRIDGE-01**: RTL3 step simulation to RTL step under lessdef register relation (no no_votes)
- [x] **BRIDGE-02**: Behavior-level corollary: RTL3 behaviors refined by RTL behaviors
- [x] **BRIDGE-03**: Call-level bridge lemma: external_call3 matched by external_call with lessdef result

### Pipeline

- [x] **PIPE-01**: Remove Novotes.transf_program from transf_rtl_program in Compiler.v
- [x] **PIPE-02**: Remove Novotes.transf_program from transf_rtl_program_to_rtl in Compiler.v
- [x] **PIPE-03**: Update pass-match and correctness proofs in Compiler.v for simplified pipeline

### Theorem

- [ ] **THERM-01**: Rewrite transf_c_program_to_rtl_preservation_faulty with 3-step composition
- [ ] **THERM-02**: Remove obsolete novotes-dependent lemmas from Complements.v
- [ ] **THERM-03**: Clean up dead Novotes/Novotesproof imports

### Validation

- [ ] **VALID-01**: All .vo files compile (RTLagreement, Compiler, RTLtolerant, Complements)
- [ ] **VALID-02**: Zero Admitted proofs across all touched files
- [ ] **VALID-03**: ccomp binary builds and compiles C with -tmr flag
- [ ] **VALID-04**: No residual Novotes references in active pipeline definitions

### Documentation

- [ ] **DOC-01**: Technical report at doc/no-novotes-report.md covering rationale, architecture, and validation

## v3 Requirements

Deferred to future release.

### Asm-Level Fault Tolerance

- **ASM-01**: Fault tolerance proof extended to RISC-V assembly level
- **ASM-02**: Asm-level color system and checker
- **ASM-03**: Faulty asm semantics and backward simulation

## Out of Scope

| Feature | Reason |
|---------|--------|
| Asm-level fault tolerance | Separate future milestone (see plans/riscv-fault-tolerance.md) |
| DMR pass changes | TMR path only |
| Performance benchmarking | Optional validation only |
| Modifying upstream Liveness.v | Used by DCE and register allocation |

## Traceability

| Requirement | Phase | Status |
|-------------|-------|--------|
| BRIDGE-01 | Phase 5 | Complete |
| BRIDGE-02 | Phase 5 | Complete |
| BRIDGE-03 | Phase 5 | Complete |
| PIPE-01 | Phase 6 | Complete |
| PIPE-02 | Phase 6 | Complete |
| PIPE-03 | Phase 6 | Complete |
| THERM-01 | Phase 7 | Pending |
| THERM-02 | Phase 7 | Pending |
| THERM-03 | Phase 7 | Pending |
| VALID-01 | Phase 8 | Pending |
| VALID-02 | Phase 8 | Pending |
| VALID-03 | Phase 8 | Pending |
| VALID-04 | Phase 8 | Pending |
| DOC-01 | Phase 9 | Pending |

**Coverage:**
- v2.0 requirements: 14 total
- Mapped to phases: 14
- Unmapped: 0

---
*Requirements defined: 2026-03-05*
*Last updated: 2026-03-05 after Phase 5 Plan 1 completion*
