# Roadmap: Improved Builtin Treatment in TMR

## Overview

This project relaxes CompCert's fault-tolerance extension so that pure, total builtins participate in Triple Modular Redundancy the same way safe `Iop` instructions do. The work proceeds in three phases: first establish the shared classification and validate that the `val_compat`-based fault model supports it (risk gate); then apply the classification across TMR pass, color system, and faulty semantics simultaneously (parallel subsystem updates); finally close the tolerant proof that synthesizes all components into the end-to-end theorem.

## Phases

**Phase Numbering:**
- Integer phases (1, 2, 3): Planned milestone work
- Decimal phases (2.1, 2.2): Urgent insertions (marked with INSERTED)

Decimal phases appear between their surrounding integers in numeric order.

- [x] **Phase 1: Classification and Semantic Foundation** - Define the single shared classification and prove it is sound under the fault model
- [ ] **Phase 2: Subsystem Updates** - Apply classification to TMR pass, color system, and faulty semantics
- [ ] **Phase 3: Tolerant Proof and Final Integration** - Close the faulted backward simulation with new builtin cases and verify full build

## Phase Details

### Phase 1: Classification and Semantic Foundation
**Goal**: A single, validated builtin classification exists that all downstream components can import, and the semantic property required by the fault model is proved
**Depends on**: Nothing (first phase)
**Requirements**: CLAS-01, CLAS-02, CLAS-03, CLAS-04, CLAS-05, CLAS-06, CLAS-07, SEMA-01, SEMA-02, SEMA-03
**Success Criteria** (what must be TRUE):
  1. `builtin_can_replicate` and `builtin_can_fault` are defined in `common/Builtins.v` and return correct results for all 22 safe builtins, all partial builtins, and all protocol builtins
  2. Reflection lemmas bridge Bool and Prop for both predicates, following the `is_protectedb_spec` pattern
  3. `builtin_sem_val_compat` is proved for `mkbuiltin_nNt` builtins: given `val_compat`-related inputs, the builtin produces `val_compat`-related outputs
  4. `builtin_sem_val_compat` is proved for `mkbuiltin_v2t` builtins (`BI_mull`, `BI_addl`, `BI_subl`, shifts) with the same property
  5. Protocol recognizers (`smove`, `vote`, `check`) are accessible from `common/Builtins.v` and explicitly excluded from the safe classification
**Plans**: 3 plans

Plans:
- [x] 01-01-PLAN.md — Define classification predicates and reflection lemmas in common/Builtins.v
- [x] 01-02-PLAN.md — Migrate protocol recognizers from backend/RTL.v to common/Builtins.v
- [x] 01-03-PLAN.md — Prove val_compat monotonicity for safe builtins in backend/RTLfault.v

### Phase 2: Subsystem Updates
**Goal**: TMR pass replicates safe builtins, color system accepts replicated safe builtins with basic colors, and faulty semantics allows faults on safe builtins
**Depends on**: Phase 1
**Requirements**: TMR-01, TMR-02, TMR-03, TMR-04, TMR-05, TMR-06, COLR-01, COLR-02, COLR-03, COLR-04, FALT-01, FALT-02, INTG-01, INTG-02, INTG-03, INTG-04
**Success Criteria** (what must be TRUE):
  1. `transf_instr` in `RTLtmr.v` emits per-color copies for safe builtins and the TMR spec has a `match_Ibuiltin_safe` case, with `RTLtmr.vo` and `RTLtmrproof.vo` building successfully
  2. `wc_Ibuiltin_safe` exists in `RTLcolor.v`, the checker accepts replicated safe builtins with basic colors, and the oracle infers basic colors for safe builtins, with `RTLcolor.vo` and `RTLcolorcheck.vo` building successfully
  3. `zap_allowed (Ibuiltin ef _ _ _)` returns `builtin_can_fault ef`, keeping protocol and White-only builtins non-faultable
  4. Non-replicable builtins (including `check`) and protocol builtins retain their existing treatment unchanged across all three subsystems
**Plans**: 3 plans

Plans:
- [ ] 02-01-PLAN.md — Add safe builtin triplication to TMR pass (RTLtmr.v) and match spec (RTLtmrspec.v)
- [ ] 02-02-PLAN.md — Prove TMR backward simulation for safe builtins (RTLtmrproof.v)
- [ ] 02-03-PLAN.md — Update color system (spec, checker, oracle) and faulty semantics for safe builtins

### Phase 3: Tolerant Proof and Final Integration
**Goal**: The faulted backward simulation handles safe-builtin cases and the full project builds with no admitted proofs
**Depends on**: Phase 1, Phase 2
**Requirements**: TOLR-01, TOLR-02, TOLR-03, INTG-05, INTG-06, INTG-07
**Success Criteria** (what must be TRUE):
  1. `exec_Ibuiltin` in `RTLtolerant.v` has a three-way case split (vote / safe / generic) with the safe-replicated-builtin case proved
  2. `RTLtolerant.vo` and `driver/Complements.vo` build successfully, confirming the main fault-tolerance theorem `transf_c_program_to_rtl_preservation_faulty` holds
  3. `make check-admitted` passes with zero admitted proofs
**Plans**: TBD

Plans:
- [ ] 03-01: TBD
- [ ] 03-02: TBD

## Progress

**Execution Order:**
Phases execute in numeric order: 1 -> 2 -> 3

| Phase | Plans Complete | Status | Completed |
|-------|----------------|--------|-----------|
| 1. Classification and Semantic Foundation | 3/3 | Complete | 2026-03-15 |
| 2. Subsystem Updates | 0/3 | Not started | - |
| 3. Tolerant Proof and Final Integration | 0/? | Not started | - |
