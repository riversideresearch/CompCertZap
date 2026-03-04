# Roadmap: CompCertZAP Liveness-Bounded Proof

## Overview

This roadmap replaces the overly-coarse register invariant in the CompCertZAP fault tolerance proof with a liveness-bounded invariant. The work flows from a new standalone dataflow analysis (ProofLiveness.v), through the color system and simulation proof in parallel, to a final integration and validation phase. Every phase delivers a verifiable Coq compilation target with zero Admitted proofs.

## Phases

**Phase Numbering:**
- Integer phases (1, 2, 3): Planned milestone work
- Decimal phases (2.1, 2.2): Urgent insertions (marked with INSERTED)

Decimal phases appear between their surrounding integers in numeric order.

- [ ] **Phase 1: ProofLiveness Analysis** - Create conservative liveness analysis with fixpoint proof and membership lemmas
- [ ] **Phase 2: Color System Update** - Swap analysis reference in RTLcolor/RTLcolorcheck and complete checker soundness proof
- [ ] **Phase 3: Faulty Simulation Proof** - Rebuild RTLtolerant backward simulation with liveness-bounded match relation
- [ ] **Phase 4: Integration and Validation** - Rebuild Complements.v and validate end-to-end compiler build

## Phase Details

### Phase 1: ProofLiveness Analysis
**Goal**: A standalone backward dataflow analysis exists that conservatively over-approximates register liveness, including Iop/Iload arguments unconditionally, and its fixpoint and membership properties are machine-checked
**Depends on**: Nothing (first phase)
**Requirements**: PLIV-01, PLIV-02, PLIV-03, PLIV-04, PLIV-05
**Success Criteria** (what must be TRUE):
  1. `ProofLiveness.transfer` includes Iop args and Iload args in the live set regardless of whether the destination register is live
  2. `make backend/ProofLiveness.vo` succeeds with zero Admitted proofs
  3. `analyze_solution` theorem is proved: for every CFG edge (pc, succ), the fixpoint satisfies the transfer function monotonicity property
  4. `reg_list_live_in` membership lemma is proved: `In r args -> Regset.In r (reg_list_live args s)`
**Plans:** 1 plan

Plans:
- [ ] 01-01-PLAN.md -- Create ProofLiveness.v with conservative transfer, solver instantiation, fixpoint proof, and membership lemma; register in Makefile

### Phase 2: Color System Update
**Goal**: The well-coloredness specification and Boolean checker reference ProofLiveness.analyze, and the checker soundness proof (check_col_instr_sound) is fully machine-checked with no Admitted
**Depends on**: Phase 1
**Requirements**: COLR-01, COLR-02, COLR-03, COLR-04
**Success Criteria** (what must be TRUE):
  1. `wc_function` in RTLcolor.v uses `ProofLiveness.analyze` (not `Liveness.analyze`) to determine the live set
  2. `check_function` in RTLcolorcheck.v uses `ProofLiveness.analyze` (not `Liveness.analyze`) to compute liveness
  3. `check_col_instr_sound` is proved for all 14 instruction cases with no Admitted
  4. `make backend/RTLcolor.vo && make backend/RTLcolorcheck.vo` succeeds with zero Admitted in both files
**Plans:** 1 plan

Plans:
- [ ] 02-01-PLAN.md -- Swap Liveness to ProofLiveness in RTLcolor.v and RTLcolorcheck.v; complete check_col_instr_sound proof

### Phase 3: Faulty Simulation Proof
**Goal**: The faulty backward simulation in RTLtolerant.v is fully proved using the liveness-bounded match relation parameterized by ProofLiveness.analyze, with no Admitted lemmas
**Depends on**: Phase 1
**Requirements**: FSIM-01, FSIM-02, FSIM-03, FSIM-04, FSIM-05, FSIM-06, FSIM-07, FSIM-08
**Success Criteria** (what must be TRUE):
  1. `match_states` and `match_stackframes` reference `ProofLiveness.analyze` for the LIVE hypothesis
  2. `step_simulation` is proved for all RTL instruction cases (Inop, Iop, Iload, Istore, Icall, Itailcall, Ibuiltin, Icond, Ijumptable, Ireturn, plus vote sub-cases)
  3. `faulty_progress` is proved for all instruction cases
  4. `faulty_backward_simulation` theorem is proved, composing step_simulation and faulty_progress
  5. `make backend/RTLtolerant.vo` succeeds with zero Admitted proofs
**Plans**: TBD

Plans:
- [ ] 03-01: TBD

### Phase 4: Integration and Validation
**Goal**: The top-level theorem chain composes successfully and the compiler binary builds end-to-end, confirming the liveness-bounded proof integrates with the full CompCert pipeline
**Depends on**: Phase 2, Phase 3
**Requirements**: INTG-01, INTG-02, INTG-03
**Success Criteria** (what must be TRUE):
  1. `make driver/Complements.vo` succeeds (transf_c_program_to_rtl_preservation_faulty theorem fully grounded)
  2. `make check-admitted` passes for all touched files (ProofLiveness.v, RTLcolor.v, RTLcolorcheck.v, RTLtolerant.v, Complements.v)
  3. `make ccomp` succeeds and the resulting ccomp binary can compile a test C program with `-tmr` flag
**Plans**: TBD

Plans:
- [ ] 04-01: TBD

## Progress

**Execution Order:**
Phases execute in numeric order: 1 -> 2 -> 3 -> 4
Note: Phase 2 and Phase 3 are independent and can execute in parallel after Phase 1 completes.

| Phase | Plans Complete | Status | Completed |
|-------|----------------|--------|-----------|
| 1. ProofLiveness Analysis | 1/1 | Complete | 2026-03-04 |
| 2. Color System Update | 0/1 | Planned | - |
| 3. Faulty Simulation Proof | 0/? | Not started | - |
| 4. Integration and Validation | 0/? | Not started | - |
