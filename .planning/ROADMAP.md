# Roadmap: CompCertZAP Liveness-Bounded Proof

## Milestones

- v1.0 **Liveness-Bounded Fault Tolerance Proof** -- Phases 1-4 (shipped 2026-03-05)
- v2.0 **No-Novotes Proof Composition** -- Phases 5-9 (in progress)

## Phases

<details>
<summary>v1.0 Liveness-Bounded Fault Tolerance Proof (Phases 1-4) -- SHIPPED 2026-03-05</summary>

- [x] Phase 1: ProofLiveness Analysis (1/1 plans) -- completed 2026-03-04
- [x] Phase 2: Color System Update (1/1 plans) -- completed 2026-03-04
- [x] Phase 3: Faulty Simulation Proof (1/1 plans) -- completed 2026-03-04
- [x] Phase 4: Integration and Validation (1/1 plans) -- completed 2026-03-05

</details>

### v2.0 No-Novotes Proof Composition (In Progress)

**Milestone Goal:** Remove the novotes dependency from the RTL fault-tolerance proof, replacing the 4-step composition (C >= RTL2 >= RTL3 >= RTL3+TMR >= faulty RTL2+TMR) with a direct 3-step composition (C >= RTL >= RTL+TMR >= faulty RTL+TMR) by proving a generic RTL3-to-RTL bridge that does not require a no_votes premise.

- [x] **Phase 5: RTL3-to-RTL Bridge** - Prove generic forward simulation from RTL3 to RTL semantics without no_votes
- [x] **Phase 6: Pipeline Simplification** - Remove Novotes pass from Compiler.v transf_rtl_program
- [ ] **Phase 7: Theorem Recomposition** - Rewrite transf_c_program_to_rtl_preservation_faulty as 3-step composition
- [ ] **Phase 8: Validation and Cleanup** - Full build validation: all .vo compile, zero Admitted, ccomp builds
- [ ] **Phase 9: Technical Report** - Document the no-novotes refactor rationale and architecture

## Phase Details

### Phase 5: RTL3-to-RTL Bridge
**Goal**: A proven backward simulation theorem in RTLagreement.v (or new file) showing that any RTL3 program behavior is refined by the corresponding RTL program behavior, using Val.lessdef on registers -- without requiring that the program has no vote instructions
**Depends on**: Phase 4 (v1.0 complete)
**Requirements**: BRIDGE-01, BRIDGE-02, BRIDGE-03
**Success Criteria** (what must be TRUE):
  1. A step-simulation lemma exists proving RTL3 step is matched by RTL step under a lessdef register relation, with no no_votes hypothesis
  2. A behavior-level corollary exists proving backward_simulation (or forward_simulation + determinate) between RTL3 semantics and RTL semantics for any well-typed program
  3. An external_call bridge lemma exists showing external_call3 results are matched by external_call results under Val.lessdef
  4. All new lemmas compile to .vo with zero Admitted
**Plans**: 1 plan

Plans:
- [x] 05-01-PLAN.md -- Prove forward simulation RTL3 -> RTL with Val.lessdef/Mem.extends match, external_call3 bridge, and behavior-level corollary

### Phase 6: Pipeline Simplification
**Goal**: Compiler.v no longer applies Novotes.transf_program in either transf_rtl_program or transf_rtl_program_to_rtl, and all pass-match/correctness lemmas in Compiler.v still compile
**Depends on**: Phase 5
**Requirements**: PIPE-01, PIPE-02, PIPE-03
**Success Criteria** (what must be TRUE):
  1. transf_rtl_program in Compiler.v does not mention Novotes.transf_program
  2. transf_rtl_program_to_rtl in Compiler.v does not mention Novotes.transf_program
  3. Compiler.vo compiles successfully with updated pass_match and correctness proof obligations
**Plans**: 1 plan

Plans:
- [x] 06-01-PLAN.md -- Remove Novotes from Compiler.v and Complements.v pipeline definitions, fix match proofs, use Phase 5 bridge

### Phase 7: Theorem Recomposition
**Goal**: transf_c_program_to_rtl_preservation_faulty in Complements.v uses a 3-step composition (standard backward sim, TMR backward sim, faulty backward sim) via the Phase 5 bridge instead of the old 4-step chain that depended on no_votes
**Depends on**: Phase 6
**Requirements**: THERM-01, THERM-02, THERM-03
**Success Criteria** (what must be TRUE):
  1. transf_c_program_to_rtl_preservation_faulty in Complements.v is proved with a 3-step composition: C >= RTL >= RTL+TMR >= faulty RTL+TMR
  2. No lemma in Complements.v references Novotes, Novotesproof, or any no_votes predicate
  3. Complements.vo compiles with zero Admitted
**Plans**: 1 plan

Plans:
- [ ] 07-01-PLAN.md -- Prove faulty theorem via 3-step behavior composition and remove dead Novotes references

### Phase 8: Validation and Cleanup
**Goal**: Full end-to-end validation confirming the entire Coq development compiles, contains no Admitted proofs, the ccomp binary builds, and no residual Novotes references remain in the active pipeline
**Depends on**: Phase 7
**Requirements**: VALID-01, VALID-02, VALID-03, VALID-04
**Success Criteria** (what must be TRUE):
  1. `make proof` succeeds: RTLagreement.vo, Compiler.vo, RTLtolerant.vo, and Complements.vo all compile
  2. `make check-admitted` reports zero Admitted proofs across all touched files
  3. `make ccomp` produces a working binary and `./ccomp test.c -tmr -o test` succeeds
  4. Grepping for `Novotes` in Compiler.v and Complements.v returns zero matches (dead code removed)
**Plans**: TBD

Plans:
- [ ] 08-01: Full build validation and Novotes residue cleanup

### Phase 9: Technical Report
**Goal**: A comprehensive technical report at doc/no-novotes-report.md documenting the motivation, architecture changes, proof structure, and validation results of the no-novotes refactor
**Depends on**: Phase 8
**Requirements**: DOC-01
**Success Criteria** (what must be TRUE):
  1. doc/no-novotes-report.md exists and covers: rationale for removing novotes, new bridge proof architecture, 3-step composition structure, and validation results
  2. The report includes before/after diagrams of the proof composition chain
**Plans**: TBD

Plans:
- [ ] 09-01: Write technical report

## Progress

**Execution Order:**
Phases execute in numeric order: 5 -> 6 -> 7 -> 8 -> 9

| Phase | Milestone | Plans Complete | Status | Completed |
|-------|-----------|----------------|--------|-----------|
| 1. ProofLiveness Analysis | v1.0 | 1/1 | Complete | 2026-03-04 |
| 2. Color System Update | v1.0 | 1/1 | Complete | 2026-03-04 |
| 3. Faulty Simulation Proof | v1.0 | 1/1 | Complete | 2026-03-04 |
| 4. Integration and Validation | v1.0 | 1/1 | Complete | 2026-03-05 |
| 5. RTL3-to-RTL Bridge | v2.0 | 1/1 | Complete | 2026-03-05 |
| 6. Pipeline Simplification | v2.0 | 1/1 | Complete | 2026-03-05 |
| 7. Theorem Recomposition | v2.0 | 0/1 | Not started | - |
| 8. Validation and Cleanup | v2.0 | 0/1 | Not started | - |
| 9. Technical Report | v2.0 | 0/1 | Not started | - |

---
*Full v1.0 details: .planning/milestones/v1.0-ROADMAP.md*
