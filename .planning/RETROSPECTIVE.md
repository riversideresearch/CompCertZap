# Project Retrospective

*A living document updated after each milestone. Lessons feed forward into future planning.*

## Milestone: v1.0 -- Liveness-Bounded Fault Tolerance Proof

**Shipped:** 2026-03-05
**Phases:** 4 | **Plans:** 4 | **Tasks:** 8

### What Was Built
- ProofLiveness.v: conservative backward liveness analysis with Kildall solver, fixpoint proof, membership lemmas
- Color system updated: RTLcolor.v + RTLcolorcheck.v swapped to ProofLiveness.analyze, 14-case checker proof completed
- Faulty backward simulation fully proved with liveness-bounded match relation in RTLtolerant.v
- End-to-end integration: Complements.vo compiles, zero Admitted, ccomp binary builds with -tmr support

### What Worked
- 4-phase structure with clear dependency ordering (Phase 1 foundation -> Phases 2+3 parallel -> Phase 4 integration)
- Creating ProofLiveness.v as standalone module avoided any disruption to existing Liveness.v consumers (DCE, regalloc)
- Save-before-inv pattern in RTLtolerant.v prevented Coq variable consumption issues during complex case analysis
- Phase 4 integration was trivial (1 min) because Phases 1-3 maintained clean interfaces

### What Was Inefficient
- Phase 3 (faulty simulation) took 267 min vs 2-7 min for other phases -- the proof required extensive manual case analysis across 10+ RTL instruction forms plus vote sub-cases
- Some rework in Phase 3 due to discovering ProofLiveness.transfer needed a fix for Ibuiltin (BR_splitlong/BR_none handling)

### Patterns Established
- Conservative transfer function pattern: always over-approximate liveness for proof purposes
- Regset.for_all_2 bridge pattern for boolean-to-propositional color checker proofs
- compat_bool_tac with ?-prefixed names to avoid variable capture

### Key Lessons
1. A separate proof-specific analysis (ProofLiveness) is better than modifying shared infrastructure (Liveness) -- keeps other passes stable
2. The Ibuiltin case in backward simulation is the hardest due to builtin result patterns (BR, BR_splitlong, BR_none) -- budget extra time for it
3. Coq destructive tactics (inv, subst) require careful ordering -- save facts before destruction

### Cost Observations
- Model mix: 100% opus (quality profile)
- Total execution time: ~4.6 hours (dominated by Phase 3 proof work)
- Notable: Phases 1, 2, 4 were fast (<10 min each); Phase 3 was the critical path

---

## Cross-Milestone Trends

### Process Evolution

| Milestone | Phases | Plans | Key Change |
|-----------|--------|-------|------------|
| v1.0 | 4 | 4 | Initial milestone -- established proof-specific analysis pattern |

### Cumulative Quality

| Milestone | Admitted Count | Files Touched | New Files |
|-----------|---------------|---------------|-----------|
| v1.0 | 0 | 6 | 1 (ProofLiveness.v) |

### Top Lessons (Verified Across Milestones)

1. Separate proof-specific infrastructure from shared compiler infrastructure
2. Budget 10x for backward simulation proofs vs other proof work
