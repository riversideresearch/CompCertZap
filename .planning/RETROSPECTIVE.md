# Project Retrospective

*A living document updated after each milestone. Lessons feed forward into future planning.*

## Milestone: v1.0 — CompCert Proof Cleanup and Reorganization

**Shipped:** 2026-03-04
**Phases:** 5 | **Plans:** 12 | **Sessions:** ~5

### What Was Built
- Clean proof baseline with 16 dead files removed
- Shared modules (RTLreplicateSpecCommon.v, RTLreplicateProofCommon.v) centralizing DMR/TMR duplication
- Relational spec decomposition replacing monolithic replication_map_wf_aux in both DMR and TMR
- Per-instruction decomposition of check_col_instr_sound (14 lemmas + dispatcher)
- Deprecated lemma removal (external_call_Three_Two) with call site migration
- Comment/TODO cleanup and DMR/TMR naming alignment

### What Worked
- Dependency-aware phase ordering (shared modules → spec strengthening → de-duplication) prevented rework
- Small atomic commits with per-file verification (`make backend/<file>.vo`) caught issues early
- User review gates on comment cleanup (Phase 5) prevented over-deletion of intentional design notes
- `Require Export` pattern for shared modules gave downstream files clean unqualified access

### What Was Inefficient
- Phase 4 attempted three Ltac de-duplications; two failed due to Coq automation limits (memory explosion, hypothesis instability). Research phase could have flagged these risks earlier.
- ROADMAP progress table fell out of sync with actual completion (audit noted phases 3-5 showing "Not started" despite being complete)
- DEDUP-02 ROADMAP success criteria specified a "named parametric lemma" that wasn't achievable with the type-dispatch structure — criteria was too prescriptive

### Patterns Established
- "Verify via rg + build before deletion" — safe pattern for removing any Coq definition or file
- "Separate commits by type" — move-only commits vs. statement-change commits prevent hidden proof obligation changes
- "Design note conversion" — TODOs that can't be resolved become `(* Design note: ... *)` with rationale, not silent deletions

### Key Lessons
1. Coq Ltac automation has hard limits — `repeat + destruct` can cause exponential memory, `inv` generates unstable hypothesis names. Plan de-duplication with manual verification of tactic feasibility first.
2. Relational spec decomposition (inductive relation → foldM proof → consequence lemmas) is a reliable pattern for replacing monolithic proofs in Coq — applied twice successfully.
3. User review at Phase 5 comment cleanup was critical — several blocks that looked dead were intentional design documentation.
4. Prescriptive success criteria ("must create a lemma named X") can conflict with what's actually achievable — prefer functional criteria ("duplication reduced by N%") over naming requirements.

### Cost Observations
- Model mix: ~70% opus, ~20% haiku, ~10% sonnet (quality profile)
- Sessions: ~5 across 2 days
- Notable: Phases 1-2 averaged 3 min/plan; Phase 3 averaged 7.5 min/plan (proof development); Phase 4 had highest variance (4-30 min) due to abandoned attempts

---

## Cross-Milestone Trends

### Process Evolution

| Milestone | Sessions | Phases | Key Change |
|-----------|----------|--------|------------|
| v1.0 | ~5 | 5 | Initial cleanup cycle — established verify-before-delete and atomic commit patterns |

### Cumulative Quality

| Milestone | Admitted Proofs | Files Deleted | Net Lines |
|-----------|----------------|---------------|-----------|
| v1.0 | 0 | 16 | -167 |

### Top Lessons (Verified Across Milestones)

1. Coq proof automation has hard feasibility limits — research tactic behavior before planning de-duplication
2. Functional success criteria outperform prescriptive naming requirements
