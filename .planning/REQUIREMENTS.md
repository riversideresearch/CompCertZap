# Requirements: CompCert Proof Cleanup

**Defined:** 2026-03-03
**Core Value:** All Coq proofs continue to compile cleanly after every change — no regressions, no new Admitted proofs.

## v1 Requirements

Requirements for this cleanup cycle. Each maps to roadmap phases.

### File Cleanup

- [ ] **FILE-01**: All 13 untracked backup files are deleted from backend/ and driver/
- [ ] **FILE-02**: backend/AdvSem.v is removed after reference/build verification
- [ ] **FILE-03**: backend/Replicate3proof.v is removed after reference/build verification
- [x] **FILE-04**: Baseline health record captured (make check-admitted + targeted .vo builds)

### Module Reorganization

- [ ] **MOD-01**: backend/RTLreplicateSpecCommon.v created with shared spec tactics and definitions extracted from RTLdmrspec.v and RTLtmrspec.v
- [ ] **MOD-02**: backend/RTLreplicateProofCommon.v created with shared proof lemmas extracted from RTLdmrproof.v and RTLtmrproof.v
- [ ] **MOD-03**: RTLdmrspec.v and RTLtmrspec.v import from RTLreplicateSpecCommon.v instead of duplicating
- [ ] **MOD-04**: RTLdmrproof.v and RTLtmrproof.v import from RTLreplicateProofCommon.v instead of duplicating

### Spec Strengthening

- [ ] **SPEC-01**: Relational spec defined for DMR replication-map construction in RTLdmrspec.v
- [ ] **SPEC-02**: Relational spec defined for TMR replication-map construction in RTLtmrspec.v
- [ ] **SPEC-03**: Monolithic replication_map_wf_aux proof in RTLdmrspec.v replaced with spec + impl + consequence composition
- [ ] **SPEC-04**: Monolithic replication_map_wf_aux proof in RTLtmrspec.v replaced with spec + impl + consequence composition

### Proof De-duplication

- [ ] **DEDUP-01**: no_votes_external_call in Novotesproof.v refactored from 8 repeats to helper lemma + driver
- [ ] **DEDUP-02**: maj_voteR_step in RTLtmrproof.v refactored from four-case duplication to parametric lemma
- [ ] **DEDUP-03**: external_call_vote_lessdef in RTLtolerant.v refactored from four identical cases to type-parametric lemma
- [ ] **DEDUP-04**: Deprecated external_call_Three_Two removed from RTLtolerant.v after migrating all 3 call sites to external_call_Three_Two'
- [ ] **DEDUP-05**: check_col_instr_sound in RTLcolorcheck.v broken into per-instruction lemmas

### Comment & Tactic Hygiene

- [ ] **HYG-01**: Large commented-out abandoned proof blocks removed from RTLtolerant.v
- [ ] **HYG-02**: Large commented-out blocks removed from RTLagreement.v
- [ ] **HYG-03**: Commented-out blocks removed from RTLtmr.v
- [ ] **HYG-04**: Commented-out blocks removed from driver/Complements.v (keep distilled design notes for vote-parametric RTL->Asm forward-sim sketch and asm weak-agreement proof direction sketch; delete other stubs)
- [ ] **HYG-05**: Commented-out blocks removed from RTLcolorcheck.v
- [ ] **HYG-06**: Commented-out blocks removed from Novotes.v
- [ ] **HYG-07**: Commented-out blocks removed from RTLfault.v
- [ ] **HYG-08**: All TODO markers in in-scope files resolved or removed (excluding CSEproof.v)
- [ ] **HYG-09**: Naming conventions aligned between DMR and TMR helper functions where semantics match

## v2 Requirements

Deferred to future cleanup cycle. Tracked but not in current roadmap.

### Cross-Pass Policy

- **XPASS-01**: Unify no_votes handling across CSEproof.v, RTLagreement.v, and Complements.v
- **XPASS-02**: Resolve CSEproof.v TODO (line ~1574) — decide if Novotes hypothesis needed or mark stale

### Structural

- **STRUCT-01**: Split RTLtolerant.v into focused modules (match relations, helpers, main simulation)

## Out of Scope

| Feature | Reason |
|---------|--------|
| New compiler features or passes | This is maintenance/cleanup only |
| Build time optimization | Different concern, separate effort |
| Touching non-fault-tolerance CompCert files | Minimize blast radius; only touch standard files if forced by dependency |
| Compatibility shim lemmas | Cleanup plan explicitly forbids — change signatures directly and migrate callers |
| Using Admitted as progress placeholder | Would break soundness invariant (currently 0 active Admitted) |
| CSEproof.v TODO resolution | Requires cross-pass architecture decision deferred to v2 |

## Traceability

| Requirement | Phase | Status |
|-------------|-------|--------|
| FILE-01 | Phase 1 - Baseline and File Cleanup | Pending |
| FILE-02 | Phase 1 - Baseline and File Cleanup | Pending |
| FILE-03 | Phase 1 - Baseline and File Cleanup | Pending |
| FILE-04 | Phase 1 - Baseline and File Cleanup | Complete |
| MOD-01 | Phase 2 - Shared Module Introduction | Pending |
| MOD-02 | Phase 2 - Shared Module Introduction | Pending |
| MOD-03 | Phase 2 - Shared Module Introduction | Pending |
| MOD-04 | Phase 2 - Shared Module Introduction | Pending |
| SPEC-01 | Phase 3 - Spec Strengthening | Pending |
| SPEC-02 | Phase 3 - Spec Strengthening | Pending |
| SPEC-03 | Phase 3 - Spec Strengthening | Pending |
| SPEC-04 | Phase 3 - Spec Strengthening | Pending |
| DEDUP-01 | Phase 4 - Proof De-duplication | Pending |
| DEDUP-02 | Phase 4 - Proof De-duplication | Pending |
| DEDUP-03 | Phase 4 - Proof De-duplication | Pending |
| DEDUP-04 | Phase 4 - Proof De-duplication | Pending |
| DEDUP-05 | Phase 4 - Proof De-duplication | Pending |
| HYG-01 | Phase 5 - Comment and Tactic Hygiene | Pending |
| HYG-02 | Phase 5 - Comment and Tactic Hygiene | Pending |
| HYG-03 | Phase 5 - Comment and Tactic Hygiene | Pending |
| HYG-04 | Phase 5 - Comment and Tactic Hygiene | Pending |
| HYG-05 | Phase 5 - Comment and Tactic Hygiene | Pending |
| HYG-06 | Phase 5 - Comment and Tactic Hygiene | Pending |
| HYG-07 | Phase 5 - Comment and Tactic Hygiene | Pending |
| HYG-08 | Phase 5 - Comment and Tactic Hygiene | Pending |
| HYG-09 | Phase 5 - Comment and Tactic Hygiene | Pending |

**Coverage:**
- v1 requirements: 27 total
- Mapped to phases: 27
- Unmapped: 0

---
*Requirements defined: 2026-03-03*
*Last updated: 2026-03-03 after 01-01-PLAN.md completion*
