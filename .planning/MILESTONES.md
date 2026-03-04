# Milestones

## v1.0 CompCert Proof Cleanup and Reorganization (Shipped: 2026-03-04)

**Phases:** 5 | **Plans:** 12 | **Commits:** 61
**Source changes:** 13 files, +926/-1093 lines (net -167)
**Timeline:** 2 days (2026-03-03 → 2026-03-04)
**Git range:** cleanup-rtl branch, 61 commits
**Requirements:** 24/27 satisfied (3 deliberately abandoned)

**Key accomplishments:**
1. Established clean proof baseline and deleted 16 dead files (14 backups + 2 stubs)
2. Created shared RTLreplicateSpecCommon.v and RTLreplicateProofCommon.v, eliminating ~280 lines of duplication
3. Replaced monolithic replication_map_wf_aux with relational spec decomposition in both DMR and TMR
4. Decomposed check_col_instr_sound into 14 per-instruction lemmas with 20-line dispatcher
5. Removed deprecated external_call_Three_Two and migrated all call sites
6. Cleaned comment blocks, resolved TODOs, and aligned DMR/TMR naming conventions

### Known Gaps

- **DEDUP-01**: `no_votes_external_call` 8-repeat proof (~170 lines) in Novotesproof.v — dedup blocked by Coq tactic memory explosion
- **DEDUP-02**: `maj_voteR_step` inline consolidation done but no named parametric lemma per ROADMAP spec
- **DEDUP-03**: `external_call_vote_lessdef` 4-case proof (~132 lines) in RTLtolerant.v — dedup blocked by Ltac hypothesis instability

All gaps are Coq proof automation limitations, not execution failures. Proofs compile correctly as-is.

---

