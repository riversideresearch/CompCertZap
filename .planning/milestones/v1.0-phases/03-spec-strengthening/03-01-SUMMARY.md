---
phase: 03-spec-strengthening
plan: 01
subsystem: backend
tags: [coq, proof-refactoring, relational-spec, dmr, replication-map]

# Dependency graph
requires:
  - phase: 02-shared-module-introduction
    provides: RTLreplicateSpecCommon shared module
provides:
  - Relational specification (replication_map_rel) for DMR replication map
  - Decomposed proof: foldM_satisfies_rel + rel_implies_rm_wf
  - Shadow map injectivity lemma (replication_map_rel_injective)
  - elements_NoDup utility lemma
affects: [03-spec-strengthening, 04-proof-dedup]

# Tech tracking
tech-stack:
  added: []
  patterns: [relational-spec-then-consequence, range-separation-for-NoDup]

key-files:
  created: []
  modified: [backend/RTLdmrspec.v]

key-decisions:
  - "Added NoDup precondition to foldM_satisfies_rel (discharged via elements_NoDup from Regset.elements_3w)"
  - "Used replication_map_rel_set helper to handle PMap.set stability across PMap overwrite"
  - "Factored shadow injectivity into separate replication_map_rel_injective lemma for reuse"

patterns-established:
  - "Relational spec pattern: define inductive capturing per-step structure, then derive consequences (range, injectivity, rm_wf) separately"
  - "NoDup4_of_ranges: generic helper for proving 4-element NoDup from range separation"

requirements-completed: [SPEC-01, SPEC-03]

# Metrics
duration: 8min
completed: 2026-03-04
---

# Phase 03 Plan 01: DMR Relational Spec Summary

**Replaced monolithic replication_map_wf_aux with replication_map_rel inductive and two-step decomposed proof (foldM_satisfies_rel + rel_implies_rm_wf)**

## Performance

- **Duration:** 8 min
- **Started:** 2026-03-04T00:38:20Z
- **Completed:** 2026-03-04T00:46:45Z
- **Tasks:** 2
- **Files modified:** 1

## Accomplishments
- Defined `replication_map_rel` inductive with `rmr_nil` and `rmr_cons` constructors capturing per-step DMR register allocation
- Proved `foldM_satisfies_rel` linking the foldM computation to the relational spec
- Proved `rel_implies_rm_wf` deriving `rm_wf` purely from the relational spec via range separation
- Deleted the ~102-line monolithic `replication_map_wf_aux` proof
- Re-proved `replication_map_wf` via composition (type signature unchanged)
- Confirmed `RTLdmrproof.v` compiles unchanged against the new interface

## Task Commits

Each task was committed atomically:

1. **Task 1: Define replication_map_rel inductive and helper lemma** - `6b8028e5` (feat)
2. **Task 2: Replace replication_map_wf_aux with decomposed proofs** - `bfd54aee` (feat)

## Files Created/Modified
- `backend/RTLdmrspec.v` - Replaced monolithic proof with relational spec and decomposed lemmas

## Decisions Made
- Added `NoDup regs` precondition to `foldM_satisfies_rel` because PMap.set semantics require knowing the head register is not in the tail list. Discharged via `elements_NoDup` from `Regset.elements_3w`.
- Factored shadow map injectivity into a separate `replication_map_rel_injective` lemma (not in original plan) for clarity and potential reuse by TMR spec strengthening.
- Added `replication_map_rel_set` helper lemma (not in original plan) to handle the PMap.set stability needed in `foldM_satisfies_rel`.
- Added `replication_map_rel_lo_le_hi` as a trivial bound lemma needed by `replication_map_rel_range`.
- Added `NoDup4_of_ranges` as a generic helper for proving 4-element NoDup from range separation.
- Added `elements_NoDup` utility deriving `NoDup` from `Regset.elements_3w` (NoDupA).

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 2 - Missing Critical] Added replication_map_rel_set helper**
- **Found during:** Task 2 (foldM_satisfies_rel proof)
- **Issue:** The relational spec for the tail uses the pre-PMap.set map, but rmr_cons requires facts about the post-PMap.set map. A stability lemma was needed.
- **Fix:** Added `replication_map_rel_set` proving that PMap.set for a key outside the register list preserves the relation.
- **Files modified:** backend/RTLdmrspec.v
- **Verification:** RTLdmrspec.vo compiles
- **Committed in:** bfd54aee (Task 2 commit)

**2. [Rule 2 - Missing Critical] Added replication_map_rel_injective helper**
- **Found during:** Task 2 (rel_implies_rm_wf proof)
- **Issue:** The NoDup proof requires `rm # r <> rm # r'` for distinct `r, r'`, which needs injectivity proven by induction on the relational spec.
- **Fix:** Added `replication_map_rel_injective` as a separate lemma proving shadow injectivity from the inductive structure.
- **Files modified:** backend/RTLdmrspec.v
- **Verification:** RTLdmrspec.vo compiles
- **Committed in:** bfd54aee (Task 2 commit)

**3. [Rule 2 - Missing Critical] Added NoDup4_of_ranges and elements_NoDup helpers**
- **Found during:** Task 2 (rel_implies_rm_wf and replication_map_wf proofs)
- **Issue:** The NoDup [r; sr; r'; sr'] construction needed a clean helper, and NoDup for Regset.elements was needed to discharge preconditions.
- **Fix:** Added both utility lemmas.
- **Files modified:** backend/RTLdmrspec.v
- **Verification:** RTLdmrspec.vo and RTLdmrproof.vo compile
- **Committed in:** bfd54aee (Task 2 commit)

---

**Total deviations:** 3 auto-fixed (all missing critical helpers for proof decomposition)
**Impact on plan:** All auto-fixes were necessary to complete the planned decomposition. No scope creep -- all helpers are minimal and directly serve the relational spec pattern.

## Issues Encountered
None

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- Relational spec pattern established and proven for DMR
- Same pattern can be applied to TMR spec strengthening in plan 03-02
- `replication_map_rel_injective` and `NoDup4_of_ranges` may be directly reusable

## Self-Check: PASSED

- [x] backend/RTLdmrspec.v exists
- [x] Commit 6b8028e5 (Task 1) exists
- [x] Commit bfd54aee (Task 2) exists
- [x] replication_map_wf_aux count = 0 (deleted)
- [x] replication_map_rel count = 25 (>= 3)
- [x] Inductive replication_map_rel = 1
- [x] foldM_satisfies_rel = 2 (definition + use)
- [x] rel_implies_rm_wf = 2 (definition + use)
- [x] make check-admitted: Nothing admitted

---
*Phase: 03-spec-strengthening*
*Completed: 2026-03-04*
