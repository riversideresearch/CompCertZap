---
phase: 06-pipeline-simplification
plan: 01
subsystem: compiler-pipeline
tags: [coq, pipeline, novotes, simplification]

# Dependency graph
requires:
  - phase: 05-rtl3-to-rtl-bridge
    provides: "rtl_weak_agreement' unconditionally (no no_votes requirement)"
provides:
  - "Compiler pipeline without Novotes pass -- transf_rtl_program ends at Unusedglob"
  - "Complements.v cleaned of Novotes dependencies and unused lemmas"
affects: [07-theorem-composition, integration-and-validation]

# Tech tracking
tech-stack:
  added: []
  patterns: ["Pipeline simplification via pass removal"]

key-files:
  created: []
  modified:
    - driver/Compiler.v
    - driver/Complements.v

key-decisions:
  - "Novotes pass removed entirely (not just bypassed) since Phase 5 bridge proves rtl_weak_agreement' unconditionally"
  - "Deleted transf_c_program_to_rtl'_no_votes and transf_c_program_to_rtl'_preservation' -- Phase 7 will reconstruct with correct types"

patterns-established:
  - "Pipeline ends at Unusedglob before DMR/TMR insertion"

requirements-completed: [PIPE-01, PIPE-02, PIPE-03]

# Metrics
duration: 3min
completed: 2026-03-05
---

# Phase 6 Plan 1: Pipeline Simplification Summary

**Removed Novotes checker pass from both Compiler.v pipelines and cleaned Complements.v of all Novotes dependencies and unused lemmas**

## Performance

- **Duration:** 3 min
- **Started:** 2026-03-05T16:54:11Z
- **Completed:** 2026-03-05T16:56:47Z
- **Tasks:** 2
- **Files modified:** 2

## Accomplishments
- Removed Novotes.transf_program from both transf_rtl_program and transf_rtl_program_to_rtl in Compiler.v
- Fixed all match/correctness proofs in Compiler.v to skip Novotes unfolding/destruct
- Removed Novotes/Novotesproof imports from both Compiler.v and Complements.v
- Deleted transf_c_program_to_rtl'_no_votes and transf_c_program_to_rtl'_preservation' lemmas from Complements.v
- Fixed transf_c_to_rtl_match_prog proof in Complements.v
- Both Compiler.vo and Complements.vo compile successfully

## Task Commits

Each task was committed atomically:

1. **Task 1: Remove Novotes pass from Compiler.v pipeline and fix proofs** - `1966bc6a` (feat)
2. **Task 2: Clean up Complements.v -- remove Novotes references and delete unused lemmas** - `14607078` (feat)

## Files Created/Modified
- `driver/Compiler.v` - Pipeline definitions and match/correctness proofs without Novotes pass
- `driver/Complements.v` - Match proofs cleaned of Novotes; unused no_votes lemmas deleted

## Decisions Made
- Novotes pass removed entirely rather than made a no-op, since Phase 5's rtl_weak_agreement' makes it unnecessary
- Deleted two lemmas (transf_c_program_to_rtl'_no_votes and transf_c_program_to_rtl'_preservation') that depended on the Novotes pipeline step; Phase 7 (THERM-01) will reconstruct the preservation' lemma with correct argument order

## Deviations from Plan

None - plan executed exactly as written.

## Issues Encountered
None

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- Pipeline simplified, ready for Phase 7 theorem composition
- transf_c_program_to_rtl_preservation_faulty remains Admitted (pre-existing, Phase 7's scope)
- Phase 7 will reconstruct the preservation' lemma using the Phase 5 bridge's rtl_weak_agreement'

## Self-Check: PASSED

- All source files exist (Compiler.v, Complements.v)
- Both .vo files compiled successfully
- Both task commits verified (1966bc6a, 14607078)
- SUMMARY.md created

---
*Phase: 06-pipeline-simplification*
*Completed: 2026-03-05*
