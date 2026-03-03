# Project State

## Project Reference

See: .planning/PROJECT.md (updated 2026-03-03)

**Core value:** All Coq proofs continue to compile cleanly after every change — no regressions, no new Admitted proofs.
**Current focus:** Phase 1 - Baseline and File Cleanup

## Current Position

Phase: 1 of 5 (Baseline and File Cleanup)
Plan: 0 of TBD in current phase
Status: Ready to plan
Last activity: 2026-03-03 — Roadmap created

Progress: [░░░░░░░░░░] 0%

## Performance Metrics

**Velocity:**
- Total plans completed: 0
- Average duration: -
- Total execution time: 0 hours

**By Phase:**

| Phase | Plans | Total | Avg/Plan |
|-------|-------|-------|----------|
| - | - | - | - |

**Recent Trend:**
- Last 5 plans: none yet
- Trend: -

*Updated after each plan completion*

## Accumulated Context

### Decisions

Decisions are logged in PROJECT.md Key Decisions table.
Recent decisions affecting current work:

- [Roadmap]: Follow dependency-aware execution order (original plan: 0,1,3,2,4,5) — spec strengthening (Phase 3) must precede proof de-duplication (Phase 4) so de-duplicated proofs can reference the cleaner relational specs
- [Roadmap]: Separate commits by type (move-only, extraction, statement changes) to prevent accidental proof obligation changes
- [Roadmap]: Verify via `rg` + build before any file deletion to prevent removing externally referenced code
- [Roadmap]: no_votes policy alignment (XPASS-01, XPASS-02) deferred to v2 — requires cross-pass architecture decision not needed for current cleanup

### Pending Todos

None yet.

### Blockers/Concerns

- [Phase 4 pre-condition]: The `no_votes` Option A vs. Option B policy decision must be made before Phase 4 implementation begins. Research recommendation: Option B (checker soundness discharges internally via `Novotes.check_program`). Record this decision explicitly at the start of Phase 4 planning.
- [Phase 2 pitfall]: New files (`RTLreplicateSpecCommon.v`, `RTLreplicateProofCommon.v`) must be added to the Makefile `BACKEND` variable in the same commit that creates them, or they will silently fail when imported.
- [Phase 3 pitfall]: Lemmas moved out of `Section VOTE` gain explicit `{VT: vote_type} {vsem: VoteSemantics VT}` parameters — all call sites must be updated in the same commit.

## Session Continuity

Last session: 2026-03-03
Stopped at: Roadmap created, STATE.md initialized. No plans written yet.
Resume file: None
