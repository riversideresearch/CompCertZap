# CompCert Proof Cleanup and Reorganization

## What This Is

A systematic cleanup of CompCert's fault-tolerance proof codebase — reducing duplication, removing dead code, centralizing shared lemmas, and resolving TODO markers across the DMR/TMR proof infrastructure. This is maintenance work on an existing formally verified compiler fork.

## Core Value

All Coq proofs continue to compile cleanly after every change — no regressions, no new Admitted proofs.

## Requirements

### Validated

- ✓ CompCert compiles C to x86-64 assembly — existing
- ✓ TMR/DMR replication passes produce correct RTL — existing
- ✓ Fault tolerance backward simulation proof composes four refinements — existing
- ✓ Color checker verifies well-coloredness of replicated programs — existing

### Active

- [ ] Delete untracked backup files and dead experimental stubs
- [ ] Centralize shared DMR/TMR proof lemmas into common modules
- [ ] De-duplicate repeated proof scripts (Novotesproof, RTLtmrproof, RTLtolerant, RTLcolorcheck)
- [ ] Strengthen replication-map specifications with relational specs
- [ ] Unify no_votes handling across cross-pass assumptions
- [ ] Remove large commented-out abandoned proof blocks from active files
- [ ] Resolve all TODO markers in in-scope files

### Out of Scope

- New features or compiler passes — this is cleanup only
- Changing theorem statements unless required for cleanup — keep signatures stable
- Optimizing build times — focus is on code quality
- Touching files outside the fault-tolerance extension unless necessary

## Context

- Brownfield: large existing Coq/OCaml codebase with established proof conventions
- DMR and TMR proof/spec files share significant duplicated machinery
- Multiple backup files and dead code accumulated during development
- TODO markers in 8+ active proof files indicate known cleanup points
- Build verification: `make backend/<file>.vo` for fast checks, `make proof -j$(nproc)` for integration

## Constraints

- **Build integrity**: Every commit must leave the proof buildable — no broken intermediate states
- **Theorem stability**: Prefer keeping theorem signatures stable; when changing, migrate all call sites in the same commit
- **Coq version**: Must remain compatible with current Coq/OCaml toolchain (OCaml 4.14.2)

## Key Decisions

| Decision | Rationale | Outcome |
|----------|-----------|---------|
| Follow dependency-aware execution order (0,1,3,2,4,5) | Phase 3 spec cleanup enables Phase 2 de-duplication | — Pending |
| Separate commits by type (move-only, extraction, statement changes) | Prevents accidental proof obligation changes | — Pending |
| Verify via rg + build before any file deletion | Prevents removing externally referenced code | — Pending |

---
*Last updated: 2026-03-03 after initialization*
