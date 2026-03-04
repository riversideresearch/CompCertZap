# CompCertZAP Liveness-Bounded Fault Tolerance Proof

## What This Is

An update to the CompCertZAP fault tolerance proof that replaces the overly-coarse register invariant (quantifying over all registers) with a liveness-bounded invariant. This enables color inference to use sparse tables instead of dense quadratic-sized tables, dramatically improving memory usage on large functions while maintaining the same formal guarantees.

## Core Value

The faulty backward simulation proof (`RTLtolerant.v`) compiles with no `Admitted` lemmas using the new liveness-bounded register match invariant.

## Requirements

### Validated

- Liveness optimization implemented in color inference oracle (`RTLinfercolor.ml`) -- existing
- Color spec (`RTLcolor.v`) updated to parameterize well-coloredness by liveness -- existing
- Color checker (`RTLcolorcheck.v`) updated to compute and pass liveness info -- existing (structure only)

### Active

- [ ] New `ProofLiveness.v` analysis with conservative transfer function (always includes Iop/Iload args)
- [ ] `check_col_instr_sound` proof completed in `RTLcolorcheck.v` (currently Admitted)
- [ ] `RTLtolerant.v` faulty backward simulation proof rebuilt with proof-liveness-bounded invariant
- [ ] Top-level theorem chain (`driver/Complements.v`) composes with updated assumptions
- [ ] End-to-end validation: `make ccomp` succeeds, color checker runs on test programs

### Out of Scope

- Extending fault tolerance proof to assembly level -- separate future milestone
- Redesigning the color inference oracle algorithm -- already functional with union-find
- Performance benchmarking of sparse vs dense inference -- optional validation only
- Changes to DMR pass or DMR proof -- TMR path only

## Context

This is a brownfield project on the `rtl-liveness` branch of the CompCertZAP fork. The branch already has:
- `RTLcolor.v` updated to accept liveness parameter in `wc_instruction` and `wc_function` (uses `Liveness.analyze`)
- `RTLcolorcheck.v` updated to compute liveness and pass it to checker (but `check_col_instr_sound` is Admitted)
- `RTLtolerant.v` partially refactored: `match_rs`/`match_rs_upto` parameterized by `live : Regset.t`, match state definitions carry `LIVE` hypothesis, but proof breaks at line ~1367 in `exec_Iop` case
- `RTLinfercolor.ml` already uses sparse liveness-bounded inference

The key insight from the plan: CompCert's `Liveness.transfer` omits `Iop`/`Iload` operands when the destination register is dead. This is correct for dead code elimination but too weak for the simulation proof, which needs argument liveness to discharge `Val.lessdef` obligations. A new `ProofLiveness` analysis with a more conservative transfer function resolves this.

## Constraints

- **Coq compatibility**: Must compile with the project's Coq version (8.x with `-ignore-coq-version`)
- **No Admitted**: All touched files must have zero `Admitted` proofs at completion
- **Existing structure**: `RTLcolor.v` and `RTLcolorcheck.v` already reference `Liveness.analyze`; must be switched to `ProofLiveness.analyze`
- **Proof style**: Follow CompCert conventions (forward/backward simulation, `TransfLink`, Section/Context for vote type parameterization)

## Key Decisions

| Decision | Rationale | Outcome |
|----------|-----------|---------|
| Create separate ProofLiveness.v rather than modifying Liveness.v | Liveness.v is used by dead code elimination and register allocation; changing its transfer function would break those passes | -- Pending |
| Conservative transfer: always include Iop/Iload args | Over-approximates liveness to guarantee simulation proof obligations can be discharged; can be refined later if needed | -- Pending |

---
*Last updated: 2026-03-04 after initialization*
