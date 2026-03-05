# CompCertZAP Liveness-Bounded Fault Tolerance Proof

## What This Is

An update to the CompCertZAP fault tolerance proof that replaces the overly-coarse register invariant (quantifying over all registers) with a liveness-bounded invariant. The liveness-bounded approach enables color inference to use sparse tables instead of dense quadratic-sized tables, dramatically improving memory usage on large functions while maintaining the same formal guarantees. The full proof chain is machine-checked with zero Admitted lemmas.

## Core Value

The faulty backward simulation proof (`RTLtolerant.v`) compiles with no `Admitted` lemmas using the new liveness-bounded register match invariant.

## Requirements

### Validated

- ProofLiveness.v conservative liveness analysis with Kildall backward solver -- v1.0
- RTLcolor.v and RTLcolorcheck.v reference ProofLiveness.analyze -- v1.0
- check_col_instr_sound fully proved (14 instruction cases, no Admitted) -- v1.0
- Faulty backward simulation proved with liveness-bounded match relation -- v1.0
- Top-level theorem chain (Complements.v) composes with updated assumptions -- v1.0
- End-to-end validation: ccomp builds and compiles with -tmr flag -- v1.0

### Active

(None -- start next milestone to define new requirements)

### Out of Scope

- Extending fault tolerance proof to assembly level -- separate future milestone
- Redesigning the color inference oracle algorithm -- already functional with union-find
- Performance benchmarking of sparse vs dense inference -- optional validation only
- Changes to DMR pass or DMR proof -- TMR path only
- Modifying Liveness.v -- used by DCE and register allocation

## Context

Shipped v1.0 on `rtl-liveness` branch. Key files:
- `backend/ProofLiveness.v` (131 LOC) -- new conservative liveness analysis
- `backend/RTLcolor.v` (247 LOC) -- well-coloredness spec
- `backend/RTLcolorcheck.v` (539 LOC) -- verified Boolean color checker
- `backend/RTLtolerant.v` (3,267 LOC) -- faulty backward simulation proof
- `driver/Complements.v` (904 LOC) -- top-level theorem chain

Total: +1,509 / -842 lines changed across 6 Coq/OCaml files.

## Key Decisions

| Decision | Rationale | Outcome |
|----------|-----------|---------|
| Create separate ProofLiveness.v rather than modifying Liveness.v | Liveness.v is used by dead code elimination and register allocation; changing its transfer function would break those passes | Good |
| Conservative transfer: always include Iop/Iload args | Over-approximates liveness to guarantee simulation proof obligations can be discharged | Good |
| Reuse module names (RegsetLat, DS) from Liveness.v | No file imports both; avoids namespace churn | Good |
| Use Regset.for_all_2 bridge in color checker | More direct than PTree_Properties.for_all_correct since checker iterates over Regset | Good |
| Changed match_stackframes RS from live!!pc to transfer f pc (live!!pc) | Aligns with exec_return obligations in backward simulation | Good |
| Save-before-inv pattern in RTLtolerant.v | Save critical facts before destructive inv_wc/inv Hstep to avoid Coq variable consumption | Good |

## Constraints

- **Coq compatibility**: Must compile with the project's Coq version (8.x with `-ignore-coq-version`)
- **No Admitted**: All touched files must have zero `Admitted` proofs at completion
- **Existing structure**: Follow CompCert conventions (forward/backward simulation, `TransfLink`, Section/Context for vote type parameterization)

---
*Last updated: 2026-03-05 after v1.0 milestone*
