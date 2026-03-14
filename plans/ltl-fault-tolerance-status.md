# LTL Fault Tolerance Status

This file is the live execution tracker for the LTL fault-tolerance
plan in [ltl-fault-tolerance.md](./ltl-fault-tolerance.md).

It is intended to answer four questions at all times:

1. What is the current target?
2. What has landed already?
3. What is blocked?
4. What should happen next?

## Scope

Primary target:

- land `V1`: first end-to-end `LTL` theorem with certified protected
  register-destination faults

Secondary target:

- land `V2`: strengthen the theorem to include certified protected
  `Local`-slot writes

Out of scope for this tracker:

- `Linear` / `Asm` follow-on work except as dependencies or future work
- redesigning TMR across function boundaries

## Source documents

- [ltl-fault-tolerance.md](./ltl-fault-tolerance.md)
- [ltl-fault-tolerance-v1.md](./ltl-fault-tolerance-v1.md)
- [liveness-invariant-plan.md](./liveness-invariant-plan.md)
- [README.md](../README.md)

## Status legend

- `pending`: not started
- `in_progress`: active work item
- `blocked`: cannot proceed without resolving a dependency
- `done`: landed and verified

## Current snapshot

- Date opened: 2026-03-07
- Current focus: establish the execution tracker and begin Phase 0
- Overall status: `in_progress`
- Active milestone: `M0`
- Active theorem target: `transf_c_program_to_ltl_preservation_faulty_v1`

## Milestones

### M0. Truncated compiler to LTL

Status: `in_progress`

Goal:

- define `transf_rtl_program_to_ltl'`
- define `transf_rtl_program_to_ltl`
- define `transf_c_program_to_ltl`
- prove ordinary non-faulty `LTL` preservation lemmas

Files:

- [driver/Compiler.v](/home/alex/source/compcert/driver/Compiler.v)
- [driver/Complements.v](/home/alex/source/compcert/driver/Complements.v)

Exit criteria:

- `transf_c_program_to_ltl` exists
- ordinary non-faulty preservation theorem to `LTL` builds

Notes:

- cut immediately after `Allocation`, before `Tunneling`

### M1. LTL indexed points and witnesses

Status: `pending`

Goal:

- choose and implement static checker points
- define runtime/continuation witness relations
- prove basic bridge lemmas for `State`, `Block`, and continuations

Files:

- [backend/LTLindex.v](/home/alex/source/compcert/backend/LTLindex.v)
- [backend/LTL.v](/home/alex/source/compcert/backend/LTL.v)
- [backend/LTLtolerant.v](/home/alex/source/compcert/backend/LTLtolerant.v)

Exit criteria:

- point representation fixed
- witness discipline fixed
- bridge lemmas available for checker and simulation proofs

Risk:

- rework if the checker is written before witness-carrying points are
  settled

### M2. RTL@Three -> LTL@Three preservation through allocation

Status: `pending`

Goal:

- prove `LTL.semantics_determinate`
- derive a backward-style preservation lemma from `Allocproof`

Files:

- [backend/LTL.v](/home/alex/source/compcert/backend/LTL.v)
- [driver/Complements.v](/home/alex/source/compcert/driver/Complements.v)

Dependencies:

- `M0`

Exit criteria:

- backward simulation or equivalent preservation lemma from post-TMR
  `RTL@Three` to `LTL@Three`

Notes:

- explicitly reuse `Allocproof.transf_program_correct`

### M3. Allocation-produced ABI facts

Status: `pending`

Goal:

- extract thin `LTLabi.wf_program` assumptions from allocator proofs

Files:

- [backend/LTLabi.v](/home/alex/source/compcert/backend/LTLabi.v)
- [backend/Allocproof.v](/home/alex/source/compcert/backend/Allocproof.v)

Dependencies:

- `M0`
- `M2`

Exit criteria:

- `LTLabi.wf_program` defined
- theorem that `Allocation.transf_program` outputs satisfy it

Key facts to expose:

- entrypoint move discipline
- `compat_entry`
- `can_undef destroyed_at_function_entry`
- signature preservation
- stacksize preservation
- call/tailcall/result placement sanity

### M4. Declarative LTL coloring and faultability

Status: `pending`

Goal:

- define tracked location domain
- define proof liveness over LTL checker points
- define declarative `LTL` coloring
- define declarative `faultable_at`

Files:

- [backend/LTLProofLiveness.v](/home/alex/source/compcert/backend/LTLProofLiveness.v)
- [backend/LTLfaultspec.v](/home/alex/source/compcert/backend/LTLfaultspec.v)
- [backend/LTLcolor.v](/home/alex/source/compcert/backend/LTLcolor.v)
- [backend/LTLindex.v](/home/alex/source/compcert/backend/LTLindex.v)

Dependencies:

- `M1`
- `M3`

Exit criteria:

- `wc_program` and `wf_faultclass` specifications exist
- overlap-aware `Local`-slot invariants are explicit
- White-boundary rules for calls/returns are explicit

### M5. Verified Boolean checker and oracle

Status: `pending`

Goal:

- implement `LTLcolorcheck.check_program`
- return certified fault metadata
- prove checker soundness

Files:

- [backend/LTLcolorcheck.v](/home/alex/source/compcert/backend/LTLcolorcheck.v)
- [backend/LTLinfercolor.ml](/home/alex/source/compcert/backend/LTLinfercolor.ml)

Dependencies:

- `M4`

Exit criteria:

- `check_program p = Some fc -> wc_program p /\ wf_faultclass p fc`

V1 requirement:

- checker may certify only the register-destination subset initially

### M6. Faulty LTL semantics

Status: `pending`

Goal:

- define faulty `LTL` state wrapper
- define `maybe_zap`
- parameterize by certified fault classification

Files:

- [backend/LTLfault.v](/home/alex/source/compcert/backend/LTLfault.v)
- [backend/LTLfaultspec.v](/home/alex/source/compcert/backend/LTLfaultspec.v)

Dependencies:

- `M4`
- `M5`

Exit criteria:

- faulty semantics at vote type `Two`
- `V1` fault class represented and consumable by the theorem

### M7. Faulty backward simulation at LTL (`V1`)

Status: `pending`

Goal:

- prove the first tolerant theorem for the register-destination fault
  class

Files:

- [backend/LTLtolerant.v](/home/alex/source/compcert/backend/LTLtolerant.v)

Dependencies:

- `M1`
- `M3`
- `M5`
- `M6`

Exit criteria:

- `faulty_backward_simulation_v1` builds

Hotspots:

- entry shuffles
- spill/reload interaction
- call / tailcall / return
- external-call result placement
- witness-carrying intra-block stepping

### M8. End-to-end composed theorem (`V1`)

Status: `pending`

Goal:

- compose the full end-to-end `C -> faulty LTL` theorem

Files:

- [driver/Complements.v](/home/alex/source/compcert/driver/Complements.v)

Dependencies:

- `M0`
- `M2`
- `M3`
- `M5`
- `M7`

Exit criteria:

- `transf_c_program_to_ltl_preservation_faulty_v1` builds

### M9. Extend fault class to protected `Local`-slot writes (`V2`)

Status: `pending`

Goal:

- enlarge the certified fault class
- prove strengthened tolerant theorem
- prove final strengthened composed theorem

Files:

- [backend/LTLfaultspec.v](/home/alex/source/compcert/backend/LTLfaultspec.v)
- [backend/LTLcolorcheck.v](/home/alex/source/compcert/backend/LTLcolorcheck.v)
- [backend/LTLfault.v](/home/alex/source/compcert/backend/LTLfault.v)
- [backend/LTLtolerant.v](/home/alex/source/compcert/backend/LTLtolerant.v)
- [driver/Complements.v](/home/alex/source/compcert/driver/Complements.v)

Dependencies:

- `M8`

Exit criteria:

- final `transf_c_program_to_ltl_preservation_faulty` builds

## Immediate next actions

1. Implement `M0` in `driver/Compiler.v` and `driver/Complements.v`.
2. Add `LTL.semantics_determinate` when starting `M2`.
3. Freeze the checker-point design before any `LTLcolor*` file exists.

## Decision log

### 2026-03-07

- Created this status tracker.
- Chosen execution strategy: land `V1` first, then extend to `V2`.
- Chosen proof cut: immediately after `Allocation`.

## Work log

Use one entry per meaningful change or proof session.

### Template

Date:

- Summary:
- Files touched:
- Build/test status:
- Blockers:
- Next step:

### 2026-03-07

- Summary: created the execution tracker for the LTL fault-tolerance
  project.
- Files touched:
  - [plans/ltl-fault-tolerance-status.md](/home/alex/source/compcert/plans/ltl-fault-tolerance-status.md)
- Build/test status: not applicable
- Blockers: none
- Next step: start `M0` by adding the truncated `LTL` pipeline and its
  ordinary preservation lemmas.

### 2026-03-07

- Summary: implemented the first `M0` code changes for the `LTL` cut:
  added `transf_*_to_ltl`, `match_prog_ltl`, the ordinary `LTL`
  preservation wrappers, and an `LTL.semantics_determinate` lemma.
- Files touched:
  - [backend/LTL.v](/home/alex/source/compcert/backend/LTL.v)
  - [driver/Compiler.v](/home/alex/source/compcert/driver/Compiler.v)
  - [driver/Complements.v](/home/alex/source/compcert/driver/Complements.v)
- Build/test status: proof validation blocked locally. `make
  backend/LTL.vo`, `make driver/Compiler.vo`, and `make
  driver/Complements.vo` all fail before checking the edits because
  `coqc` cannot resolve `Require Import Coqlib`.
- Blockers:
  - local Coq load-path / build configuration mismatch
- Next step: resolve the Coq build environment, then re-run the narrow
  proof targets and fix any remaining proof-script issues.
