# Plan: LTL Fault Tolerance for Asm

## Goal

Establish the `LTL`-level protection structure needed by the simplified
Asm fault-tolerance story.

The key deliverable is not just an `LTL` theorem, but a checked witness
interface that can serve as the trusted source of truth for which final
Asm instruction points are faultable.

The intended top-level `LTL` theorem remains:

```coq
Theorem transf_c_program_to_ltl_preservation_faulty :
  forall p tp fc beh,
    transf_c_program_to_ltl p = OK tp ->
    LTLcolorcheck.check_program tp = Some fc ->
    program_behaves (LTLfault.faulty_semantics tp fc) beh ->
    exists beh', program_behaves (Csem.semantics p) beh'
              /\ behavior_improves beh' beh.
```

But for the Asm line of work, the truly critical milestone is:

- checker/specification soundness at `LTL`
- existence of a lowering-oriented witness
- witness content sufficient to identify protected register-destination
  operations and White-boundary points

The full standalone `LTL` tolerant theorem is still valuable, but it is
not the only artifact that matters for the Asm path.

## Relationship to the simplified Asm plan

This plan is the `LTL` half of
`plans/asm-fault-tolerance-simplified.md`.

Interpretation:

1. `LTL` remains the first post-regalloc target
2. `LTL` is the trusted source of protection structure
3. later backend passes lower an `LTL` witness to final Asm
   `faultable_point`s
4. the Asm semantics itself remains small and RTL-style

Therefore this plan is intentionally biased toward the subset of `LTL`
results needed by the simplified Asm fault model.

## Scope

This plan targets the current TMR design with White function
boundaries.

Protected values may live only in:

- machine registers
- `Local` stack slots

`Incoming` and `Outgoing` locations remain White-only interface
locations.

The proof must account explicitly for:

- `call_regs`
- `return_regs`
- caller-save destruction
- external-call result placement
- function-entry destruction

## Fault model

The `LTL` fault model remains staged:

- `V1`: protected writes whose destination is a machine register
- `V2`: protected writes whose destination is a `Local` slot

For the Asm line of work:

- `V1` is the main line
- `V2` is a later strengthening

This is the main change in emphasis relative to the standalone `LTL`
story. The simplified Asm theorem only needs the `V1` subset, because
the final Asm fault semantics faults only destination registers of
current machine instructions.

Still, `V2` remains part of this plan because:

- it is natural at `LTL`
- it matches the broader post-regalloc fault model
- it reuses the same point model, checker interface, and tolerant-proof
  structure

## Shared high-level proof shape

Keep the existing composition:

```text
C >=2 RTL(no votes) >=3 RTL(no votes) >=3 RTL+TMR >=3 LTL >=2,faulty LTL
```

Interpretation:

1. reuse the standard compiler-correctness chain to pre-TMR RTL
2. reuse weak agreement at RTL
3. reuse TMR correctness at RTL
4. prove backend preservation from post-TMR RTL@Three to `LTL`@Three
5. prove a faulty backward simulation from `LTL`@Three to faulty
   `LTL`@Two

## Main design decisions

### 1. Cut immediately after Allocation

The first target remains `LTL` immediately after `Allocation`, before:

- `Tunneling`
- `Linearize`
- `CleanupLabels`
- `Debugvar`
- `Stacking`
- `Asmgen`

This is still the right point for checking post-regalloc protection
structure.

### 2. Track `loc`, not only registers

The checker/specification must track:

- `R mreg`
- `S slot ofs ty`

Even though the Asm theorem only needs register-destination fault sites,
the `LTL` witness still needs `Local`-slot structure in order to:

- justify protected reloads
- enforce White boundaries
- prove separation of protected local state

### 3. Use block-local points

Program points should be block-local instruction positions, e.g.
`(pc, idx)`.

The proof and checker should share this point representation, and the
tolerant invariant should carry point witnesses explicitly rather than
trying to reconstruct them from raw `Block ... bb ...` states.

### 4. Keep `LTLabi` separate from coloring

Allocator-produced structural / ABI facts should live in a separate thin
predicate such as `LTLabi.wf_program`, extracted from `Allocproof`.

Do not overload `LTLcolor.wc_program` with allocator facts.

### 5. Keep `faultable_at` independent of the checker algorithm

Define a declarative predicate:

```coq
faultable_at f pt instr
```

The checker should certify this predicate; it should not define it.

For the Asm-facing path, the critical `V1` cases are:

- protected arithmetic/dataflow `Lop`
- protected move/repair register writes
- protected `Lgetstack Local ...`
- protected non-vote, non-external builtins with register destinations

`V2` later enlarges this set to protected `Local`-slot writes.

## Witness export

## Principle

The witness exported by checker soundness should be deliberately
narrower than a full color map.

It should expose exactly the facts needed later by the Asm path:

- protected program-point classes
- White-boundary points
- which `LTL` points are protected register-destination operations
- enough lane / ownership facts to distinguish protected computation
- enough protected `Local`-slot provenance to justify protected reloads

For the Asm path, the witness does not need to expose future faultable
memory destinations, because the simplified Asm fault model does not
fault memory.

## LTL theorem versus witness milestone

There are two distinct milestones in this plan.

### Milestone A: reusable witness layer

Deliverables:

1. `transf_c_program_to_ltl`
2. `LTLabi.wf_program`
3. `LTLcolor.wc_program`
4. `LTLfaultspec.wf_faultclass`
5. `LTLwitness.wf_witness`
6. `LTLcolorcheck.check_program_sound`

This is the minimum needed by the simplified Asm line of work.

### Milestone B: standalone `LTL` tolerant theorem

Deliverables:

1. `LTLfault.faulty_semantics`
2. `LTLtolerant.faulty_backward_simulation`
3. `transf_c_program_to_ltl_preservation_faulty_v1`
4. optionally later, the strengthened `V2` theorem

This remains a desirable milestone, but it is downstream of the witness
layer.

## Phase breakdown

### Phase 0: truncated compiler to LTL

Add:

- `transf_rtl_program_to_ltl'`
- `transf_rtl_program_to_ltl`
- `transf_c_program_to_ltl`

and the ordinary non-faulty preservation theorem to `LTL`.

### Phase 0.5: point and continuation witnesses

Define:

- static checker points
- runtime-to-point bridge lemmas
- indexed continuation witnesses for stack frames

This should happen before the checker and tolerant proof.

### Phase 1: RTL@Three to LTL@Three preservation

Reuse `Allocproof.transf_program_correct` and prove the
backward-simulation-style preservation result from post-TMR RTL@Three to
`LTL`@Three.

### Phase 2: thin ABI / structure extraction

Create `LTLabi.v` containing:

- entrypoint move discipline
- signature / stacksize preservation
- function-entry undef discipline
- call / tailcall / result-placement sanity

all extracted from existing allocation-proof facts.

### Phase 3: declarative color system and witness interface

Create:

- `LTLcolor.v`
- `LTLfaultspec.v`
- `LTLwitness.v`

Define:

- block-local points
- tracked-domain and liveness machinery
- color system over `loc`
- independent declarative `faultable_at`
- lowering-oriented witness interface

### Phase 4: verified checker

Create `LTLcolorcheck.v` with:

- inference oracle
- verified Boolean checker
- theorem exposing:
  - `wc_program`
  - certified fault classification
  - existence of a witness

The checker should support staged certification:

- `V1` first
- `V2` later without changing the interface

### Phase 5: faulty LTL semantics

Create `LTLfault.v` parameterized by the certified `faultclass`.

The Asm-facing line only strictly needs `V1`, but the semantics
interface should be compatible with later `V2`.

### Phase 6: faulty backward simulation

Create `LTLtolerant.v` proving:

- `faulty_backward_simulation_v1`
- later `faulty_backward_simulation_v2`

using:

- `LTLabi.wf_program`
- `LTLcolor.wc_program`
- `LTLfaultspec.wf_faultclass`

### Phase 7: final theorem

Compose the `LTL` tolerant theorem with:

- checker soundness
- `LTLabi` extracted from `Allocation`
- RTL@Three to LTL@Three preservation
- existing RTL weak-agreement / TMR / compiler-correctness chain

## Exit criteria

The Asm-facing `LTL` plan is complete when the development has:

1. `transf_c_program_to_ltl`
2. `LTLabi.wf_program`
3. `LTLcolor.wc_program`
4. `LTLfaultspec.wf_faultclass`
5. `LTLwitness.wf_witness`
6. `LTLcolorcheck.check_program_sound`
7. `LTLfault.faulty_semantics`
8. `LTLtolerant.faulty_backward_simulation_v1`
9. `transf_c_program_to_ltl_preservation_faulty_v1`

The strengthened `V2` theorem remains a later extension.

## Practical meaning

This plan keeps the full `LTL` proof story available, but it narrows
the exported contract to what the simplified Asm theorem actually needs:

- a trusted post-regalloc protection witness
- clear identification of protected register-destination points
- clear identification of White-boundary / vote / repair points
- enough protected-local structure to justify protected reloads

That is the right `LTL` source of truth for the simplified Asm fault
model.
