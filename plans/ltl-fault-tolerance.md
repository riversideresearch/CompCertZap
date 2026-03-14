# Plan: Standalone LTL Fault Tolerance

## Goal

Prove an `LTL`-level analogue of the current RTL theorem as a
standalone backend result, without constraining the plan to future
Asm-level requirements.

The intended final theorem is:

```coq
Theorem transf_c_program_to_ltl_preservation_faulty :
  forall p tp fc beh,
    transf_c_program_to_ltl p = OK tp ->
    LTLcolorcheck.check_program tp = Some fc ->
    program_behaves (LTLfault.faulty_semantics tp fc) beh ->
    exists beh', program_behaves (Csem.semantics p) beh'
              /\ behavior_improves beh' beh.
```

This should target the first backend IR after register allocation,
namely `LTL`.

## Why target LTL

`LTL` is the cheapest post-regalloc target that still exposes the
location-level structure needed for post-regalloc fault tolerance:

- machine registers and abstract stack locations via `loc`
- explicit `Callstate` / `Returnstate`
- explicit stack frames
- explicit `call_regs` / `return_regs`

At the same time, it avoids the extra proof burden of later backend
IRs:

- no linearized global code-position layer
- no label-resolution bridge
- no `Tunneling` / `Linearize` / `CleanupLabels` obligations in the
  first theorem

So `LTL` is the natural place to answer the standalone question:

- does fault tolerance survive register allocation?

## Scope

This plan targets the current TMR design with White function
boundaries.

Protected values may live in:

- machine registers
- `Local` stack slots

`Incoming` and `Outgoing` locations are interface-only and remain
White.

The proof must account explicitly for:

- `call_regs`
- `return_regs`
- caller-save destruction
- external-call result placement
- function-entry destruction

Extending TMR across function boundaries is out of scope.

## Fault model

The standalone `LTL` fault model should follow the RTL story as closely
as is natural after allocation:

- a fault occurs only at the current instruction
- at most one fault occurs during execution
- only the destination written by the current instruction is faulted
- faults may affect protected register destinations and protected
  `Local`-slot destinations
- ordinary memory effects remain out of scope

This leads naturally to the staged split:

- `V1`: protected register-destination writes only
- `V2`: protected `Local`-slot writes added as well

Unlike the Asm-facing fork, this standalone plan treats both `V1` and
`V2` as part of the main intended result.

## Shared high-level proof shape

Keep the existing composition:

```text
C >=2 RTL(no votes) >=3 RTL(no votes) >=3 RTL+TMR >=3 LTL >=2,faulty LTL
```

Interpretation:

1. standard compiler correctness to pre-TMR RTL
2. weak agreement at RTL
3. TMR correctness at RTL
4. new preservation theorem from post-TMR RTL@Three to `LTL`@Three
5. new faulty backward simulation from `LTL`@Three to faulty `LTL`@Two

## Main design decisions

### 1. Cut immediately after Allocation

The first target should be `LTL` immediately after `Allocation`, before:

- `Tunneling`
- `Linearize`
- `CleanupLabels`
- `Debugvar`
- `Stacking`
- `Asmgen`

### 2. Track `loc`

The checker/specification should track:

- `R mreg`
- `S slot ofs ty`

This is the whole point of moving beyond RTL: the checker must reason
about spills, reloads, and protected local state directly.

### 3. Use a declarative `faultable_at`

Define a point-indexed declarative predicate:

```coq
faultable_at f pt instr
```

whose meaning is:

- the current instruction writes a destination
- the destination is part of protected redundant state at `pt`
- faulting that write respects the White/interface discipline

The checker should certify this predicate; it should not define it.

### 4. Keep `V1` / `V2`

The standalone plan should keep the staged split.

`V1` should cover:

- protected arithmetic/dataflow `Lop`
- protected move/repair register writes
- protected `Lgetstack Local ...`
- protected non-vote, non-external builtins with register destinations

`V2` should add:

- protected `Lsetstack Local ...`
- any additional certified overlap-sensitive protected local-slot
  writes justified by the checker/specification

This is a natural post-regalloc generalization of the current RTL fault
model: some faultable RTL pseudoregisters have become machine
registers, while others have become protected `Local` slots.

### 5. Use block-local program points

Represent static points as block-local instruction positions, e.g.
`(pc, idx)`.

The proof should carry point witnesses explicitly in states and stack
frames rather than trying to infer them uniquely from suffix blocks.

### 6. Make overlap explicit

The key new issue beyond RTL is overlap between stack locations.

Therefore:

- protected tracked `Local` slots must be pairwise `Loc.diff`
- transfer functions must be overlap-aware
- `V2` faultability for local-slot writes must be justified by
  overlap-aware update reasoning

### 7. Make function-entry obligations explicit

Because `call_regs` and function-entry undef happen in stages, the plan
should state explicitly:

- parameter locations are White at entry
- any tracked location live at entry must be a parameter location
- non-parameter tracked locations must be defined before protected use

## Checker/specification consequences

The `LTL` checker must enforce:

- White boundaries at calls, returns, tailcalls, and function entry
- separation of protected local slots
- overlap-aware update rules for `Local` slots
- consistency of colors/facts across control-flow successors
- explicit treatment of move-heavy allocation artifacts

It should still mention `Incoming` and `Outgoing`, but only to constrain
them to White behavior.

The call/return rules should be phrased over whole-location-set effects,
including:

- `call_regs`
- `return_regs`
- caller-save / callee-save register behavior
- `Local`, `Incoming`, and `Outgoing` slots separately
- external-call argument/result placement

## Phases

### Phase 0: truncated compiler to LTL

Add:

- `transf_rtl_program_to_ltl'`
- `transf_rtl_program_to_ltl`
- `transf_c_program_to_ltl`

plus the ordinary non-faulty preservation theorem to `LTL`.

### Phase 0.5: point and continuation design

Define:

- static checker points
- runtime-to-point bridge lemmas
- indexed continuation witnesses

This should happen before the checker and tolerant proof.

### Phase 1: RTL@Three to LTL@Three preservation

Reuse `Allocproof.transf_program_correct` to prove the
backward-simulation-style preservation theorem from post-TMR RTL@Three
to `LTL`@Three.

### Phase 2: thin ABI / structure extraction

Create `LTLabi.v` containing the allocation-produced structural facts
the tolerant proof should rely on independently of coloring.

### Phase 3: declarative color system

Create:

- `LTLcolor.v`
- `LTLfaultspec.v`
- optionally `LTLwitness.v`

Define:

- block-local points
- tracked-domain and liveness machinery
- color system over `loc`
- declarative `faultable_at`

The witness layer is still useful, but in this standalone plan it is a
secondary artifact rather than a contract driven by Asm.

### Phase 4: verified checker

Create `LTLcolorcheck.v` with:

- inference oracle
- verified Boolean checker
- theorem exposing:
  - `wc_program`
  - certified fault classification
  - optionally witness existence

The checker should support staged certification:

- `V1` first
- `V2` later without changing the theorem interface

### Phase 5: faulty LTL semantics

Create `LTLfault.v`:

- faulty state wrapper with a global fault bit
- `maybe_zap` in the `LTL` style
- parameterization by a certified static fault classification
- semantics at vote type `Two`

### Phase 6: faulty backward simulation

Create `LTLtolerant.v` proving:

- `faulty_backward_simulation_v1`
- later `faulty_backward_simulation_v2`

using:

- `LTLabi.wf_program`
- `LTLcolor.wc_program`
- `LTLfaultspec.wf_faultclass`

The proof must explicitly budget for:

- `Lgetstack` spill/reload interaction in `V1`
- `Lsetstack` overlap-sensitive spill/reload interaction in `V2`
- entry shuffles
- parmove cycle breaking
- stack-to-stack repair through temporaries
- two-address repair `Omove`
- splitlong helper moves
- call / tailcall / return / external-call result placement

### Phase 7: final theorem

Compose:

1. faulty `LTL`@Two refined by non-faulty `LTL`@Three
2. checker soundness
3. `LTLabi` facts extracted from `Allocation`
4. RTL@Three to `LTL`@Three preservation
5. RTL weak-agreement / TMR / standard compiler-correctness chain

to obtain:

- first `V1` theorem
- then strengthened `V2` theorem

## Exit criteria

The standalone `LTL` plan is complete when the development has:

1. `transf_c_program_to_ltl`
2. `LTLabi.wf_program`
3. `LTLcolor.wc_program`
4. `LTLfaultspec.wf_faultclass`
5. `LTLcolorcheck.check_program_sound`
6. `LTLfault.faulty_semantics`
7. `LTLtolerant.faulty_backward_simulation_v1`
8. `transf_c_program_to_ltl_preservation_faulty_v1`
9. `LTLtolerant.faulty_backward_simulation_v2`
10. `transf_c_program_to_ltl_preservation_faulty`

## Recommended implementation order

1. `transf_c_program_to_ltl` cut point
2. point / continuation witness design
3. RTL@Three -> `LTL`@Three preservation through `Allocation`
4. thin `LTLabi.wf_program`
5. declarative color system plus declarative `faultable_at`
6. verified checker
7. faulty `LTL` semantics
8. `V1` tolerant theorem
9. `V1` final end-to-end theorem
10. `V2` checker strengthening for protected local-slot writes
11. `V2` tolerant theorem and final theorem

## Practical payoff

- the TMR transformation survives register allocation
- `V1` gives the first post-regalloc theorem with relatively low proof
  overhead
- `V2` extends the result to the larger overlap-sensitive class of
  protected post-regalloc writes

This is the clean standalone `LTL` story, independent of any later Asm
consumer.
