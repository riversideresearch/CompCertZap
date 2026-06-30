# Plan: Interface TMR for Return Values

## Goal

Extend interface TMR so selected internal functions return protected
values as Red/Green/Blue triples instead of forcing every return through
a single White value.

This plan assumes the arguments-only stage in
`plans/interface-tmr-arguments-plan.md` has already been completed or is
being developed as a prerequisite.

Concretely:

- protected internal callees receive protected arguments
- protected internal callees produce protected result triples
- callers receive result triples without a vote-and-replicate sequence
- external, indirect, and non-eligible boundaries remain conservative
  White boundaries

## Why This Is Harder Than Arguments

RTL calls can already pass a longer argument list, so argument triples
fit naturally into `Callstate`.

RTL returns do not have the same flexibility:

- `Returnstate` carries one value
- `Icall` writes one result register
- backend calling conventions expose one result type

Therefore, protected return triples need an explicit result-channel
protocol. The preferred design is hidden output parameters.

Unlike argument triples, hidden result channels introduce memory effects.
That is the main new proof risk.

## Core Design

### Hidden Result Channels

For an original function:

```text
f(A1, ..., An) -> R
```

the full protected ABI is:

```text
f_ret_tmr(A1_r, A1_g, A1_b, ..., An_r, An_g, An_b,
          out_r, out_g, out_b) -> void
```

where:

- `out_r` points to the Red result slot
- `out_g` points to the Green result slot
- `out_b` points to the Blue result slot

For a first version, use three explicit output pointers rather than one
aggregate pointer.

### Caller Protocol

For an eligible direct call with a non-void result:

1. reserve three private result slots
2. compute addresses for those slots into ordinary RTL registers
3. pass the addresses as hidden output arguments
4. call the transformed callee
5. load the three slots into the caller's result triple registers
6. continue without voting the result

The old single call destination register becomes a dummy register or is
otherwise ignored by the transformed continuation.

### Callee Protocol

For a transformed return:

1. compute the Red, Green, and Blue return values in the corresponding
   channel registers
2. store each channel value into the matching hidden output pointer
3. execute `Ireturn None`, or return an ignored dummy value

The first implementation should prefer `Ireturn None` for transformed
protected-return functions if the surrounding well-typedness and RTL
typing obligations are cleaner with a void transformed result.

### Void Results

Functions with no source-level result do not need hidden result slots.
They can use the protected-argument ABI only.

## Result Slot Allocation

The caller must own the result slots.

Recommended first design:

- allocate the slots in the caller's RTL stack frame
- increase `fn_stacksize` as needed
- use `Oaddrstack` operations to materialize the three hidden pointers
- use typed `Iload` instructions after the call to receive the result
  triple

This keeps result-channel lifetime local to the caller and avoids global
state.

Open design point:

- whether to reserve one slot triple per call site
- or reuse one slot triple per result type when liveness makes reuse
  simple

For the first proof, one private slot triple per transformed call site
is easier to specify.

## Boundary Policy

### Protected-to-Protected Calls

Use the full protected ABI:

- tripled ordinary arguments
- hidden result output pointers
- no vote at call entry
- no vote after return

### Protected-to-Old-ABI Calls

Keep the existing behavior:

- vote arguments before the call
- execute the old ABI call
- copy the single White result to shadows

### Old-ABI-to-Protected Calls

Use a wrapper:

1. receive old ABI White arguments
2. replicate arguments into triples
3. allocate result slots
4. call the protected implementation
5. vote or otherwise select the protected result triple
6. return one White value on the old ABI

`main` must remain on the old external ABI.

## Tailcalls

Tailcalls need an explicit first-version decision.

Recommended first restriction:

- do not use protected-return ABI for functions containing `Itailcall`
  until a tailcall protocol is specified

Rationale:

- if the caller allocates private stack slots, an `Itailcall` frees the
  current stack frame before entering the callee
- forwarding the current function's own hidden output pointers is
  possible, but it needs a separate proof case

Later extension:

- a transformed tailcall can forward the current function's hidden
  output pointers to the tail-called protected callee, then perform an
  ordinary `Itailcall`

## Implementation Impact

### `backend/RTLtmr.v`

Add a full protected-return ABI mode on top of the protected-argument
ABI.

For protected-return functions:

1. expand ordinary arguments as in the argument plan
2. append hidden output pointer parameters for non-void results
3. change the transformed result signature to void, if chosen
4. transform `Ireturn (Some r)` into result-channel stores followed by
   `Ireturn None`
5. transform eligible direct calls to allocate/pass/load result channels
6. keep non-eligible calls on the old path

The transformation must reserve:

- fresh pointer registers for hidden out-parameter addresses at call
  sites
- fresh stack slots for result channels
- any dummy result register required by RTL typing

### `backend/RTLtmrspec.v`

Add relational cases for:

- transformed signatures with hidden output parameters
- transformed call sites with result-slot setup and post-call loads
- transformed returns with three result stores
- result-slot freshness and non-aliasing
- old ABI wrappers, if wrappers are generated in this pass

The current `match_Ireturn` cases vote a single return register. Those
remain only for old-ABI returns.

### `backend/RTLtmrproof.v`

The proof must relate a source return value to a target sequence that
writes three hidden result slots.

Main obligations:

1. caller result slots are fresh and private
2. output pointers passed to the callee point to those slots
3. callee stores the correct Red/Green/Blue values
4. caller loads the stored values into the result triple
5. the old source result register matches the target Red result and its
   Green/Blue shadows
6. unrelated memory is preserved

This is substantially larger than the arguments-only proof because the
state relation needs a result-channel memory invariant.

## Color System Impact

Add protected-return rules for:

- hidden output pointer parameters
- callee-side result stores
- caller-side result loads
- preservation of non-result live colors across the call
- wrapper transitions between protected and White values

The existing rule that `Istore` requires White data cannot be used for
protected result-channel stores. Add a dedicated rule for stores to
hidden result channels, with explicit separation requirements.

The checker likely needs at least small program-level side conditions:

- which functions use hidden result channels
- which parameters are output pointers
- which call-site slots are private result slots
- which stores/loads are part of the result-channel protocol

A purely local checker is less likely to be enough for returns than it
is for arguments.

## Faulty Simulation Impact

The current faulty simulation uses `Memory.Mem.extends` as the memory
relation. Protected result stores can invalidate plain memory extension
if one colored channel has been faulted and stores an arbitrary
compatible value.

Therefore the return stage likely needs a strengthened memory relation.

Candidate relation:

```text
protected_mem_match faulted result_slots m_three m_faulty
```

Properties:

- ordinary memory still satisfies `Mem.extends`
- protected result slots are related by a color-aware triple invariant
- if no fault has occurred, all three slots agree with the source value
- if one fault has occurred, the affected color slot may differ
- slots are private, non-overlapping, and not read by ordinary program
  operations except through the result-channel protocol

The proof must then rework cases that currently rely directly on:

- `Mem.storev_extends`
- `Mem.loadv_extends`
- `Mem.free_parallel_extends`
- external-call memory preservation/extensionality lemmas

This memory relation is the main reason returns should be staged after
arguments.

## Wrappers

Wrappers are likely required for a usable full ABI story.

### Old ABI Wrapper

For externally visible functions and `main`-reachable old ABI calls:

```text
f_old(args) -> R
```

wrapper behavior:

1. replicate old ABI args into triples
2. allocate hidden result slots
3. call the protected implementation
4. vote the result triple
5. return one White result

### Protected Implementation

Use either:

- a fresh internal symbol for the protected implementation, or
- the original symbol only when it is known private and non-address-taken

Fresh internal symbols are more invasive but make external ABI
preservation easier to state.

## Restrictions for the First Milestone

Use these restrictions initially:

- require the arguments-only plan first
- direct internal calls only
- no indirect calls using the protected-return ABI
- no external calls using the protected-return ABI
- preserve `main`'s ABI
- non-void scalar results only
- no struct or aggregate returns
- no transformed tailcalls at first
- one private result-slot triple per transformed call site
- no separate compilation guarantee except through wrappers

## Suggested Phases

### Phase 0: Result-Channel Specification

Define:

- hidden output parameter layout
- result slot allocation policy
- result-slot typing and alignment
- result-channel memory invariant
- tailcall restriction

Deliverable: a precise protected-return ABI spec.

### Phase 1: Executable Transformation

Modify `RTLtmr.v` to:

1. add hidden output parameters
2. allocate caller result slots
3. materialize output pointers
4. transform protected direct calls
5. transform returns into result-channel stores

Deliverable: transformed RTL generation compiles for a restricted
program class.

### Phase 2: TMR Soundness

Update `RTLtmrspec.v` and `RTLtmrproof.v`.

Deliverable: semantic preservation for full protected interface TMR,
including result channels.

### Phase 3: Color Rules and Checker

Update `RTLcolor.v`, `RTLcolorcheck.v`, and `RTLinfercolor.ml`.

Deliverable: checker soundness for hidden result channels and wrappers.

### Phase 4: Faulty Simulation

Update `RTLtolerant.v` with the protected memory relation.

Deliverable: `faulty_backward_simulation` restored for full interface
TMR programs accepted by the checker.

### Phase 5: Top-Level Composition

Update `driver/Complements.v`.

Deliverable: the top-level RTL fault-tolerance theorem composes through
the full protected-return ABI.

## Exit Criteria

This stage is complete when:

1. eligible direct internal calls receive protected argument triples
2. eligible non-void internal calls return protected result triples
3. old ABI boundaries still vote and return one White value
4. result slots are proven private and separated
5. TMR soundness is reproved
6. checker soundness is reproved
7. faulty backward simulation is reproved under the strengthened memory
   invariant
8. the top-level RTL fault-tolerance theorem is restored

Until the protected memory relation is stable, this plan should not be
fed into downstream `Linear` or `Asm` fault-tolerance plans.
