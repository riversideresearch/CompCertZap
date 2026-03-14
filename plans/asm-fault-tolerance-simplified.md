# Plan: Simplified Asm Fault Tolerance

## Goal

Prove an `Asm`-level analogue of the current RTL theorem, but with a
much simpler final fault model than the one proposed in
`plans/asm-fault-tolerance.md`.

The intended top-level theorem is still of the form:

```coq
Theorem transf_c_program_to_asm_preservation_faulty :
  forall p tp beh,
    transf_c_program_tagged p = OK tp ->
    AsmFaultCert.check_program tp = true ->
    program_behaves (Asmfault.faulty_semantics tp) beh ->
    exists beh', program_behaves (Csem.semantics p) beh'
              /\ behavior_improves beh' beh.
```

but the meaning of `Asmfault.faulty_semantics tp` should *not* be "fault
whatever the metadata says".  Instead, the fault semantics should have a
small trusted definition, and the metadata checker should only certify
that the compiled program satisfies the faultability predicate required
by that semantics.

## Core simplification

The final machine fault model should match the style of `RTLfault`:

- a fault can happen only at the current instruction
- at most one fault occurs during execution
- only the destination register of the current instruction can be
  faulted
- no memory locations are faulted
- no arbitrary metadata-defined state updates are allowed

This is intentionally narrower than the earlier Asm plan:

- no Asm-level faulting of frame stores
- no Asm-level faulting of arbitrary memory writes
- no machine-level fault semantics whose trusted meaning is defined by a
  metadata payload

## Trusted semantic story

The trusted story should be:

1. `LTL` is the source of truth for protection structure after register
   allocation.
2. A checked `LTL` witness identifies protected register-destination
   operations and White-boundary points.
3. Verified lowering transports that witness to a predicate over final
   Asm instruction points.
4. The Asm fault semantics uses only that abstract predicate together
   with the syntactic destination register of the current instruction.
5. Metadata, if used, is only a certificate / executable encoding of the
   abstract predicate in step 3.

This means the answer to "what is the fault model?" is:

- execute one ordinary Asm instruction
- if the current machine point is certified faultable, optionally zap
  the destination register of that instruction

not:

- execute whatever fault behavior the metadata describes

## Abstract Asm fault model

### Faultable points

The final semantics should be parameterized by a simple predicate over
concrete Asm instruction positions, for example:

```coq
Record asm_point := {
  ap_fun : block;
  ap_pos : Z
}.

Definition faultable_point := asm_point -> Prop.
```

This is the Asm analogue of the RTL-level choice of faultable program
points.

### Destination register

Separately, define a syntactic function:

```coq
dest_reg_of_instr : Asm.instruction -> option preg
```

capturing the unique destination register, when one exists, for the
machine instructions included in the fault scope.

Examples that may be in scope:

- integer register-result arithmetic instructions
- floating-point register-result arithmetic instructions
- register-result loads / reloads
- other register-writing instructions that correspond to protected
  compute or protected reload at the source witness level

Examples that should remain out of scope in the first theorem:

- stores
- frame-management instructions
- calls / returns / tailcalls
- jumps and labels
- vote / repair / White-boundary traffic
- instructions whose register writes are only scratch artifacts of
  lowering

### Faulty step

The faulty semantics should follow the same shape as `RTLfault`:

1. inspect the current `PC`
2. identify the current function and instruction position
3. execute one ordinary Asm step
4. if the pre-step instruction point is `faultable_point` and the
   instruction has `dest_reg_of_instr i = Some r`, optionally replace
   the post-state value of `r` by a compatible value
5. record that the single fault has now been spent

No metadata should appear in this trusted semantic definition.

## Role of LTL

## Why LTL is still needed

The simplified Asm fault model does **not** eliminate the need for an
`LTL`-level source of truth.

Plain Asm syntax does not determine:

- whether a machine instruction is protected compute or only scratch
- whether a reload comes from protected `Local` state or from White
  interface traffic
- whether a register write is part of vote / repair / boundary plumbing
- which machine points correspond to protected register-destination
  operations after register allocation

Those facts are naturally stated at `LTL`, where the compiler still
exposes:

- machine registers and abstract stack locations via `loc`
- explicit `call_regs` / `return_regs`
- White interface structure at calls, returns, and entry
- protected `Local`-slot structure needed to justify protected reloads

Therefore the trusted source of faultability should remain a checked
`LTL` witness, not naked Asm syntax and not metadata alone.

## What is needed from the LTL development

For the simplified Asm theorem, the `LTL` plan is still needed, but only
part of it is directly on the Asm-critical path.

Needed:

- an `LTL` checker/specification over block-local points and `loc`
- soundness yielding a witness of protected structure
- enough witness content to identify protected register-destination
  operations and White-boundary points
- enough `Local`-slot information to justify protected reloads
- a verified lowering path from that witness to final Asm instruction
  points

Not required as a prerequisite for the simplified Asm theorem:

- Asm-level memory-fault support
- lowering of faultable memory destinations
- the stronger `V2` story where `Local`-slot writes themselves are
  faultable

The full `LTL` faulty theorem is still a good milestone, but the
essential dependency for Asm is the witness/specification layer, not
necessarily the entire `LTL` tolerant theorem first.

## Witness lowering

## Principle

The right abstraction boundary is:

- `LTL` checker proves existence of a witness
- later passes lower that witness
- the final Asm semantics consumes only the abstract predicate
  `faultable_point`

The witness should not be lowered as a raw full color map.  It should be
lowered as the smaller set of facts needed to justify final Asm
faultability:

- which `LTL` points are protected register-destination operations
- which `LTL` points are White-boundary / vote / repair / neutral
- provenance from later IR points back to those protected/White classes
- enough abstract location meaning to distinguish protected reloads from
  boundary/frame traffic

## Pass-by-pass lowering

### Through Tunneling / Linearize / CleanupLabels

Transport:

- point provenance
- protected-vs-boundary point class
- register-destination protection facts

No commitment to concrete stack-frame layout is needed yet.

### Through Stacking

`Stacking` is still important, but only for classification, not because
the final semantics faults memory.

Its role is to explain:

- which reload-like machine operations still represent reads from
  protected `Local` state
- which frame accesses are White interface traffic
- which frame-management instructions are never in the fault scope

### Through Asmgen

`Asmgen` is the point where one abstract operation can expand into
several machine instructions.

The lowering proof must therefore identify:

- which emitted instruction point inherits the protected meaning
- which emitted instructions are scratch / neutral artifacts
- which emitted instruction, if any, has the register destination that
  the Asm semantics may fault

## Metadata

## Demoted role

Metadata may still be useful, but only in the following role:

- an executable certificate that a compiled Asm program realizes the
  abstract faultable-point predicate obtained from verified lowering

Metadata should **not** define the trusted semantics.

The desired layering is:

1. trusted semantics parameterized by abstract `faultable_point`
2. trusted proof that compiler lowering induces such a predicate from
   the checked `LTL` witness
3. verified checker that metadata correctly implements that predicate

If metadata is present in the final theorem statement, the logical shape
should be:

```coq
AsmFaultCert.check_program tp = true
```

implies:

- a well-formedness property
- existence of the intended `faultable_point`
- agreement between metadata and the abstract predicate

not:

- "the fault semantics is whatever the metadata says"

## Recommended proof organization

## Stage 1: LTL witness milestone

Deliverables:

1. `LTL` checker/specification
2. witness extraction theorem
3. witness content sufficient for protected register-destination points
4. optionally, the standalone `LTL` faulty theorem

This remains the first substantive milestone.

## Stage 2: Abstract Asm fault semantics

New file:

- `backend/Asmfault.v` or arch-specific equivalent

Actions:

1. define `asm_point`
2. define abstract `faultable_point`
3. define `dest_reg_of_instr`
4. define RTL-style `maybe_zap`
5. define faulty Asm semantics parameterized by `faultable_point`

This is the trusted machine-level fault model.

## Stage 3: Witness lowering to abstract Asm faultability

New files:

- new lowering proof files under `backend/`

Actions:

1. lower the checked `LTL` witness through later backend passes
2. define the induced abstract predicate over final Asm instruction
   points
3. prove that this predicate marks exactly the intended protected
   register-destination machine points

This stage gives the semantic answer to "which Asm points are faultable?"

## Stage 4: Optional metadata certificate

New files:

- `backend/AsmFaultCert.v`
- `backend/AsmFaultCertCheck.v`

Actions:

1. define a compact metadata format implementing the abstract
   faultability predicate
2. prove checker soundness
3. prove metadata-to-abstract-predicate agreement

The metadata should be deliberately narrow:

- point provenance / classification
- enough information to identify faultable machine points
- no attempt to make metadata itself the semantic specification

## Stage 5: Final Asm tolerant proof

New file:

- `backend/Asmtolerant.v`

Core theorem shape:

```coq
Theorem faulty_backward_simulation :
  abstract_faultability_from_compiler tp ->
  backward_simulation
    (@Asm.semantics Three VoteSemantics_Three (tp_prog tp))
    (Asmfault.faulty_semantics faultable_point (tp_prog tp)).
```

If a metadata certificate is used in the top-level theorem, it should be
connected to the above assumption by a separate soundness theorem.

## Main consequences

Compared with the earlier Asm plan, this simplified plan:

- keeps a clean, small trusted Asm fault semantics
- avoids making metadata part of the trusted semantic definition
- avoids Asm-level memory-fault sites
- still relies on `LTL` as the semantic source of truth for protected
  structure
- keeps witness lowering necessary, but narrower and more focused

So the conceptual picture is:

- `LTL` defines and checks the protection structure
- verified lowering tells us which final Asm instruction points inherit
  that structure
- the Asm semantics faults only the destination register of those points
