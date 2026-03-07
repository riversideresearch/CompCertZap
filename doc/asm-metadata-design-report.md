# Asm Metadata Design Report

## Purpose

This note records two design threads that came up while reviewing the
RISC-V fault-tolerance extension plan:

1. replacing explicit `Pftag` instructions with compiler-produced metadata
2. comparing register-only tracking against location-aware tracking

It also records the conclusion that `Linear` is the latest IR in the
pipeline that still exposes abstract stack locations directly.

## 1. Replacing `Pftag` with metadata

### Problem

Using explicit `Pftag` pseudo-instructions in `Asm` is awkward because
the current `Asm` semantics is position-based:

- `PC` steps by one instruction
- labels resolve to instruction positions
- calls save return addresses based on instruction positions

If tags are inserted as actual instructions, they change code layout.
If the printer later erases them, the printed assembly no longer matches
the code layout used by the proved semantics.

### Tag map idea

Instead of inserting instructions, attach metadata to the final Asm
program. Conceptually:

```coq
Record tagged_program := {
  tp_prog : Asm.program;
  tp_tags : function_id -> Z -> option ftag_kind
}.
```

or equivalently a separate tag map carried alongside `Asm.program`.

Then:

- ordinary `Asm.semantics` uses only `tp_prog`
- `Asmfault.faulty_semantics` consults `tp_tags`
- the printer emits only ordinary assembly from `tp_prog`

This preserves code layout while still carrying the provenance needed to
classify faultable instructions.

### Soundness requirement

If the fault semantics depends on tags, the tags cannot be arbitrary.
They must be justified by one of the following:

1. compiler-produced metadata with a proof
2. unverified producer plus verified validator/checker

Unchecked tags would amount to assuming the fault classification is
correct without proving or validating it.

### Preferred option

The cleanest option is:

1. `Asmgen` (or an immediately surrounding pass) produces plain Asm plus
   tags/metadata
2. the proof of that pass establishes that the metadata correctly
   reflects the lowering decisions
3. the checker and faulty semantics consume that metadata

If exposing tags in the top-level theorem makes the proof simpler, that
is acceptable. A cleaner corollary can be derived later if desired.

## 2. Register-only tracking vs. location-aware tracking

### Register-only idea

The register-only design tracks only machine registers in the Asm color
system and treats loads as producing White values. The motivation is
simplicity:

- fixed-size register domain
- no need to reason about stack-slot aliasing
- easier checker and invariant shape

### Concern

This design is plausible only if spill/reload behavior is acceptable.
Once a protected value is spilled, the allocator/backend can reintroduce
it via an ordinary load. If the Asm system treats reloads as White,
there is no automatic recovery of Red/Green/Blue structure unless the
backend also introduces explicit recovery operations.

That means a register-only design may:

- reject realistic spilled TMR code, or
- accept it while reducing protection coverage more aggressively than
  intended

This is the main feasibility risk for a register-only Asm theorem.

### Location-aware idea

A more faithful design colors both:

- machine registers
- stack locations corresponding to spilled values / calling-convention
  slots

This matches the post-allocation view of CompCert more closely, since
register allocation maps values to locations, not just registers.

### Why it is easier before Asm

At the Asm level, abstract stack slots have already been lowered away.
To reason about them there, one would need metadata that remembers which
concrete SP-relative accesses correspond to which abstract locations.

Earlier in the backend, this information is explicit in the IR.

## 3. Latest IR that still has abstract locations

`Linear` is the latest convenient representation that still has abstract
locations directly.

In `Linear`:

- stack accesses still use `Lgetstack` / `Lsetstack`
- builtins can mention `loc`
- locations are still `R mreg | S slot pos ty`

After `Linear`, `Stacking` translates abstract stack-slot operations
into concrete frame-offset operations in `Mach`, and later passes lower
those to ordinary loads/stores.

Therefore:

- if we want a theorem over a language with explicit abstract locations,
  `Linear` is the natural target
- if we want an Asm theorem with location-aware reasoning, metadata
  should be propagated from `Linear` (or earlier) down to Asm

## 4. Propagating location metadata to Asm

It is possible to carry abstract-location information from `Linear`
down to Asm to inform an Asm checker.

The right model is compiler-produced metadata, not post hoc recovery
from plain Asm syntax.

Conceptually:

```coq
Asmgen :
  Linear.function ->
  res (Asm.function * asm_loc_meta)
```

where `asm_loc_meta` can describe facts such as:

- which Asm position came from which `Linear` instruction
- which abstract location(s) are being read or written
- whether a write is faultable/protected/neutral
- how replicated Red/Green/Blue values correspond across lowered code

This is feasible, but significantly more complicated than staying at
`Linear`.

## 5. Practical conclusion

### If the immediate goal is an Asm theorem

Use metadata instead of `Pftag` instructions. If stack-aware reasoning
is needed, propagate metadata from `Linear` (or another pre-`Stacking`
IR) rather than trying to reconstruct abstract locations from naked
Asm.

### If the immediate goal is to validate register allocation

Retarget the fault-tolerance theorem to `Linear` first.

This would:

- cover `Alloc`, which is the main pass that can destroy TMR separation
- avoid the Asm-specific problems around tags, positions, labels,
  temporaries, and multi-instruction expansion
- allow direct reasoning over abstract locations instead of reconstructing
  them from machine code
