# Plan: Extending Fault Tolerance to Asm via LTL-Sourced Metadata

## Goal

Prove a final `Asm`-level analogue of the current RTL theorem:

```coq
Theorem transf_c_program_to_asm_preservation_faulty :
  forall p tp beh,
    transf_c_program_tagged p = OK tp ->
    AsmmetaCheck.check_program tp = true ->
    program_behaves (Asmfault.faulty_semantics tp) beh ->
    exists beh', program_behaves (Csem.semantics p) beh'
              /\ behavior_improves beh' beh.
```

where `tp` is ordinary `Asm` plus compiler-produced protection
metadata.

## High-level strategy

Use the existing `LTL` fault-tolerance plan as Stage 1, then continue
to final `Asm` by carrying compiler-produced metadata down the rest of
the backend and validating it at the end.

The important design decision is:

- do not try to preserve raw `LTL` colorings unchanged through later
  passes
- do not try to reconstruct separation from plain `Asm` syntax alone
- instead, establish separation at `LTL`, lower a protection witness
  alongside the program, and validate the final `Asm + metadata`

This keeps `LTL` as the source of truth for the protected structure
created after register allocation while avoiding the need to force the
same invariant shape through `Stacking` and `Asmgen`.

## Relationship to `plans/ltl-fault-tolerance.md`

This plan is an extension of the `LTL` plan, not a replacement for it.

Interpretation:

1. the `LTL` theorem remains the first post-regalloc milestone
2. the `LTL` checker/specification becomes the authoritative source of
   protection structure after allocation
3. later backend passes compile that structure into metadata
4. the final `Asm` theorem is proved using a checked metadata layer

So the `LTL` plan should be read as Phases 0-7 of this broader effort.

However, the recommended implementation order is not "finish every
detail of the `LTL` plan, then begin thinking about `Asm`".  The cleaner
interpretation is:

1. design the exportable `LTL` witness interface up front
2. land the `LTL` theorem as a clean milestone using that interface
3. treat the later `Asm` work as a consumer of that already-stabilized
   post-allocation witness

That preserves a real standalone `LTL` milestone while avoiding
refactoring the checker contract later.

## Why this route

### 1. Why keep `LTL` as the source of truth

`LTL` is the first IR after allocation and still exposes exactly the
information needed to reason about separation:

- machine registers
- abstract stack locations
- explicit ABI structure at calls, returns, and entry

This is the right level to determine whether the allocator preserved the
intended TMR structure.

### 2. Why not push `LTL` well-coloredness directly by preservation

Weak agreement transports through behavioral refinement because it has a
semantic formulation. Separation does not currently have that shape.

The `LTL` color system is an intensional invariant over:

- block-local program points
- tracked locations
- White boundary discipline
- overlap-aware effects on abstract stack slots

That invariant does not survive later representation changes in any
literal sense:

- `Linearize` changes program-point structure
- `Stacking` lowers abstract stack locations into frame accesses
- `Asmgen` expands one abstract operation into one or more machine
  instructions and may use scratch registers

Therefore the right move is to lower a witness of the invariant, not to
preserve the raw invariant unchanged.

### 3. Why not rely on plain Asm only

Plain `Asm` lacks the provenance needed to recover:

- which machine instruction came from which protected abstract step
- which concrete frame access corresponds to which abstract `Local` slot
- which scratch traffic is neutral versus part of protected state
- which machine writes are in the intended fault scope

So the final theorem should target `Asm` plus metadata, not naked
`Asm`.

## Shared proof shape

The full composed story should be:

```text
C
>=2 RTL(no votes)
>=3 RTL(no votes)
>=3 RTL+TMR
>=3 LTL
>=2,faulty LTL
>=2,faulty tagged Asm
```

with the following interpretation:

1. standard compiler correctness to pre-TMR RTL
2. weak agreement to move from 2-voting to 3-voting
3. TMR soundness on RTL
4. backend preservation from post-TMR RTL to post-alloc `LTL`
5. faulty tolerance at `LTL`
6. metadata-guided preservation of the protected structure from `LTL`
   to final tagged `Asm`
7. faulty tolerance at tagged `Asm`

There are two viable ways to organize the final two steps:

### Option A: direct tagged-Asm tolerant theorem

1. prove `LTL` fault tolerance
2. prove that checked tagged `Asm` refines checked `LTL`
3. conclude final `Asm` fault tolerance by composition

### Option B: independent Asm tolerant theorem

1. prove `LTL` fault tolerance
2. lower the checked `LTL` witness into `Asm` metadata
3. prove `AsmmetaCheck` sound
4. prove a standalone tagged-Asm faulty backward simulation from
   non-faulty `Asm`@Three to faulty tagged `Asm`@Two

This plan recommends Option B.  It is more work, but gives a final
theorem whose assumptions are entirely `Asm`-local and checker-based.

## Core design decisions

### 1. Keep Stage 1 exactly at `LTL`

The existing `LTL` plan remains the first theorem milestone:

- establish a location-aware checker over `LTL`
- prove the first post-regalloc theorem
- make the protection discipline explicit

Do not skip this and try to invent the whole story directly at `Asm`.

### 2. Export a protection witness, not a raw coloring

The `LTL` checker should validate a structure that can be exported and
lowered.  The exported witness should not be "the full color map at
every `LTL` point" in some opaque internal format.

Instead, it should expose the information later passes need to compile
into metadata:

- point-indexed protected operation classes
- point-indexed location/lane ownership facts
- White boundary facts
- protected write/read classifications
- overlap and tracked-domain facts consumed by later lowering proofs

This witness may still be computed from an inferred `LTL` coloring, but
it should be designed as an explicit intermediate artifact.

### 3. Use compiler-produced metadata at the end

The final backend should produce:

```coq
Record tagged_program := {
  tp_prog : Asm.program;
  tp_meta : AsmMetadata.program_meta
}.
```

Ordinary non-faulty semantics uses only `tp_prog`.
Faulty semantics and the final checker consume `tp_meta`.

### 4. Track provenance, effect class, and abstract location meaning

The final metadata should carry enough information to support an Asm
checker, not merely a faultable/unfaultable bit.

At minimum it should support:

- source-point provenance
- protected-lane classification
- abstract effect classification
- stack-location provenance
- machine-position indexing
- fault-scope classification

### 5. Keep the final fault model metadata-driven

At `Asm`, the fault model should consult checked metadata to determine:

- which machine instructions are in fault scope
- which destination register they may fault
- how that fault is interpreted relative to the protected structure

Unchecked metadata must not influence the theorem.

## Candidate metadata model

## Tagged program

```coq
Record tagged_program := {
  tp_prog : Asm.program;
  tp_meta : AsmMetadata.program_meta
}.
```

## Per-function metadata

Conceptually:

```coq
Record fun_meta := {
  fm_points : PTree.t point_meta;
  fm_entry  : entry_meta;
  fm_stack  : stack_layout_meta
}.
```

where `point_meta` is indexed by final Asm instruction position.

## Per-position metadata

The exact record should be kept minimal, but a good starting shape is:

```coq
Record point_meta := {
  pm_origin : option origin_point;
  pm_class  : asm_point_class;
  pm_fault  : fault_class;
  pm_write  : option abstract_write;
  pm_reads  : list abstract_read
}.
```

Suggested payload meanings:

- `pm_origin`
  - which later-stage point this machine instruction came from
- `pm_class`
  - protected compute
  - protected reload
  - vote
  - smove / repair
  - White boundary
  - neutral lowering artifact
- `pm_fault`
  - whether the machine instruction is faultable in the first theorem
- `pm_write`
  - the protected abstract location/lane written, if any
- `pm_reads`
  - abstract protected locations/lanes consumed, if relevant

The exact origin language for `origin_point` can be chosen later:

- `LTL` point
- `Linear` point
- `Mach` point

This plan starts from `LTL` as the semantic source of truth, but the
lowering witness can be re-expressed at later backend stages if that
makes proofs simpler.

## Stage breakdown

## Stage 1: Land the LTL milestone with witness export built in

This is the current `plans/ltl-fault-tolerance.md`, interpreted with
the witness layer as part of the milestone rather than as a later
refactor.

Deliverables:

1. `transf_c_program_to_ltl`
2. `LTLabi.wf_program`
3. `LTLcolor.wc_program`
4. `LTLcolorcheck.check_program`
5. `LTLfault.faulty_semantics`
6. `LTLtolerant.faulty_backward_simulation`
7. `transf_c_program_to_ltl_preservation_faulty`
8. `LTLwitness.wf_witness`
9. `LTLcolorcheck.check_program_sound` exposing witness existence

The key point is that witness export is not a post-milestone cleanup
task.  It is part of what makes the `LTL` milestone reusable.

## Stage 2: Stabilize the witness API for downstream lowering

### Objective

Freeze the post-allocation witness contract that later backend passes
will lower into metadata.

### Files

- `backend/LTLcolor.v`
- `backend/LTLcolorcheck.v`
- `backend/LTLwitness.v` or similar

### Actions

1. validate that the milestone witness type is compact and lowering-
   oriented rather than proof-only
2. ensure that checker success yields both:
   - `wc_program`
   - existence of a witness satisfying the witness spec
3. separate witness contents from proof-only derived facts where useful
4. ensure the witness names:
   - protected program points
   - White boundary points
   - protected lanes
   - tracked abstract locations
   - any required stack-slot provenance

### Exit criteria

- `LTLcolorcheck.check_program` still implies `LTLcolor.wc_program`
- there is an explicit witness theorem consumable by later passes
- no downstream metadata design requires changing the checker-output
  theorem shape

## Stage 3: Choose the metadata lowering spine

### Objective

Decide where the witness is reified and transformed between `LTL` and
`Asm`.

### Recommended choice

Use a staged internal lowering path:

1. `LTL` witness
2. `Linear` or `Mach` witness for stack/provenance lowering
3. final `Asm` per-position metadata

The witness source of truth remains `LTL`, but the proof artifacts may
change representation at later IRs.

### Why this is recommended

- `Tunneling` / `Linearize` / `CleanupLabels` mostly affect control-flow
  shape and point identity
- `Stacking` is the natural place to lower abstract stack slots into
  concrete frame-access meaning
- `Asmgen` is the natural place to lower abstract operations into
  machine-position metadata

### Files

- new metadata files under `backend/`
- likely small extensions to `Linearizeproof`, `Stackingproof`,
  `Asmgenproof`, or companion metadata proof files

### Exit criteria

- a fixed per-pass metadata contract is chosen before implementation

## Stage 4: Metadata-aware truncated compiler cut points

### Objective

Add compiler entry points for the metadata-carrying backend path.

### Files

- `driver/Compiler.v`
- `driver/Complements.v`

### Actions

1. define metadata-carrying versions of later-stage compilation paths,
   for example:
   - `transf_c_program_to_tagged_asm`
   - optionally intermediate `to_linear_meta`, `to_mach_meta`
2. expose enough top-level structure for theorem statements and testing
3. keep the plain `Asm` path intact where possible

### Exit criteria

- the driver/proof layer can talk about tagged `Asm` as a first-class
  target

## Stage 5: Metadata transport through Tunneling / Linearize / CleanupLabels

### Objective

Transport point and origin information from post-alloc `LTL` through the
 control-flow reshaping passes that follow allocation and precede
 `Stacking`.

### Files

- new metadata companion files for these passes
- possibly `backend/Tunneling.v`, `backend/Linearize.v`,
  `backend/CleanupLabels.v` proofs or wrappers

### Actions

1. define per-pass metadata transformation functions
2. prove that transformed metadata remains consistent with:
   - successor structure
   - block-local point meaning
   - protected-point classes
   - White boundary classes
3. account for:
   - node renaming
   - removed branches / bypassed blocks
   - linearized point numbering

### Design note

At this stage the metadata can still refer to abstract locations.
Nothing here should commit to concrete frame offsets yet.

### Exit criteria

- a checked witness can be transported to the latest pre-`Stacking` IR

## Stage 6: Lower stack-location meaning through Stacking

### Objective

Translate witness facts about abstract `Local` stack slots into a form
usable after `Stacking`.

### Files

- new `backend/Stackmeta.v` or similar
- `backend/Stackingproof.v` companion proofs

### Actions

1. define how protected abstract locations map to stack-frame layout
2. record the stack-layout provenance needed by later Asm metadata
3. prove that protected-slot separation becomes a concrete frame-access
   separation property
4. classify frame-related operations as:
   - protected local reload/store effects
   - White boundary traffic
   - neutral frame-management traffic

### Key obligations

- preserve the distinction between protected `Local` slots and White
  interface slots
- explain how overlapping abstract slots map to concrete accesses
- identify frame-management instructions that should never be treated as
  protected computation

### Exit criteria

- the witness no longer depends on pre-`Stacking` abstract-slot syntax
- later proofs can interpret concrete frame accesses via checked
  provenance

## Stage 7: Emit final per-position metadata in Asmgen

### Objective

Produce final per-PC metadata aligned with actual Asm instruction
positions.

### Files

- `x86/Asmgen.v` or `riscV/Asmgen.v`
- companion metadata proof files
- `backend/AsmMetadata.v`

### Actions

1. extend `Asmgen` or an immediately surrounding layer to produce
   ordinary `Asm` plus metadata
2. assign metadata to each emitted machine instruction position
3. make explicit which emitted instructions are:
   - protected compute
   - protected reload
   - vote
   - repair / smove / boundary traffic
   - neutral
4. identify which positions are faultable in the first theorem
5. prove that the produced metadata faithfully reflects the lowering
   decisions

### Design note

This is the point where one abstract step may expand into multiple
machine instructions.  The metadata proof must say which subset of
those instructions carries the protected meaning and which are merely
lowering artifacts.

### Exit criteria

- final tagged `Asm` is produced by the compiler
- metadata faithfully tracks machine positions and abstract protection
  meaning

## Stage 8: Define tagged-Asm checker and metadata well-formedness

### Objective

Define the static contract that checked tagged `Asm` programs must
satisfy.

### Files

- `backend/Asmmeta.v`
- `backend/AsmmetaCheck.v`

### Actions

1. define a declarative well-formedness predicate for tagged `Asm`
2. define a verified Boolean checker for the metadata
3. check consistency between:
   - actual Asm instruction stream
   - point classes
   - fault classification
   - stack/layout provenance
   - vote/smove/repair structure
4. ensure the checker validates enough structure for the final tolerant
   proof, rather than merely confirming metadata shape

### Suggested checked facts

- tags align with real machine positions and function boundaries
- positions marked faultable really have the expected destination shape
- metadata never classifies White boundary traffic as protected compute
- metadata never merges distinct protected lanes at the same point
- concrete frame accesses marked as protected correspond to valid
  lowered protected slots
- vote and recovery sequences obey the intended lane/interface discipline

### Exit criteria

- `AsmmetaCheck.check_program tp = true -> Asmmeta.wf_program tp`

## Stage 9: Define faulty tagged-Asm semantics

### Objective

Define final machine-level faulty semantics that uses checked metadata.

### Files

- `backend/Asmfault.v` or arch-specific fault files

### Actions

1. define a tagged-program semantics wrapper
2. define metadata-guided `maybe_zap`
3. restrict zaps using checked metadata rather than syntax-only pattern
   matching
4. keep the first theorem conservative about fault scope

### Suggested first fault scope

- machine instructions classified as protected compute
- machine instructions classified as protected reload

Suggested initial exclusions:

- call/return plumbing
- frame management
- White boundary traffic
- pure repair / move lowering artifacts
- positions without validated destination metadata

### Exit criteria

- final faulty semantics is defined solely in terms of `Asm` plus
  checked metadata

## Stage 10: Tagged-Asm tolerant proof

### Objective

Prove a final faulty backward simulation for checked tagged `Asm`.

### Files

- `backend/Asmtolerant.v`

### Core theorem

```coq
Theorem faulty_backward_simulation :
  Asmmeta.wf_program tp ->
  backward_simulation
    (@Asm.semantics Three VoteSemantics_Three (tp_prog tp))
    (Asmfault.faulty_semantics tp).
```

### Proof structure

1. define machine-state match relation using checked metadata
2. relate machine registers and validated protected frame locations
3. carry a global fault bit as before
4. simulate each faultable instruction class
5. use metadata well-formedness to exclude impossible bad cases

### Main expected proof obligations

- protected compute instructions preserve lane separation
- protected reload instructions recover from a single fault exactly as
  intended
- White boundary instructions are outside the fault model or handled by
  explicit checker facts
- frame accesses use checked provenance to recover the protected-slot
  meaning needed by the invariant
- machine-position stepping respects metadata alignment

### Exit criteria

- checked tagged `Asm` refines ordinary `Asm` under the faulty semantics

## Stage 11: Final top-level theorem

### Objective

Compose the full source-to-tagged-Asm theorem in `driver/Complements.v`.

### Files

- `driver/Complements.v`

### Target theorem

```coq
Theorem transf_c_program_tagged_preservation_faulty :
  forall p tp beh,
    transf_c_program_tagged p = OK tp ->
    AsmmetaCheck.check_program tp = true ->
    program_behaves (Asmfault.faulty_semantics tp) beh ->
    exists beh', program_behaves (Csem.semantics p) beh'
              /\ behavior_improves beh' beh.
```

### Proof composition

1. use the standard compiler-correctness chain up to pre-TMR RTL
2. use weak agreement to move from 2-voting to 3-voting
3. use TMR soundness on RTL
4. use `Allocation`-to-`LTL` preservation at vote type `Three`
5. use the `LTL` fault-tolerance theorem as the first backend theorem
6. use metadata-lowering preservation from `LTL` witness to final tagged
   `Asm`
7. use the tagged-Asm tolerant theorem
8. compose `behavior_improves` transitively

### Design note

Depending on proof ergonomics, Step 5 may be used only as an
intermediate confidence milestone while the final proof composes Steps
6-7 directly from ordinary `Asm`@Three.  The plan keeps the `LTL`
theorem explicit because it is a valuable standalone deliverable and a
sanity check for the metadata route.

## Open design questions

### 1. What should the metadata origin language be

Possible choices:

- direct `LTL` points
- later `Linear` points
- `Mach` points

Recommendation:

- keep `LTL` as the semantic source of truth
- allow the internal witness to be re-expressed at `Linear` or `Mach`
  if that simplifies metadata transport proofs

### 2. How much should the final Asm checker reconstruct

Possible extremes:

- metadata-heavy: the checker mostly validates consistency
- reconstruction-heavy: the checker derives substantial structure from
  Asm syntax

Recommendation:

- use metadata for facts that are not recoverable from syntax
- validate as much syntax-level consistency as practical
- do not ask the checker to reverse-engineer abstract stack-slot meaning
  from plain machine code

### 3. Whether to target x86 first or RISC-V first

The plan is architecture-agnostic in shape, but the exact metadata and
fault classification will be arch-specific at `Asmgen`.

Recommendation:

- follow the backend with the cleaner existing fault-model story and
  strongest current motivation
- keep metadata interfaces generic enough to share most proof structure

### 4. Whether to keep a register-only first Asm theorem

This plan recommends against a register-only `Asm` theorem as the main
route.  It can be useful as a simplification experiment, but once
spilling is realistic the location/provenance story becomes necessary.

## Recommended implementation order

1. update the `LTL` plan so the witness layer is part of the milestone
2. land the `LTL` milestone theorem and checker stack
3. freeze the witness API and only then choose the metadata lowering
   spine and tagged-program surface API
4. implement metadata transport through post-alloc control-flow passes
5. implement stack-location lowering in `Stacking`
6. emit final per-position metadata in `Asmgen`
7. define and prove `AsmmetaCheck` sound
8. define metadata-guided faulty `Asm` semantics
9. prove tagged-Asm faulty backward simulation
10. compose the final source-to-tagged-Asm theorem

## Deliverables

1. the existing `LTL` theorem and checker stack
2. a reusable exported protection witness for checked `LTL`
3. compiler-produced metadata carried to final `Asm`
4. a verified checker for tagged `Asm`
5. metadata-guided faulty `Asm` semantics
6. a final source-to-tagged-Asm fault-tolerance theorem

## Practical payoff

- register allocation is handled where it is most naturally visible:
  `LTL`
- final machine-code fault tolerance is established without trying to
  recover abstract protection structure from naked `Asm`
- the proof architecture remains validator-driven and fits CompCert's
  existing style of external oracle plus verified checking
