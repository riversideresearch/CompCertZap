# Plan: Extending Fault Tolerance to LTL

## Goal

Prove an `LTL`-level analogue of the current RTL theorem:

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

## Why target LTL first

`LTL` is the cheapest post-regalloc target that still exposes the
location-level structure relevant to fault tolerance:

- machine registers and abstract stack locations via `loc`
- explicit `Callstate` / `Returnstate`
- explicit stack frames
- explicit ABI transformers `call_regs` and `return_regs`

At the same time, `LTL` avoids the extra proof overhead of `Linear`:

- no global linearized code-index layer
- no `find_label` / label-resolution bridge
- no whole-program linearized instruction indexing layer
- no `Tunneling` / `Linearize` / `CleanupLabels` proof obligations in
  the first theorem

This makes `LTL` the best first target for answering the question
"does fault tolerance survive register allocation?"

## Scope

This plan targets the current TMR design, where function boundaries
enforce a White interface discipline.

Concretely:

- protected values may live only in machine registers and `Local` stack
  slots
- `Incoming` and `Outgoing` locations are interface-only and must remain
  White
- call arguments, return values, and call-target channels must remain
  White at function boundaries
- faults should be allowed on as many writes as possible, but only when
  the destination is certified to lie within protected redundant state
  at that program point
- the proof must account explicitly for `call_regs`, `return_regs`,
  caller-save destruction, external-call result placement, and
  function-entry destruction rather than treating the boundary as
  "everything becomes White"

The fault model should be staged explicitly:

- **V1** should certify only protected writes whose destination is a
  machine register
- **V2** should extend the same framework to protected writes whose
  destination is a `Local` stack slot

The purpose of the split is proof management, not a change in semantic
intent.  Both versions should use the same checker-point representation,
the same coloring interface, and the same `faultable_at`-parameterized
faulty semantics.  `V2` should strictly enlarge the certified fault
class proved in `V1`, not replace it with a different model.

Extending TMR across function boundaries is out of scope for this plan.
So are faults on White/interface channels such as vote results, call
results before re-replication, `Incoming`/`Outgoing` traffic, and other
ABI boundary moves.

## Shared high-level proof shape

Keep the same refinement composition pattern as the current RTL proof:

```text
C >=2 RTL(no votes) >=3 RTL(no votes) >=3 RTL+TMR >=3 LTL >=2,faulty LTL
 (1) standard       (2) weak agree    (3) TMR sim  (4) alloc     (5) faulty sim
```

Interpretation:

1. reuse the existing standard compiler-correctness chain from C to
   pre-TMR RTL
2. reuse weak agreement at RTL exactly as in the current proof
3. reuse the existing TMR correctness theorem at RTL
4. add a new backend preservation lemma from post-TMR RTL@Three to
   final `LTL`@Three
5. add a new faulty backward simulation from non-faulty `LTL`@Three to
   faulty `LTL`@Two

This preserves the current proof architecture while moving the target
language from RTL to `LTL`.

## Common design decisions

### 1. Cut immediately after Allocation

The first target should be `LTL` immediately after `Allocation`, before:

- `Tunneling`
- `Linearize`
- `CleanupLabels`
- `Debugvar`
- `Stacking`
- `Asmgen`

This captures register allocation while minimizing new proof machinery.
If successful, extension from `LTL` through `Linear` can be treated as a
second step.

### 2. Track locations, not just registers

At `LTL`, values live in locations:

- `R mreg`
- `S slot ofs ty`

Therefore the color system should track `loc`, not only registers.

This lets the checker reason directly about spills and reloads, which is
the main point of moving beyond RTL.

### 3. Use a certified protected-write fault model with staged rollout

The development should define one general certified fault model, but the
first theorem should target a smaller fault class than the final one.

Therefore zappability should not be defined by instruction syntax alone.
Instead, the development should define an explicit declarative predicate
for faultable writes at static checker points, for example:

- `faultable_at f pt instr`

The intended meaning is:

- the current instruction performs a write
- the written destination is part of protected redundant state at `pt`
- faulting that write does not cross a White/interface boundary

The Boolean checker should certify this predicate together with
well-coloredness, and the faulty semantics should be parameterized by
the resulting certified fault classification.

Under the fixed current TMR design, the intended `V1` target is to make
the following classes faultable whenever they are certified protected at
the current point and write to a machine register:

- arithmetic/dataflow `Lop`
- move/repair `Lop`, including `Omove`, `Omakelong`, `Olowlong`,
  `Ohighlong`
- `Lgetstack Local ...`
- non-vote, non-external builtins whose destination is a protected
  machine register

The intended `V2` extension is to add overlap-sensitive protected
`Local`-slot writes, in particular:

- `Lsetstack Local ...`
- any additional protected `Local`-slot write classes justified by the
  checker/specification

The intended exclusions are design limitations, not proof shortcuts:

- vote results
- `smove` steps that rebuild redundancy from a White value
- call results before re-replication
- `Incoming` / `Outgoing` traffic
- call / tailcall / return interface moves
- `Lgetstack Incoming ...` and `Lgetstack Outgoing ...`
- `Lstore`, external calls, and other ordinary memory side effects
- protected `Local`-slot writes in `V1`

This yields two milestones under the same White-boundary TMR design:

- `V1` lands the first theorem with protected register-destination
  writes only
- `V2` strengthens that theorem by adding protected `Local`-slot writes
  once the overlap-aware proof machinery is in place

### 4. Protected locations are registers plus Local slots

For this plan, protected values live only in:

- `R r`
- `S Local ofs ty`

`Incoming` and `Outgoing` remain White-only interface locations.

### 5. Program points are block-local instruction positions

Unlike RTL, `LTL` executes basic blocks, not single instructions.
Therefore the static program-point representation should be:

- a block node `pc`
- plus an instruction position within the current block

Recommended representation:

- `(pc, k)` where `pc` identifies the current block and `k` is either an
  instruction index or a suffix position inside that block

For the checker and inference, use a static finite representation such
as `(pc, instruction-index)`.

At runtime, `LTL` states do not always store this point explicitly:

- `State ... pc ...` stores the block node but not an instruction index
- `Block ... bb ...` stores the remaining block suffix `bb`, not the
  originating `pc`

Therefore the development should define both:

- a static checker point type, e.g. `(pc, idx)`
- a runtime relation connecting states to checker points

Recommended shape of the runtime relation:

- `State ... pc ...` corresponds to `(pc, 0)`
- `Block ... bb ...` corresponds to `(pc, idx)` when
  `fn_code ! pc = Some full_block` and `bb = skipn idx full_block`

However, this relation should not be assumed functional from raw runtime
states alone.  `Block` states and stored continuations carry only block
suffixes, so the same suffix can in principle arise from multiple static
points.

Therefore the proof design should carry explicit point witnesses:

- the current-state simulation invariant should include the static
  checker point it is talking about
- the stack-frame match relation should carry indexed continuation
  witnesses, not just raw `bb` suffixes
- checker soundness may use a runtime-to-point relation, but the
  tolerant simulation should not rely on reconstructing a unique point
  from the runtime state alone

This relation is what the simulation invariant and checker-soundness
lemmas should use to recover the current static point from a runtime
state.

The static checker point representation should be shared by:

- the declarative coloring specification
- the Boolean checker
- the inference oracle
- the statement of the faulty simulation invariant

The point is to stay close to the existing CFG structure of `LTL`
without introducing a `Linear`-style indexing layer.

### 6. Use a fixed finite tracked domain plus proof liveness

As at `Linear`, the location domain is not fixed-size because stack
slots vary by function.  The right design is:

- a fixed finite per-function tracked domain `Dom(f)`
- plus a proof-oriented liveness analysis that prunes obligations within
  `Dom(f)` at each program point

`Dom(f)` should include:

- all machine registers
- all syntactically mentioned stack locations
- all ABI boundary locations needed for entry/call/return obligations
- builtin/debug locations that appear explicitly

Liveness and domain construction should remain separate:

- `Dom(f)` determines which locations are visible to the proof
- liveness determines which of those tracked locations matter at a given
  program point

### 7. Make overlap explicit and transfer-aware

The key stack-location issue is overlap.  Two distinct stack locations
may partially overlap, and `Locmap.set` invalidates overlapping
locations.

Therefore:

- the color system should carry an explicit invariant that distinct
  protected non-White `Local` slots are pairwise `Loc.diff`
- the checker should enforce this invariant over the finite tracked
  domain
- transfer functions and simulation lemmas must be overlap-aware, not
  only equality-aware

In particular, a write to one tracked stack slot must account for all
tracked overlapping stack slots.  It is not sound to update only the
exact destination and ignore overlapping tracked locations.

This matters both for coloring and for fault classification: a stack
write can be faultable only if the certified protected destination is
stable under overlap-aware update.

### 8. Make function-entry obligations explicit

The hardest boundary issue is function entry.  `call_regs` copies
registers from caller to callee and maps caller `Outgoing` slots to
callee `Incoming` slots; only then does `exec_function_internal` apply
`undef_regs destroyed_at_function_entry`.

So the callee does not begin in an arbitrary all-White state.

The plan should therefore require an explicit entrypoint discipline:

- parameter locations at function entry are White
- any tracked location live at function entry must be a parameter
  location
- non-parameter tracked locations must be defined before any protected
  use

## White-boundary consequences

### Intended protected domain

Protected values may live in:

- `R r`
- `S Local ofs ty`

`Incoming` and `Outgoing` are interface-only and remain White.

### Consequences for the checker

The checker must enforce:

- loads/stores involving `Local` slots preserve separation
- calls consume White arguments
- call results are White
- returns expose only White interface values
- tailcalls satisfy the same White interface discipline
- distinct protected `Local` slots at a program point are pairwise
  non-overlapping

The checker still needs rules mentioning `Incoming` and `Outgoing`, but
only to constrain them to White behavior.

The first certified fault class does not need to mark every checked
write as faultable.  In particular, the checker/specification should be
ready from the start for overlap-sensitive `Local`-slot writes, but the
initial checker result should certify only the `V1` register-destination
subset.  `V2` can then enlarge the certified set without changing the
semantics interface.

The call/return rules should be phrased over whole-location-set effects,
not just explicit argument/result locations.  In particular, the
specification should state the intended White/protected behavior for:

- `call_regs` at function entry
- `return_regs` at return and tailcall
- caller-save vs. callee-save machine registers
- `Local`, `Incoming`, and `Outgoing` slots separately
- external-call argument/result placement via `loc_arguments` and
  `loc_result`

### Consequences for the faulty simulation

The match relation only needs to track protected consistency over:

- machine registers
- protected `Local` slots

But the proof must still handle the ABI-mediated transformations
performed by:

- `call_regs` at function entry
- `return_regs` at returns and tailcalls
- external-call argument/result placement
- caller-save destruction
- function-entry destruction

These should already be reflected in the checker/specification as
first-class interface-discipline rules.

## Theorem phases

### Phase 0: Add a truncated compiler to LTL

**Files**

- `driver/Compiler.v`
- `driver/Complements.v`

**Actions**

1. Define `transf_rtl_program_to_ltl'` for the path:
   - optional DMR
   - optional TMR
   - `Renumber`
   - `Allocation`
2. Define `transf_rtl_program_to_ltl` for the full RTL optimization
   path followed by `transf_rtl_program_to_ltl'`
3. Define `transf_c_program_to_ltl`
4. Add helper lemmas analogous to the existing RTL truncation lemmas

**Desired result**

A theorem analogous to `transf_c_program_to_rtl_preservation`, but
targeting ordinary non-faulty `LTL`.

### Phase 0.5: Indexed-point and continuation design

**Files**

- `backend/LTLindex.v` or `backend/LTLcolor.v`
- `backend/LTLtolerant.v`

**Actions**

1. Choose the static checker-point representation:
   - `(pc, instruction-index)`
   - or an equivalent finite encoding
2. Define the witness structure used by proofs:
   - current-state point witnesses
   - indexed continuation witnesses for stack frames
3. Prove the basic bridge lemmas relating:
   - `State ... pc ...` to entry index `0`
   - `Block ... bb ...` to a witnessed suffix position
   - stored `Stackframe ... bb` continuations to witnessed return points
4. Commit to the invariant discipline that simulation carries these
   witnesses explicitly, rather than reconstructing a unique point from
   raw runtime states

**Design note**

This phase should happen before the checker and tolerant proof.  The
biggest avoidable rework risk is baking an implicit point model into the
checker, then discovering that `Block`/`Stackframe` suffixes are not
enough to recover unique static points.

### Phase 1: LTL metatheory and backend preservation from RTL to LTL@Three

**Files**

- `driver/Complements.v`
- `backend/LTL.v` or a small new metatheory file, if needed

**Actions**

1. Prove the semantic side conditions actually needed to convert the
   existing RTL-to-LTL forward simulation into a backward-style
   preservation lemma:
   - reuse source receptiveness from `RTL`
   - prove `LTL.semantics_determinate`
2. Define the composed pass relation from post-TMR RTL to final `LTL`
   through:
   - `Alloc`
3. Reuse `Allocproof.transf_program_correct` instantiated at `Three`
4. Prove a lemma of the shape:

```coq
backward_simulation
  (@RTL.semantics Three VoteSemantics_Three p)
  (@LTL.semantics Three VoteSemantics_Three tp).
```

**Design note**

This phase should explicitly reuse the existing allocation-validator
facts rather than rebuilding an RTL-to-LTL relation from scratch.

### Phase 2: Allocation-produced ABI/structure well-formedness

**New file**

- `backend/LTLabi.v`

**Actions**

1. Define a thin structural / ABI-discipline predicate for `LTL`
   programs produced by allocation, capturing exactly the facts that the
   tolerant proof should rely on independently of coloring
2. Include the allocator-facing facts that matter to the fault-tolerance
   proof, such as:
   - entrypoint move discipline
   - entry compatibility and function-entry undef discipline
   - signature and stacksize consistency
   - call / tailcall / result placement sanity
   - any structural facts about generated `LTL` blocks consumed later by
     the tolerant proof
3. Prove that programs returned by `Allocation.transf_program` satisfy
   this predicate

**Design note**

Do not overload `wc_program` with allocator facts.  Keep coloring and
allocation-produced structural well-formedness as separate predicates so
the tolerant theorem states its real assumptions explicitly.

Also, do not build `LTLabi` as a fresh general-purpose `LTL`
well-formedness theory.  It should be a thin extraction layer over the
facts already proved by `Allocproof`, especially:

- entry-block shape / move expansion facts
- `compat_entry`
- `can_undef destroyed_at_function_entry`
- signature / stacksize preservation
- parameter / tailcall / result-placement lemmas already available from
  the allocation proof path

### Phase 3: Declarative location-aware color system for LTL

**New file**

- `backend/LTLcolor.v`

**Likely supporting files**

- `backend/LTLfaultspec.v`
- `backend/LTLProofLiveness.v`

**Actions**

1. Define static checker points as block-local instruction positions
2. Define a proof-oriented liveness analysis over those program points
   and tracked `loc`s
3. Define a coloring over `loc`
4. Define an independent declarative faultability specification over
   point-indexed writes, e.g. `faultable_at`
5. Define well-coloredness for `LTL` instructions
6. Include rules for:
   - `Lop`
   - `Lload`
   - `Lstore`
   - `Lgetstack`
   - `Lsetstack`
   - calls / tailcalls / returns
   - builtins including votes, smoves, and `EF_debug`
   - `Lbranch`, `Lcond`, and `Ljumptable`

The specification must state explicitly:

- only `Local` stack slots may carry protected colors
- `Incoming` and `Outgoing` are White-only
- protected tracked `Local` slots are pairwise `Loc.diff`
- writes and kills are overlap-aware over the tracked domain
- `faultable_at` is defined independently of the checker algorithm
- `faultable_at` includes every protected write class supported by the
  fixed TMR design and excludes White/interface writes by design

`LTLindex.v` should provide the bridge lemmas relating runtime states
and continuations to static checker points so that checker soundness and
the witness-carrying simulation invariant can talk about the coloring at
the current instruction position.

### Phase 4: Verified Boolean checker

**New file**

- `backend/LTLcolorcheck.v`

**Likely supporting files**

- `backend/LTLinfercolor.ml`

**Actions**

1. Follow the RTL checker architecture:
   - inference oracle
   - verified Boolean checker
2. Use the same block-local program-point representation as the
   declarative specification
3. Use the same tracked domain `Dom(f)` and proof-liveness information
4. Return certified fault-site metadata in addition to validating the
   coloring
5. Expose a theorem of the shape:

```coq
Lemma check_program_sound :
  check_program p = Some fc ->
  LTLcolor.wc_program p /\ LTLfaultspec.wf_faultclass p fc.
```

**Design note**

Do not introduce a standalone `LTLtyping` layer unless the proof
actually needs one.  Prefer reusing the well-formedness and entrypoint
facts already available from the allocation validator path.

The checker API should support staged certification:

- the initial implementation should return a `V1` fault classification
- the later extension should enlarge the certified classification to
  `V2` without changing the theorem interface

### Phase 5: Faulty LTL semantics

**New file**

- `backend/LTLfault.v`

**Actions**

1. Define a faulty state wrapper with a global fault bit
2. Define `maybe_zap` in the `LTL` style
3. Parameterize `maybe_zap` / `faulty_semantics` by a certified static
   fault classification
4. Define `faulty_semantics` at vote type `Two`

**Suggested staged classification**

- any write certified by `LTLfaultspec.faultable_at` is faultable
- `V1` should include protected arithmetic/dataflow `Lop`
- `V1` should also include protected move/repair register writes
  generated by allocation
- `V1` should include protected `Lgetstack Local ...`
- `V1` may include non-vote, non-external protected builtins with
  machine-register destinations
- `V2` should add protected `Lsetstack Local ...` and other certified
  overlap-sensitive protected `Local`-slot writes
- both versions should exclude White/interface writes and ordinary
  memory effects

**Important scope note**

Even in `V1`, move-heavy regalloc traffic remains central to the proof.
Register allocation emits move-heavy `LTL` code for:

- entry shuffles
- parmove cycle breaking through temporaries
- stack-to-stack repair via temporaries
- two-address repair `Omove`s
- splitlong helper moves

The checker and tolerant invariant must therefore specify these cases
precisely even before `V2` certifies the overlap-sensitive stack-write
subset as faultable.

### Phase 6: Faulty backward simulation at LTL

**New file**

- `backend/LTLtolerant.v`

**Core theorem schema**

```coq
Theorem faulty_backward_simulation :
  forall fc,
  LTLabi.wf_program prog ->
  LTLcolor.wc_program prog ->
  LTLfaultspec.wf_faultclass prog fc ->
  backward_simulation
    (@LTL.semantics Three VoteSemantics_Three prog)
    (LTLfault.faulty_semantics prog fc).
```

The plan should target two milestones under this same theorem shape:

- `faulty_backward_simulation_v1` for the initial register-destination
  fault class
- `faulty_backward_simulation_v2` for the strengthened class including
  protected `Local`-slot writes

**Proof structure**

1. define a location-set match relation
2. define a stack-frame match relation
3. use `Mem.extends`
4. prove current-step simulation case-by-case
5. prove the backward simulation theorem

The proof should explicitly budget work for:

- `Lgetstack` spill/reload interaction in `V1`
- `Lsetstack` overlap-sensitive spill/reload interaction in `V2`
- move-heavy regalloc artifacts:
  - entry shuffles
  - parmove cycle breaking
  - stack-to-stack repair through temporaries
  - two-address repair `Omove`
  - splitlong helper moves
- intra-block stepping and block-local program points
- call
- tailcall
- return
- external-call result placement

The match relation should track protected registers plus protected
`Local` slots, with explicit interface-discipline call boundaries.

The proof should consume:

- the checked pairwise-`Loc.diff` invariant for protected local slots
- the explicit `LTLabi.wf_program` assumptions extracted from the
  allocation-validator path
- the certified point-indexed fault classification

### Phase 7: Final theorem in `driver/Complements.v`

**Milestone theorem (`V1`)**

```coq
Theorem transf_c_program_to_ltl_preservation_faulty_v1 :
  forall p tp fc beh,
    transf_c_program_to_ltl p = OK tp ->
    LTLcolorcheck.check_program tp = Some fc ->
    LTLfaultspec.is_v1_faultclass tp fc ->
    program_behaves (LTLfault.faulty_semantics tp fc) beh ->
    exists beh', program_behaves (Csem.semantics p) beh'
              /\ behavior_improves beh' beh.
```

**Strengthened theorem (`V2`)**

```coq
Theorem transf_c_program_to_ltl_preservation_faulty :
  forall p tp fc beh,
    transf_c_program_to_ltl p = OK tp ->
    LTLcolorcheck.check_program tp = Some fc ->
    program_behaves (LTLfault.faulty_semantics tp fc) beh ->
    exists beh', program_behaves (Csem.semantics p) beh'
              /\ behavior_improves beh' beh.
```

**Proof composition**

1. faulty `LTL`@Two is refined by non-faulty `LTL`@Three via the new
   tolerant theorem
2. the checker output yields both `LTLcolor.wc_program` and certified
   `LTLfaultspec.wf_faultclass`
3. `Allocation` outputs satisfy `LTLabi.wf_program`
4. `LTL`@Three is refined by post-TMR RTL@Three via the new allocation
   preservation lemma
5. post-TMR RTL@Three is refined by pre-TMR RTL@Three via the existing
   TMR theorem
6. pre-TMR RTL@Three is refined by C via the existing weak-agreement +
   standard compiler-correctness chain
7. compose `behavior_improves` transitively

The `V2` theorem should reuse the same composition and differ only in
the larger certified fault classification admitted by the checker and
tolerant theorem.

## Open design questions

### 1. Exact block-local point representation

The main static-design choice is whether to represent points as:

- `(pc, instruction-index)`
- `(pc, block-suffix)`
- or a small finite encoding isomorphic to one of the above

The choice should be made based on proof ergonomics and checker cost,
not abstraction purity.

### 2. How much of Allocproof's infrastructure to reuse directly

`Allocation` and `Allocproof` already have substantial overlap-aware
location machinery and well-formedness facts for generated `LTL`.

The first implementation should reuse as much of that infrastructure as
practical, especially for:

- overlap-aware location reasoning
- entrypoint sanity
- call/return well-formedness consequences

### 3. Whether to add Tunneling as a second theorem step

Once the `LTL` theorem lands, there is a natural follow-on theorem:

```text
LTL -> tunneled LTL
```

That extension should be treated as a separate proof step, not folded
into the first `LTL` milestone.

## Recommended implementation order

1. `transf_c_program_to_ltl` cut point and basic preservation lemmas
2. indexed-point / continuation-witness design
3. `LTL` determinacy lemma plus RTL@Three -> LTL@Three backward
   preservation through `Allocation`
4. thin `LTLabi.wf_program` extracted from `Allocproof`, plus proof that
   `Allocation` outputs satisfy it
5. declarative `LTL` color system plus independent declarative
   faultability specification, parameterized by the chosen point design
6. Boolean checker + oracle returning certified fault-site metadata
7. faulty `LTL` semantics parameterized by the certified fault
   classification
8. `V1`: certify the register-destination fault class and prove the
   first tolerant theorem
9. `V1`: compose the first end-to-end `transf_c_program_to_ltl`
   preservation theorem
10. `V2`: enlarge the certified fault class to protected `Local`-slot
    writes
11. `V2`: strengthen the tolerant theorem and the final composed theorem

## Practical payoff

- the TMR transformation survives register allocation
- `V1` lands the first post-regalloc theorem with substantially less
  proof machinery than a direct `Linear` target
- `V2` then extends the theorem to the larger overlap-sensitive class of
  protected post-regalloc writes available under the current
  White-boundary design

This gives the fastest path to a backend-level theorem under the current
prototype design.
