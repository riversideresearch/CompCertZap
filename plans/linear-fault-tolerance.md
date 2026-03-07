# Plan: Extending Fault Tolerance to Linear

## Goal

Prove a `Linear`-level analogue of the current RTL theorem:

```coq
Theorem transf_c_program_to_linear_preservation_faulty :
  forall p tp beh,
    transf_c_program_to_linear p = OK tp ->
    Linearcolorcheck.check_program tp = true ->
    program_behaves (Linearfault.faulty_semantics tp) beh ->
    exists beh', program_behaves (Csem.semantics p) beh'
              /\ behavior_improves beh' beh.
```

This should target the latest backend IR that still exposes abstract
locations directly, namely `Linear`.

## Why target Linear first

`Linear` is a good intermediate target because it already includes:

- machine registers and abstract stack locations via `loc`
- explicit `Callstate` / `Returnstate`
- explicit stack frames

At the same time, it is late enough in the pipeline to cover the pass of
greatest concern for TMR separation: register allocation.

Targeting `Linear` avoids most of the Asm-specific complexity:

- no instruction-position tags
- no metadata needed to recover origin through lowering
- no `PC`/layout issues
- no temporary-register classification issues
- no multi-instruction expansion issues

## Scope

This plan targets the current TMR design, where function boundaries
enforce a **White interface discipline**.

Concretely:

- protected values may live only in machine registers and `Local` stack
  slots
- `Incoming` and `Outgoing` locations are interface-only and must remain
  White
- call arguments, return values, and call-target channels must remain
  White at function boundaries
- the proof must account explicitly for `call_regs`, `return_regs`,
  caller-save destruction, and function-entry destruction rather than
  treating the whole boundary as "everything becomes White"

Extending TMR across function boundaries is out of scope for this plan.
If that work is revived later, it should be treated as a separate design
and proof effort rather than folded into this one.

## Shared high-level proof shape

Keep the same refinement composition pattern as the current RTL proof:

```text
C >=2 RTL(no votes) >=3 RTL(no votes) >=3 RTL+TMR >=3 Linear >=2,faulty Linear
 (1) standard       (2) weak agree    (3) TMR sim  (4) backend   (5) faulty sim
```

Interpretation:

1. reuse the existing standard compiler-correctness chain from C to
   pre-TMR RTL
2. reuse weak agreement at RTL exactly as in the current proof
3. reuse the existing TMR correctness theorem at RTL
4. add a new backend preservation lemma from post-TMR RTL@Three to
   final `Linear`@Three
5. add a new faulty backward simulation from non-faulty
   `Linear`@Three to faulty `Linear`@Two

This preserves the current proof architecture while moving the target
language from RTL to `Linear`.

## Common design decisions

### 1. Track locations, not just registers

At `Linear`, values live in locations:

- `R mreg`
- `S slot ofs ty`

Therefore the color system should track `loc`, not only registers.

This is the main design difference from the register-only Asm proposal.
It allows the checker to reason directly about spills and reloads
without reconstructing location information from lower-level code.

### 2. Keep the fault model register-only initially

Even though the checker should reason about locations, the first faulty
semantics can still follow the existing RTL fault model and corrupt only
register destinations.

That means:

- zappable destinations are `R r`
- stack-slot writes are not faulted directly
- stack locations may still be colored if they are part of the
  protected separation story

Crucially, this should still include **protected local reloads**:

- `Lgetstack Local ...` writes a register destination and should be
  faultable
- if a protected value is spilled to separated `Local` slots and then
  reloaded into replicated registers, a fault on one reload should still
  be tolerated by the usual single-fault argument

But this should **not** include interface reloads:

- `Lgetstack Incoming ...` reads an unreplicated parameter channel and
  must remain outside the first theorem's fault coverage
- `Lgetstack Outgoing ...` is likewise an interface/ABI operation, not a
  protected local reload

So the first `Linear` theorem should cover faults on `Lop` and
`Lgetstack Local ...`, while still excluding direct faults on stack-slot
writes such as `Lsetstack` and `Lstore`.

### 3. Reuse Linear's explicit call/return structure

Unlike Asm, `Linear` already has:

- `State`
- `Callstate`
- `Returnstate`
- explicit stack frames

Therefore the faulty simulation should use an ordinary stack-frame match
relation, not a ghost caller-context stack.

### 4. Be explicit about the protected location domain

The crucial design choice is not whether `Linear` contains
`Incoming`/`Outgoing` slots. It does. The question is whether those
locations are allowed to carry protected values.

For this plan, protected values live only in:

- `R r`
- `S Local ofs ty`

`Incoming` and `Outgoing` locations are White-only interface locations.

### 5. Use liveness-bounded checker state

The location domain is not fixed-size because stack slots vary by
function. A dense `program point x loc` representation is expected to be
too expensive at `Linear`, so the first viable design should be
**liveness-bounded** rather than dense.

However, two representation choices should be made early because they
affect the checker specification and the faulty simulation invariant:

1. **Program points.**
   `Linear` states use code suffixes as their current position, not RTL
   node identifiers. For static analysis and checker purposes, use
   **instruction indices in `fn_code`** as the canonical finite program
   point representation.
2. **Tracked location domain.**
   Use a finite per-function tracked set of `loc`s rather than all
   possible stack slots.

Recommended initial approach:

- define a shared indexing layer for `Linear` based on instruction
  indices
- build label-resolution and successor facts over those indices
- prove bridge lemmas between runtime code suffixes and static indices
- define a fixed finite per-function tracked domain `Dom(f)` and use it
  uniformly in the declarative specification, the Boolean checker, the
  oracle, and the faulty simulation
- include all machine registers in `Dom(f)`
- include every stack location syntactically mentioned in the function
  body in `Dom(f)`, including `Lgetstack`, `Lsetstack`,
  builtin/debug-argument locations, and any other explicit `loc`
  mention
- include all ABI boundary locations induced by `loc_parameters`,
  `loc_arguments`, `loc_result`, and call-target channels in `Dom(f)`,
  even when they are only needed for White-interface obligations
- if a tracked `Local` slot may be protected, include enough
  syntactically-mentioned overlapping stack locations to make the
  checked `Loc.diff` non-overlap invariant sound
- keep liveness and tracked-domain construction conceptually separate:
  `Dom(f)` determines which locations are ever visible to the proof,
  while liveness only determines which of those tracked locations matter
  at a given program point

This is effectively "instruction indices plus a shared `Linearindex`
library", not a new semantic IR.

### 6. Make protected local non-overlap explicit

The color system should not rely on an implicit global theorem that all
mentioned `Local` slots are pairwise non-overlapping.  Instead, it
should carry an explicit invariant:

- at each program point, distinct protected non-White `Local` slots are
  pairwise `Loc.diff`

This invariant should be checked over the same finite tracked location
domain used by the checker and the faulty simulation.

Why this matters:

- `Locmap.set` invalidates partially overlapping locations
- `Linear` typing/bounds validate slots but do not by themselves give a
  global pairwise-non-overlap theorem for all mentioned slots
- the faulty simulation wants a direct way to conclude that updating one
  protected location leaves the others unchanged

Recommended use:

- make non-overlap part of declarative well-coloredness
- have the checker enforce it over tracked protected `Local` slots
- consume it in the simulation via `Locmap.gso`/`Loc.diff`

### 7. Make the tracked location domain overlap-closed

The tracked location domain cannot be an arbitrary sparse subset.  If an
untracked stack slot can overlap a tracked protected `Local` slot, then
an untracked `Lsetstack` could silently invalidate the protected
invariant.

Therefore the finite tracked domain should satisfy:

- all machine registers are tracked
- all ABI boundary locations needed for entry/call/return obligations
  are tracked
- all syntactically mentioned stack locations are tracked
- if a tracked `Local` slot may be protected, then any stack location
  that is syntactically mentioned and may overlap it is also tracked

This gives the checker and simulation a sound basis for using the
checked pairwise-`Loc.diff` invariant.

In particular, the plan should not start from "currently live
locations only" or "whatever locations the oracle inferred".  The
tracked domain must be fixed independently of liveness so that
call/return rules remain strong enough and overlap soundness does not
depend on oracle accidents.

### 8. Make function-entry obligations explicit

The hardest call-boundary issue is function entry.  `call_regs` copies
registers from caller to callee, and `exec_function_internal` only
applies `undef_regs destroyed_at_function_entry` on top of that.  So the
callee does not begin in an arbitrary "all White" state.

The plan should therefore require an explicit entrypoint discipline:

- parameter locations at function entry are White
- any tracked location that is live at function entry must be a
  parameter location
- non-parameter tracked locations must be defined before any protected
  use

This is the `Linear` analogue of making entrypoint compatibility a
first-class checked condition, rather than discovering it ad hoc inside
the faulty simulation proof.

## Where to cut the compiler pipeline

Target final `Linear` code after:

- `Alloc`
- `Tunneling`
- `Linearize`
- `CleanupLabels`
- `Debugvar` if enabled

and stop before:

- `Stacking`
- `Asmgen`

This captures register allocation and the linearized location-level
backend while avoiding the loss of abstract stack-slot structure.

## White-Boundary Consequences

### Intended protected domain

Protected values may live in:

- `R r`
- `S Local ofs ty`

`Incoming` and `Outgoing` locations are treated as interface-only and
remain White.

This matches the current TMR discipline in which function parameters and
results are not themselves triplicated across the boundary.

### Consequences for the checker

The checker must enforce:

- loads/stores involving `Local` slots preserve separation
- calls consume White arguments
- call results are White
- returns expose only White interface values
- tailcalls satisfy the same White interface discipline while also
  accounting for the `return_regs` / `call_regs` transition
- distinct protected `Local` slots at a program point are pairwise
  non-overlapping

The checker still needs rules mentioning `Incoming`/`Outgoing`, but only
to constrain them to White behavior rather than to treat them as
protected channels.

The call/return rules should be phrased over whole-location-set effects,
not just explicit argument/result locations.  In particular, the
specification should state the intended White/protected behavior for:

- `call_regs` at function entry
- `return_regs` at return and tailcall
- caller-save vs. callee-save machine registers
- `Local`, `Incoming`, and `Outgoing` slots separately
- external-call argument/result placement via `loc_arguments` and
  `loc_result`

At function entry, the specification should also state:

- parameter locations are White
- live tracked locations at entry are restricted to parameter locations
- non-parameter tracked locations are irrelevant until defined

### Consequences for the faulty simulation

The match relation only needs to track protected consistency over:

- machine registers
- protected local slots

Calls and returns are simpler here because:

- `Incoming`/`Outgoing` are not part of the protected invariant
- the proof can treat the interface as an intentional White boundary

But they are still not trivial.  The proof must handle the ABI-mediated
transformations performed by:

- `call_regs` at function entry
- `return_regs` at returns and tailcalls
- `loc_arguments` / `loc_result` for external calls
- caller-save destruction and function-entry destruction

The simulation should not have to discover these obligations on its own.
They should already be reflected in the checker/specification as
first-class interface-discipline rules.

## Theorem Phases

### Phase 0: Add a truncated compiler to Linear

**Files**

- `driver/Compiler.v`
- `driver/Complements.v`

**Actions**

1. Define `transf_c_program_to_linear`.
2. Factor the existing compiler composition so there is a clean theorem
   path from C to final `Linear`.
3. Add helper lemmas analogous to the existing RTL truncation lemmas.

**Desired result**

A `Linear` truncation theorem analogous to the existing
`transf_c_program_to_rtl_preservation`, but targeting ordinary
non-faulty `Linear`.

This phase should also preserve the exact optional pass structure around
`Debugvar`, since the target cut point includes it.

### Phase 1: Backend preservation from RTL to Linear@Three

**Files**

- `driver/Complements.v`
- `backend/Linear.v` or a small new proof file for `Linear`
  metatheory, if preferred

**Actions**

1. Define the composed pass relation from RTL to final `Linear` through:
   - `Alloc`
   - `Tunneling`
   - `Linearize`
   - `CleanupLabels`
   - `Debugvar` if enabled
2. Reuse the existing backend forward simulations instantiated at
   `Three`.
3. Prove the semantic side conditions needed to convert the composed
   forward simulation to backward simulation, in particular a
   `Linear.semantics_determinate` lemma analogous to the existing RTL
   one.
4. Convert the composed forward simulation to backward simulation using
   `forward_to_backward_simulation`.
5. Prove a lemma of the shape:

```coq
backward_simulation
  (@RTL.semantics Three VoteSemantics_Three p)
  (@Linear.semantics Three VoteSemantics_Three tp).
```

**Additional proof note**

Make explicit that the proof path must respect the existing
`find_label` behavior of `Linear` (first matching label occurrence),
since any indexed control-flow view must agree with it.

### Phase 2: Declarative location-aware color system for Linear

**New file**

- `backend/Linearcolor.v`

**Likely supporting files**

- `backend/Linearindex.v`
- `backend/LinearProofLiveness.v`

**Actions**

1. Define a finite static program-point representation for `Linear`
   instructions, preferably instruction indices in `fn_code`.
2. Define a proof-oriented liveness analysis over those program points
   and tracked `loc`s.
3. Define a coloring over `loc`.
4. Define well-coloredness for `Linear` instructions.
5. Include rules for:
   - `Lop`
   - `Lload`
   - `Lstore`
   - `Lgetstack`
   - `Lsetstack`
   - calls / tailcalls / returns
   - builtins including votes, smoves, and `EF_debug`
   - labels / gotos / conditionals / jumptables

The checker/specification should treat calls, tailcalls, returns, and
external calls as first-class cases, not as minor variations on other
instructions, because they perform ABI-level transformations on the
whole `locset`.

This phase should consume the fixed per-function tracked domain `Dom(f)`
from the common design decisions above, rather than leaving the domain
as an oracle-side choice.

The specification must state explicitly that only `Local` slots may
carry protected colors among stack locations, while `Incoming` and
`Outgoing` remain White-only interface locations.

The specification should also include an explicit protected-local
non-overlap invariant:

- if two tracked `Local` slots are both protected (non-White) at a
  program point and are distinct, then they satisfy `Loc.diff`

Instruction rules should preserve this invariant at successors.

For calls, returns, tailcalls, and external calls, specify the full
location-set discipline up front:

- which locations must be White before the instruction
- how `call_regs` changes the callee-entry view
- how `return_regs` changes the post-return / tailcall view
- which caller-save registers may be forgotten
- which callee-save registers and stack locations are preserved
- how `loc_arguments` / `loc_result` interact with White boundaries

For function entry, specify the live-in discipline up front:

- parameter locations are White at entry
- any tracked location live at entry must be a parameter location
- no protected non-parameter location is assumed across the boundary

For `EF_debug` builtins in the first theorem:

- treat them as White/debug-interface operations
- do not treat them as protected computation
- keep their rule aligned with the current RTL treatment, rather than
  trying to optimize around them initially

### Phase 3: Verified Boolean checker

**New file**

- `backend/Linearcolorcheck.v`

**Likely supporting files**

- `backend/Lineartyping.v`

**Actions**

1. Add a whole-program well-typedness wrapper for the existing Linear
   type checker in `Lineartyping`:
   - define `wt_program : Linear.program -> Prop`
   - define a Boolean whole-program checker that runs `wt_function` on
     internal functions
   - prove the Boolean checker sound with respect to `wt_program`
2. Follow the RTL checker architecture:
   - inference oracle
   - verified Boolean checker
3. Integrate the well-typedness check with the color checker, either by
   folding it into `Linearcolorcheck.check_program` or by proving a
   paired top-level theorem that exposes both conclusions
4. Prove:

```coq
Lemma check_program_sound :
  check_program p = true ->
  Lineartyping.wt_program p /\ Linearcolor.wc_program p.
```

**Design note**

The Boolean checker should consume the same indexed program-point view
and proof-liveness information used by the declarative specification, so
that checker soundness and the faulty simulation invariant do not drift
apart.

It should also consume the same finite tracked location domain used by
the simulation invariant.  In particular, the protected-local
non-overlap guarantee is only as strong as the tracked domain over which
it is checked.

The tracked domain should be overlap-closed enough that an untracked
stack write cannot overlap a tracked protected `Local` slot.

The important point is that well-typedness should not be rediscovered
inside the faulty simulation proof.  The simulation should assume it via
the `Lineartyping` wrapper produced by the checker path and then use the
existing consequences of `wt_state` for slot validity, tailcalls,
builtins, and call/return agreement.

### Phase 4: Unverified inference oracle

**New file**

- `backend/Linearinfercolor.ml`

**Actions**

1. Implement a first oracle over `Linear` locations.
2. Prefer sparse storage keyed only by relevant locations.
3. Reuse the shared indexed program-point representation rather than
   inventing a separate oracle-local numbering.
4. Wire extraction similarly to the existing RTL checker pipeline.

The oracle should target the same tracked location domain that the
checker validates and the simulation consumes.

### Phase 5: Faulty Linear semantics

**New file**

- `backend/Linearfault.v`

**Actions**

1. Define a faulty state wrapper with a global fault bit.
2. Define `maybe_zap` in the `Linear` style.
3. Allow faults only on register destinations for the first theorem.
4. Define `faulty_semantics` at vote type `Two`.

**Suggested classification**

- `Lop`: faultable exactly when the underlying `operation` is not
  protected
- `Lgetstack Local ...`: faultable, since it reloads a protected local
  value into a register destination and should be covered by the theorem
- `Lgetstack Incoming ...` and `Lgetstack Outgoing ...`: not faultable
  in the first theorem, because they read interface/ABI channels rather
  than protected local storage
- `Lload`: likely not faultable in the first version, matching the RTL
  prototype's conservative choice
- `Lsetstack`, `Lstore`, calls, tailcalls, and direct stack writes:
  unfaultable in the first theorem
- votes, `smove`, and `EF_debug` builtins: classify explicitly and keep
  them unfaultable if they are intended to remain outside the
  single-fault coverage argument

### Phase 6: Faulty backward simulation at Linear

**New file**

- `backend/Lineartolerant.v`

**Core theorem**

```coq
Theorem faulty_backward_simulation :
  Lineartyping.wt_program prog ->
  Linearcolor.wc_program prog ->
  backward_simulation
    (@Linear.semantics Three VoteSemantics_Three prog)
    (Linearfault.faulty_semantics prog).
```

**Proof structure**

1. define a location-set match relation
2. define a stack-frame match relation
3. use `Mem.extends`
4. prove current-step simulation case-by-case
5. prove the backward simulation theorem

The case analysis should explicitly budget proof work for:

- `Lgetstack` / `Lsetstack` spill-reload interaction
- call
- tailcall
- return
- external call builtins / ABI result placement

The match relation should track protected registers plus `Local` slots,
with explicit interface-discipline call boundaries. The proof should
treat `call_regs`,
`return_regs`, external-call result placement, caller-save destruction,
and function-entry destruction as first-class invariant transitions.

The match relation should also consume the checked non-overlap invariant
for protected local slots, so that when one protected location is
updated the proof can show that the other protected locations are
unchanged via `Loc.diff`.

The proof should make systematic use of the existing `Lineartyping`
infrastructure, rather than reproving slot-validity or ABI sanity facts
from scratch.

### Phase 7: Final theorem in `driver/Complements.v`

**Target theorem**

```coq
Theorem transf_c_program_to_linear_preservation_faulty :
  forall p tp beh,
    transf_c_program_to_linear p = OK tp ->
    Linearcolorcheck.check_program tp = true ->
    program_behaves (Linearfault.faulty_semantics tp) beh ->
    exists beh', program_behaves (Csem.semantics p) beh'
              /\ behavior_improves beh' beh.
```

**Proof composition**

1. faulty `Linear`@Two is refined by non-faulty `Linear`@Three via the
   new `Linear` tolerant theorem
2. `Linear`@Three is refined by post-TMR RTL@Three via the new backend
   preservation lemma
3. post-TMR RTL@Three is refined by pre-TMR RTL@Three via the existing
   TMR theorem
4. pre-TMR RTL@Three is refined by C via the existing weak-agreement +
   standard compiler-correctness chain
5. compose `behavior_improves` transitively

## Open design questions

### 1. Sparse mentioned-locations vs. location liveness

The checker and simulation proof may want:

- only locations mentioned in the function
- all protected registers plus relevant stack locations
- a proof-oriented liveness-bounded domain

This should be decided based on proof ergonomics and oracle cost, not on
proof architecture.

Specific risks:

- tracking all mentioned `Local` slots may bloat the checker state with
  dead locations
- ordinary dead-code liveness may be too weak for simulation
  obligations, just as at RTL
- if protected `Local` slots are tracked but their pairwise non-overlap
  is not checked, stack-slot overlap can invalidate the intended
  separation invariant

Likely mitigations:

- start from the fixed conservative domain `Dom(f)` described above
- prune obligations within `Dom(f)` using a dedicated proof-oriented
  liveness analysis
- include boundary-specific White obligations for `loc_arguments`,
  `loc_result`, `call_regs`, and `return_regs`
- include an explicit pairwise-`Loc.diff` check for tracked protected
  `Local` slots

The remaining design choice is therefore not whether boundary locations
are tracked, but only how much liveness information is needed to avoid
paying for the full fixed domain at every program point.

### 2. Indexed helper layer vs. new IR

The default plan should be:

- use instruction indices as the static representation of program points
- factor shared lookup/successor/label lemmas into an auxiliary indexed
  library
- avoid introducing a separate semantic `IndexedLinear` language unless
  the suffix-to-index bridge becomes a serious proof bottleneck

## Recommended implementation order

1. `transf_c_program_to_linear` cut point and basic preservation lemmas
2. backend RTL@Three -> Linear@Three preservation
3. declarative `Linear` color system with protected domain
   = registers + `Local` slots
4. Boolean checker + oracle
5. faulty `Linear` semantics
6. tolerant backward simulation
7. final composed theorem

## Practical payoff

- the TMR transformation survives register allocation and the
  location-level backend through `Linear`

This gives the fastest path to a `Linear` theorem under the current
prototype design.
