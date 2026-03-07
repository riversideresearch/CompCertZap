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

## Relationship to the interface-TMR plan

This plan deliberately separates two questions:

1. **Where is the theorem proved?**
   Here: at `Linear`.
2. **What TMR interface discipline is assumed at function boundaries?**
   Either:
   - the current design, where call/return boundaries are White, or
   - a future extended design where protected values cross internal
     calls and returns via replicated parameters and hidden
     out-parameters

The second question is covered by
[`plans/interface-tmr-plan.md`](plans/interface-tmr-plan.md).

This `Linear` plan therefore supports two variants:

- **Variant A:** current White-boundary TMR
- **Variant B:** extended interface TMR

Most of the theorem-composition path is shared. The main differences are
in the checker invariant and the faulty simulation match relation.

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

This depends on the TMR interface variant:

- **Variant A:** protected values live only in registers and `Local`
  slots; `Incoming` and `Outgoing` are White-only interface locations
- **Variant B:** protected values may also live in argument/result
  interface locations for internal TMR-to-TMR calls

### 5. Prefer sparse or liveness-bounded checker state

The location domain is not fixed-size because stack slots vary by
function. A fully dense `program point x loc` representation may become
expensive.

For the first implementation, use one of:

1. only locations relevant to the function, or
2. a proof-oriented location liveness analysis

Unlike the theorem shape, this is an engineering choice, not a semantic
one. It can be revisited as the checker/proof develops.

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

## Variant A: Current White-boundary TMR

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

The checker still needs rules mentioning `Incoming`/`Outgoing`, but only
to constrain them to White behavior rather than to treat them as
protected channels.

### Consequences for the faulty simulation

The match relation only needs to track protected consistency over:

- machine registers
- protected local slots

Calls and returns are simpler here because:

- `Incoming`/`Outgoing` are not part of the protected invariant
- the proof can treat the interface as an intentional White boundary

## Variant B: Extended interface TMR

This variant depends on a stable design from
[`plans/interface-tmr-plan.md`](plans/interface-tmr-plan.md).

### Intended protected domain

Protected values may live in:

- `R r`
- `S Local ofs ty`
- internal-call argument locations
- internal-return result channels

In this variant, some `Incoming` and `Outgoing` locations are no longer
just White interface slots. They become part of the protected flow for
internal TMR-to-TMR calls.

### Consequences for the checker

The checker must additionally enforce:

- parameter triples are separated across call boundaries
- hidden out-parameter channels for returns are separated
- internal TMR-to-TMR calls preserve channel correspondence
- wrappers mediate any boundary that still uses the ordinary ABI

### Consequences for the faulty simulation

The match relation must track protected state across:

- call argument setup
- callee entry
- return-channel writes
- caller-side receipt of protected results

This is the main proof burden added by Variant B.

## Shared theorem phases

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

### Phase 1: Backend preservation from RTL to Linear@Three

**Files**

- `driver/Complements.v`

**Actions**

1. Define the composed pass relation from RTL to final `Linear` through:
   - `Alloc`
   - `Tunneling`
   - `Linearize`
   - `CleanupLabels`
   - `Debugvar` if enabled
2. Reuse the existing backend forward simulations instantiated at
   `Three`.
3. Convert the composed forward simulation to backward simulation using
   `forward_to_backward_simulation`.
4. Prove a lemma of the shape:

```coq
backward_simulation
  (@RTL.semantics Three VoteSemantics_Three p)
  (@Linear.semantics Three VoteSemantics_Three tp).
```

**Additional proof note**

Make explicit any determinacy lemma needed for `Linear` to use
`forward_to_backward_simulation`.

### Phase 2: Declarative location-aware color system for Linear

**New file**

- `backend/Linearcolor.v`

**Shared actions**

1. Define a coloring over `loc`.
2. Define well-coloredness for `Linear` instructions.
3. Include rules for:
   - `Lop`
   - `Lload`
   - `Lstore`
   - `Lgetstack`
   - `Lsetstack`
   - calls / tailcalls / returns
   - builtins including votes and smoves
   - labels / gotos / conditionals / jumptables

**Variant-specific obligation**

The specification must state exactly which slot kinds may carry
protected colors:

- Variant A: only `Local`
- Variant B: `Local` plus selected interface locations

### Phase 3: Verified Boolean checker

**New file**

- `backend/Linearcolorcheck.v`

**Actions**

1. Follow the RTL checker architecture:
   - inference oracle
   - verified Boolean checker
2. Prove:

```coq
Lemma check_program_sound :
  check_program p = true ->
  Linearcolor.wc_program p.
```

**Design note**

If a dense `pc x loc` domain becomes awkward, switch early to a sparse
or liveness-bounded formulation instead of forcing a quadratic
representation.

### Phase 4: Unverified inference oracle

**New file**

- `backend/Linearinfercolor.ml`

**Actions**

1. Implement a first oracle over `Linear` locations.
2. Prefer sparse storage keyed only by relevant locations.
3. Wire extraction similarly to the existing RTL checker pipeline.

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
- `Lload`: likely not faultable in the first version, matching the RTL
  prototype's conservative choice
- `Lgetstack`, `Lsetstack`, `Lstore`, calls, tailcalls, votes, and other
  intentionally uncovered operations: start conservative

### Phase 6: Faulty backward simulation at Linear

**New file**

- `backend/Lineartolerant.v`

**Core theorem**

```coq
Theorem faulty_backward_simulation :
  Linearcolor.wc_program prog ->
  backward_simulation
    (@Linear.semantics Three VoteSemantics_Three prog)
    (Linearfault.faulty_semantics prog).
```

**Shared proof structure**

1. define a location-set match relation
2. define a stack-frame match relation
3. use `Mem.extends`
4. prove current-step simulation case-by-case
5. prove the backward simulation theorem

**Variant-specific proof burden**

- Variant A: match relation tracks protected registers plus `Local`
  slots, with White call boundaries
- Variant B: match relation also tracks protected argument/result
  interface channels across internal calls and returns

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

### 2. How early should Variant B be attempted?

Variant B should not be started until the interface-TMR plan has stable
answers for:

- eligibility of transformed calls
- wrapper policy
- hidden out-parameter design

Until then, Variant A is the default path.

## Recommended implementation order

### Recommended order for Variant A

1. `transf_c_program_to_linear` cut point and basic preservation lemmas
2. backend RTL@Three -> Linear@Three preservation
3. declarative `Linear` color system with protected domain
   = registers + `Local` slots
4. Boolean checker + oracle
5. faulty `Linear` semantics
6. tolerant backward simulation
7. final composed theorem

### Recommended order for Variant B

1. complete the interface-TMR design plan
2. revise the protected-location domain and call/return rules in
   `Linearcolor`
3. extend checker/oracle accordingly
4. strengthen `Lineartolerant` to track protected state through internal
   calls and returns
5. rebuild the final theorem

## Practical payoff

Both variants establish the same milestone:

- the TMR transformation survives register allocation and the
  location-level backend through `Linear`

Variant A gives the fastest path to a `Linear` theorem under the current
prototype design.

Variant B is the path to stronger protection once function interfaces
are themselves incorporated into TMR.
