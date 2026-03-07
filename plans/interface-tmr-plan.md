# Plan: Extending TMR Across Function Boundaries

## Goal

Extend the current TMR design so that protected values can cross
internal function boundaries without being majority-voted at every call
and re-replicated after every return.

Concretely, this means:

- internal TMR-protected functions receive replicated arguments
- internal TMR-protected functions produce replicated results
- function boundaries cease to be uniformly White for protected flows

This plan is meant to cover the full prototype impact if we were to
implement the change now:

- transformation design
- proof of TMR soundness
- color system / checker consequences
- faulty simulation consequences
- top-level theorem consequences

It is intentionally written first at the RTL level, because that is
where the current prototype proves both TMR soundness and fault
tolerance.

## Current baseline

Today the prototype has the following structure:

- the TMR pass is inserted at RTL
- calls and returns are White boundaries
- the TMR pass soundness theorem lives in `backend/RTLtmrproof.v`
- fault tolerance is proved by the checker + faulty simulation route:
  `RTLcolor.v`, `RTLcolorcheck.v`, `RTLtolerant.v`,
  `driver/Complements.v`

High-level proof chain today:

```text
C >=2 RTL(no votes) >=3 RTL(no votes) >=3 RTL+TMR >=2,faulty RTL+TMR
```

If interface TMR is added, steps (1) and (2) stay the same, but step
(3) changes substantially and step (4) must be strengthened because the
checker and faulty simulation will now need to reason through calls and
returns.

## Core design choice

Use replicated parameters plus hidden out-parameters for replicated
results.

### Parameters

For an original internal function

```text
f : (A1, ..., An) -> R
```

the transformed internal TMR-protected function receives

```text
f_tmr : (A1r, A1g, A1b, ..., Anr, Ang, Anb, result channels...) -> void-or-R
```

where each original argument is threaded as a triple.

### Returns

Do **not** attempt to encode a triple directly in the machine return
convention. CompCert signatures and calling conventions currently expose
a single result type with at most an `rpair` result location.

Instead, return triples through hidden output parameters:

- either three output pointers (`out_r`, `out_g`, `out_b`)
- or one pointer to a result-triple aggregate

For a first design, prefer three hidden output pointers because the
triple structure is explicit in the transformed IR and easy to reason
about.

## Why hidden out-parameters

This avoids a backend-wide ABI redesign.

Advantages:

- no need to generalize `sig_res`
- no need to redefine `loc_result`
- no need to change result-handling machinery in `LTL`, `Linear`,
  `Mach`, or `Asm`
- external boundaries can be mediated by wrappers

Cost:

- the transformed function interface is more invasive
- hidden pointers become part of the trusted boundary protocol

## Scope and non-scope

### In scope

- transformed internal function signatures
- transformed internal call sites
- transformed internal returns
- wrappers/adapters for non-TMR boundaries
- updated TMR pass and proof
- updated checker and faulty simulation assumptions
- updated top-level fault-tolerance theorem path

### Out of scope for the first version

- arbitrary indirect-call support
- whole-program binary interoperability without wrappers
- backend-specific implementation below RTL

## Boundary policy

Distinguish two kinds of call boundaries.

### 1. Internal TMR-to-TMR calls

These use the transformed interface:

- arguments are passed as triples
- results are written through hidden out-parameters as triples

No majority vote is inserted merely to cross the call boundary.

### 2. TMR-to-non-TMR boundaries

These include:

- calls to external functions
- calls to internal functions not transformed for interface TMR
- calls that remain indirect / address-taken in the first version

These boundaries require wrappers or adapters:

- when calling out from protected code, vote before crossing
- when receiving a result from unprotected code, treat it as White and
  re-replicate if needed

For a first version, keep these wrappers explicit and conservative.

## Recommended restrictions for a first implementation

To keep the first proof tractable:

- transform only direct internal calls
- require the callee to be non-address-taken
- leave indirect calls on the current White-boundary discipline
- leave external calls on the current White-boundary discipline
- preserve the external ABI of `main`

This gives a clean first design without having to redesign function
pointer semantics globally.

## New proof obligations introduced by interface TMR

This section is the main addition over the previous version of the plan.

### 1. TMR transformation soundness changes

The existing TMR soundness proof is largely intra-procedural. With
interface TMR, it must also cover:

- transformed function entry conventions
- transformed call instructions
- transformed returns
- wrapper correctness

The match relation used in `backend/RTLtmrproof.v` will need new cases
for:

- call-state correspondence with replicated arguments
- return-state correspondence with replicated result channels
- transitions through wrappers

### 2. Agreement changes

Agreement is no longer only about vote sites inside function bodies.
It must additionally account for:

- entry parameter triples of transformed callees
- result triples produced by transformed returns
- wrapper obligations at boundaries to unprotected code

This does **not** necessarily require changing the weak-agreement leg in
`RTLagreement.v`. The standard chain

```text
C >=2 RTL(no votes) >=3 RTL(no votes)
```

can stay as it is. What changes is the TMR correctness theorem: the
replicated program it produces now has a richer interface discipline,
and the soundness argument must establish the corresponding replicated
entry/return invariants.

### 3. Separation changes

Protected state can now flow through function interfaces.

Therefore separation must cover not only ordinary replicated registers
inside a function, but also:

- replicated call arguments
- hidden result channels
- wrapper-induced vote / re-replication boundaries

This is the key reason the checker and faulty simulation must change.

### 4. Checker changes

The default assumption should be that the checker remains mostly local
and per-function.

At minimum, the RTL color system/checker will need to express:

- transformed internal calls consume correctly-colored triples
- callee entry parameters begin with the expected colors
- transformed returns produce correctly-colored result triples
- wrapper bodies satisfy their intended White/protected interface
  contracts

This does **not** by itself require an interprocedural color analysis.
If the transformation proof already guarantees:

- which functions use the transformed ABI
- which call sites target that ABI
- where wrappers are inserted

then the checker can likely stay local and simply validate separation
within each transformed function or wrapper body.

Only introduce explicit program-level interface compatibility checks if
some boundary fact cannot be pushed into the transformation/wrapper
correctness proof.

### 5. Faulty simulation changes

The current faulty simulation in `backend/RTLtolerant.v` relies on
calls/returns being White boundaries in a crucial way.

With interface TMR, `faulty_backward_simulation` must be strengthened to
track protected state through:

- call argument setup
- callee entry
- return-channel production
- caller receipt of protected results

The fault model itself can remain register-only initially. The main
change is the match relation and the invariants it must preserve at call
and return boundaries.

### 6. Top-level theorem changes

The high-level theorem in `driver/Complements.v` can keep the same
composition pattern, but:

- the TMR soundness leg is a different theorem
- the checker soundness theorem is stronger
- the faulty simulation theorem is stronger

So the top-level statement can remain similar, but the supporting
lemmas are materially different.

## Concrete implementation work

## Phase 0: Freeze the first-version design

Decide and document:

1. eligibility policy for transformed calls
2. hidden result channel shape
3. wrapper policy
4. whether this is an extension of the current RTL TMR pass or a new
   pass family

**Deliverable**

A precise transformed-interface specification.

## Phase 1: Extend the RTL TMR transformation

**Primary files**

- `backend/RTLtmr.v`
- any new helper modules needed for wrapper generation or eligibility

**Actions**

1. Transform internal function signatures to include replicated
   parameters and hidden output channels.
2. Transform direct internal call sites to pass triples and hidden
   result channels.
3. Transform returns to write triple results through hidden
   out-parameters.
4. Insert wrappers/adapters at boundaries that remain on the old ABI.
5. Make sure the transformed program remains well-formed as an RTL
   program.

**Important proof-design decision**

Interface reshaping and replication are semantically coupled.

Why:

- a pure interface-only transformation could be semantics-preserving even
  if the new channels are simply ignored
- but the replication proof needs more than semantic preservation of
  that intermediate program
- it needs the added parameters/result channels to be reserved, fresh,
  and safe to use for replicated values

Therefore, the initial proof plan should treat:

- interface transformation
- intra-procedural replication

as one logically coupled transformation, even if they are implemented as
separate modules or passes for engineering reasons.

Only split the proof if there is a strong intermediate theorem stating a
reservation / non-interference property for the added channels.

## Phase 2: Strengthen TMR soundness at RTL

**Primary file**

- `backend/RTLtmrproof.v`

**Actions**

1. Extend the program match relation to relate original functions with
   transformed signatures and wrapper structure.
2. Extend the state match relation to cover transformed calls and
   returns.
3. Prove simulation lemmas for:
   - transformed function entry
   - transformed internal calls
   - transformed returns
   - wrapper calls in both directions
4. Re-prove the main TMR correctness theorem.

**Expected result**

A replacement for the current `transf_program_correct` theorem that
states semantic preservation of the richer combined transformation
(interface reshaping plus replication).

## Phase 3: Specify interface-level agreement and separation

**Primary files**

- likely `backend/RTLtmrproof.v`
- possibly a new helper file if the specification becomes large

**Actions**

1. State what it means for transformed callee entries to receive valid
   triples.
2. State what it means for transformed returns to produce valid result
   triples.
3. State wrapper correctness obligations.
4. Identify which parts are established directly by TMR soundness and
   which parts are deferred to the color checker.

**Important split**

- agreement of replicated values across channels should still be
  established by TMR construction/soundness
- separation of channels after later compiler passes should still be
  checked a posteriori by the color system

## Phase 4: Extend the RTL color system

**Primary files**

- `backend/RTLcolor.v`
- `backend/RTLcolorcheck.v`
- `backend/RTLinfercolor.ml`

**Actions**

1. Revise the declarative color rules so that transformed internal calls
   can consume protected argument triples, not only White arguments.
2. Add rules or program-level obligations for callee entry parameters.
3. Add rules or program-level obligations for hidden result channels.
4. Add rules for wrappers that bridge protected and White boundaries.
5. Update the checker soundness proof:

```coq
Lemma check_program_sound :
  check_program p = true ->
  RTLcolor.wc_program p.
```

6. Update the inference oracle to infer colors compatible with the new
   call/return interface rules.

**Default architectural choice**

Keep the checker local unless a concrete proof obligation forces a
program-level interface check.

## Phase 5: Strengthen the RTL faulty simulation proof

**Primary file**

- `backend/RTLtolerant.v`

**Actions**

1. Extend the register-match invariant to cover protected state through
   transformed calls and returns.
2. Add match constructors/lemmas for:
   - protected call arguments
   - protected callee entries
   - hidden output channels
   - wrapper transitions
3. Re-prove current-step simulation cases involving calls, returns, and
   builtins used by wrappers.
4. Re-prove:

```coq
Theorem faulty_backward_simulation :
  RTLcolor.wc_program prog ->
  backward_simulation
    (@RTL.semantics Three VoteSemantics_Three prog)
    (RTLfault.faulty_semantics prog).
```

The theorem statement may stay the same, but its proof obligations will
be strictly stronger.

## Phase 6: Rebuild the top-level fault-tolerance theorem

**Primary file**

- `driver/Complements.v`

**Actions**

1. Keep the same high-level refinement composition pattern.
2. Swap in the strengthened TMR correctness theorem.
3. Swap in the strengthened checker soundness theorem.
4. Swap in the strengthened faulty backward simulation theorem.
5. Re-prove the top-level RTL fault-tolerance theorem.

**Expected result**

The current theorem shape remains the target:

```coq
Theorem transf_c_program_to_rtl_preservation_faulty :
  forall p tp beh,
    transf_c_program_to_rtl p = OK tp ->
    RTLcolorcheck.check_program tp = true ->
    program_behaves (RTLfault.faulty_semantics tp) beh ->
    exists beh', program_behaves (Csem.semantics p) beh'
              /\ behavior_improves beh' beh.
```

but now `tp` is produced by a TMR pass whose protection crosses
selected function boundaries.

## Phase 7: Feed the design into downstream `Linear` / `Asm` plans

Only after the RTL story is stable should downstream plans be updated.

What will change downstream:

- the protected-location domain will expand to include internal
  argument/result interface locations
- call/return rules in downstream color systems will change
- downstream faulty simulations will need interprocedural protected
  invariants

This is why the interface-TMR plan should complete first.

## Architectural questions to settle explicitly

### 1. One pass or multiple passes?

Options:

1. extend the current RTL TMR pass directly
2. split into:
   - interface transformation
   - replication transformation
   - wrapper generation

Recommendation:

- code structure may be split for engineering reasons
- proof structure should initially target the composed transformation
- only later factor the proof if an intermediate reservation theorem for
  added channels turns out to be clean and reusable

### 2. How much of the checker should be interprocedural?

Options:

1. keep the checker entirely local and push interface consistency into
   the transformation proof
2. keep the checker mostly local but add small program-level side
   conditions
3. build a more explicitly interprocedural checker

Recommendation:

- start with option (1)
- move to option (2) only if a concrete boundary obligation cannot be
  discharged from the transformation/wrapper correctness proof
- avoid option (3) unless forced

### 3. Where do wrappers live?

Wrappers can be:

1. synthesized by the TMR pass itself
2. introduced by a separate wrapper-generation pass

Recommendation:

- whichever choice keeps proof structure cleanest in `RTLtmrproof.v`

### 4. What is the first acceptable restriction set?

Recommendation:

- direct internal non-address-taken calls only
- external and indirect calls remain White boundaries

This is the best first target for an implement-now plan.

## Validation checklist

Implementation should not be considered complete until all of the
following are rebuilt:

1. transformed RTL generation (`RTLtmr.v`) compiles
2. TMR soundness proof (`RTLtmrproof.v`) compiles
3. checker and soundness proof (`RTLcolor.v`, `RTLcolorcheck.v`)
   compile
4. faulty simulation proof (`RTLtolerant.v`) compiles
5. top-level theorem (`driver/Complements.v`) compiles
6. extraction / driver integration for the checker still works if
   signatures changed

## Exit criterion

This plan is complete when the repository has:

1. a concrete interface-TMR transformation at RTL
2. a soundness theorem for that transformation
3. a checker specification/soundness theorem that understands the new
   call/return discipline
4. a faulty backward simulation proof that tolerates faults under the
   new discipline
5. a rebuilt top-level RTL fault-tolerance theorem

Only after this should the `Linear` and `Asm` plans be specialized to
exploit the richer interface-TMR design.
