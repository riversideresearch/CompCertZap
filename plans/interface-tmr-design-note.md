# Plan: Extending TMR Across Function Boundaries

## Goal

Extend the current TMR design so that protected values can cross
internal function boundaries without being majority-voted at every call
and re-replicated after every return.

Concretely, this means:

- internal TMR-protected functions receive replicated arguments
- internal TMR-protected functions produce replicated results
- function boundaries cease to be uniformly White for protected flows

This plan is intentionally separate from any particular target theorem
(`RTL`, `Linear`, or `Asm`). Its purpose is to settle the transformed
calling convention and the invariants that later proof plans will rely
on.

## Motivation

The current prototype treats calls and returns as White boundaries:

- function arguments are passed unprotected
- function results are received unprotected
- smoves re-establish replicated state after calls when needed

This is simple, but it leaves call boundaries outside the protected
domain. If we eventually want stronger end-to-end protection, we need a
design in which protected values can flow through function interfaces.

## Scope

This plan concerns:

- transformed signatures for internal TMR-protected functions
- transformed call sites
- transformed returns
- boundary wrappers for external / non-TMR code
- the resulting agreement/separation story

This plan does **not** by itself prove a new fault-tolerance theorem at
any specific IR level. Instead, it produces a stable interface design
for later theorem plans to target.

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

## Boundary policy

Distinguish two kinds of call boundaries.

### 1. Internal TMR-to-TMR calls

These use the transformed interface:

- arguments are passed as triples
- results are written through hidden out-parameters as triples

No majority vote is inserted at the boundary merely to cross the call.

### 2. TMR-to-non-TMR boundaries

These include:

- calls to external functions
- calls to internal functions not transformed for interface TMR
- possible separately-compiled code

These boundaries require wrappers or adapters:

- when calling out from protected code, vote before crossing
- when receiving a result from unprotected code, treat it as White and
  re-replicate if needed

For a first version, keep these wrappers explicit and conservative.

## Hard design questions

### 1. Indirect calls and address-taken functions

This is the biggest semantic design question.

If a function can be called indirectly through a pointer, changing its
ABI is not transparent. Options:

1. restrict interface TMR to direct calls to internal, non-address-taken
   functions
2. generate wrapper entry points and ensure all escaped function values
   point to wrapper ABIs
3. redesign function-pointer handling globally

Recommendation for a first version:

- restrict to internal, direct calls to non-address-taken functions
- leave indirect/external calls on the current White-boundary policy

### 2. Which hidden-result shape to use

Options:

1. three separate output pointers
2. one pointer to a triple-aggregate object

Recommendation:

- start with three separate output pointers

Reason:

- simpler to express in IRs that already manipulate explicit arguments
- clearer separation reasoning than aggregate layout reasoning

### 3. What happens at `main`

`main` must keep the standard external ABI.

Recommendation:

- preserve the existing external signature of `main`
- if needed, generate one transformed internal entry point plus a thin
  wrapper using the standard ABI

## Invariants to settle

The interface design must state exactly which values are protected at
call boundaries.

### Agreement

For internal TMR-to-TMR calls:

- corresponding Red/Green/Blue arguments represent the same source
  value
- the three result channels written by a return represent the same
  source value

### Separation

For internal TMR-to-TMR calls:

- each channel is computed from only its corresponding color channel,
  except at explicit vote points
- hidden out-parameters for different colors remain separated

### White values

White remains necessary at external / wrapper boundaries and for other
intentionally unprotected operations. Interface TMR reduces the number
of White boundaries; it does not eliminate White from the language.

## Proposed phases

### Phase 0: Choose the transformed calling convention

Decide and document:

1. parameter tripling layout
2. hidden result out-parameter layout
3. which functions are eligible for transformed internal ABI
4. wrapper policy for non-eligible calls

**Deliverable**

A precise transformed-signature specification.

### Phase 1: Update the TMR transformation design

Determine how the TMR pass changes:

1. internal function definitions
2. direct internal call sites
3. returns
4. wrapper generation

Questions to settle:

- whether this remains one pass or becomes multiple coordinated passes
- where wrappers are inserted
- whether eligibility analysis is needed before replication

### Phase 2: Define interface-level agreement and separation

State the new correctness criteria at the first IR where the interface
transformation is expressed.

This should cover:

- entry-point parameter triples
- return-channel triples
- wrapper obligations

### Phase 3: Update TMR correctness theorem(s)

Refine the existing TMR pass soundness story so that it accounts for the
new interface transformation.

At minimum:

- protected calls preserve replicated flows
- protected returns preserve replicated flows
- wrappers correctly bridge protected and unprotected interfaces

### Phase 4: Feed the design into downstream checker/proof plans

Once the interface design is fixed, downstream plans (`Linear`, `Asm`,
etc.) can choose to target either:

- the current White-boundary TMR design, or
- the extended interface-TMR design

## Expected impact on later IR-level plans

If interface TMR is adopted, downstream fault-tolerance plans must
expand their protected-location domain:

- not only registers and local spill slots
- but also argument/result interface locations at internal calls

This is the main reason to keep this plan separate from any specific
`Linear` or `Asm` proof plan.

## Recommended implementation order

1. settle transformed calling convention and eligibility policy
2. settle wrapper policy for external / indirect calls
3. define interface-level agreement/separation specification
4. update the TMR transformation design
5. only then revise IR-specific checker/proof plans to exploit it

## Exit criterion

This plan is complete when there is a stable, written answer to:

1. which calls use the transformed ABI
2. how replicated results are returned
3. how wrappers mediate untransformed boundaries
4. what agreement/separation invariants later proofs should assume at
   call and return boundaries
