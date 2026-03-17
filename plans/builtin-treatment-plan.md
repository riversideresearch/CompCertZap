# Plan: Improving Builtin Treatment in TMR, Coloring, and Faulty RTL

## Goal

Relax the current all-or-nothing treatment of RTL builtins so that a
conservative safe subset can participate in redundancy the same way
safe `Iop` instructions do, while effectful, protocol-level, or
semantically fragile builtins remain on the current White-only path.

Scope assumption for this plan:

- the intended theorem/pipeline path is TMR without DMR
- `vote` and `check` are protocol builtins, not ordinary candidates for
  the new safe-builtin bucket
- `check` is treated as DMR-specific and is therefore out of scope for
  the TMR fault-tolerance theorem, except that it should remain
  conservatively non-safe/non-faultable if it is classified at all

Concretely:

- replicate a safe subset of builtins instead of always voting inputs,
  executing once in White, and copying the result to shadows
- allow faults on that same safe subset in the faulty RTL semantics
- keep unsafe builtins White-only and non-faultable
- make the TMR pass, coloring rules/checker/oracle, and tolerant proof
  agree on the same split

## Current baseline

Today all `Ibuiltin` instructions are treated conservatively.

- In `backend/RTLtmr.v`, only non-protected `Iop` instructions are
  triplicated.
- Other instructions, including all builtins, first majority-vote
  their arguments, execute once in the regular world, and then copy any
  result to the two shadow worlds.
- In `backend/RTLfault.v`, `zap_allowed` is `False` for all
  `Ibuiltin`s.
- In `backend/RTLcolor.v`, `backend/RTLcolorcheck.v`, and
  `backend/RTLinfercolor.ml`, every builtin other than the existing
  special cases (`smove`, `vote`) is forced to White.

This is sound but stronger than necessary.

## Terminology

The existing name `is_protected` is about operations that must not be
replicated. For builtins, the useful distinction is instead:

- builtins that may be replicated and faulted
- builtins that must remain White-only

The new names should reflect that directly.

## Core design choice

Introduce one shared builtin classification and reuse it in all places
that care about this distinction:

1. TMR transformation
2. faulty RTL `zap_allowed`
3. color specification
4. color checker
5. color inference oracle

Recommended interface:

- `builtin_can_replicate : external_function -> bool`
- `builtin_can_fault : external_function -> bool`

For the first implementation, these should be definitionally aligned,
or one should be defined directly in terms of the other.

## The real semantic cut

The relevant criterion is not merely "syntactically an `EF_builtin`"
and not even just "recognized by `lookup_builtin_function`".

The builtin must be safe under the actual fault model in
`backend/RTLfault.v`:

- `maybe_zap` can replace a register value with any `val_compat` value,
  not only `Vundef`
- after such a corruption, a replicated builtin must still be able to
  execute without getting stuck
- the tolerant proof therefore needs a semantic monotonicity argument
  strong enough for faulted inputs, not just an ad hoc syntactic
  whitelist

In practice, the first-cut whitelist should be chosen so that a faulted
execution of the builtin still returns `Some ...` on corrupted but
type-compatible inputs.

The `_t` vs `_p` helper split in `Builtins0.v` is a good first
approximation of this boundary:

- `_t` helpers are the intended "safe" class
- `_p` helpers, `BI_unreachable`, and similar fragile cases stay
  White-only

## Why recognized builtins are still the right outer cut

The right semantic hook is not just "any `EF_builtin`".

- In `common/Events.v`, recognized builtins are routed through
  `known_builtin_sem`.
- `known_builtin_sem` gives exactly the extcall shape wanted for the
  safe class: `E0` trace and unchanged memory.
- Unrecognized `EF_builtin name sg` values fall back to general
  external-call semantics and must not be treated as pure
  compiler-internal computations.

So the first cut should be:

1. require `lookup_builtin_function name sg = Some bf`
2. reject protocol builtins from this fork
3. reject builtin cases whose semantics can fail on faulted inputs

## Recommended first-cut classification

### Replicable / faultable builtins

Allow only builtins satisfying all of the following:

1. They are recognized by `lookup_builtin_function`.
2. They are not fork-specific protocol builtins:
   `smove`, `vote`, `check`.
3. Their semantic implementation belongs to the "total enough under
   faulted inputs" class intended by the `_t` helper family.

Concrete initial whitelist:

#### Standard builtins

- `BI_fabs`, `BI_fabsf`, `BI_fsqrt`
- `BI_negl`
- `BI_addl`, `BI_subl`, `BI_mull`
- `BI_i16_bswap`, `BI_i32_bswap`, `BI_i64_bswap`
- `BI_i64_umulh`, `BI_i64_smulh`
- `BI_i64_shl`, `BI_i64_shr`, `BI_i64_sar`
- `BI_i64_stod`, `BI_i64_utod`, `BI_i64_stof`, `BI_i64_utof`

#### Platform builtins

- x86: `BI_fmin`, `BI_fmax`

If RISC-V or another backend has platform builtins in scope for the RTL
being proved here, classify them explicitly rather than assuming they
follow the x86 list.

### White-only builtins

Keep the following conservative in the first pass:

1. Unknown `EF_builtin name sg` cases.
2. All protocol builtins from this fork:
   `smove`, `vote`, `check`.
3. Partial or UB-sensitive known builtins, including:
   - `BI_select`
   - `BI_unreachable`
   - signed/unsigned div/mod helpers
   - float-to-int64 conversion helpers that can return `None`

Here `vote` and `check` are excluded for different reasons:

- `vote` is part of the TMR protocol and already has dedicated
  treatment in the transform, coloring rules, and tolerant proof
- `check` is part of the DMR protocol and is not expected to appear in
  the TMR theorem path, because this plan assumes DMR and TMR are not
  used together

## Where to define the classification

The canonical place should be `common/Builtins.v`.

Reasons:

- the classification is fundamentally about `builtin_function`,
  `lookup_builtin_function`, and builtin semantics, all of which live
  there already
- the proof-critical lemmas also live at the builtin-function layer
  (`builtin_function_sem_lessdef`) and are then lifted in
  `common/Events.v`
- TMR, faulty RTL, coloring, checker, and oracle are all consumers of
  the policy, not the natural home of the policy
- `backend/RTL.v` already contains some builtin recognizers, but that
  reflects historical convenience rather than a good module boundary

As part of this change, the existing protocol-builtin recognizers that
currently live in `backend/RTL.v` should move to `common/Builtins.v`
rather than serving as precedent for adding more builtin
classification there.

## Existing lemma support and the real proof risk

There is already a generic lemma:

- `builtin_function_sem_lessdef` in `common/Builtins.v`

and its `known_builtin_sem` wrapper in `common/Events.v`.

That reduces risk, but it does not eliminate the main proof question.
The proof work still needs to confirm that the existing lemma has the
right orientation and strength for the new faulted-builtin case in
`RTLtolerant.v`, where inputs come from the `val_compat`-based fault
model.

So the real risk is not "there is no supporting lemma", but:

- the existing lessdef lemmas may be close rather than sufficient
- the exact property needed by the tolerant proof must be validated
  early, before investing heavily in TMR/code-shape work

## Implementation order

The implementation should proceed in this order.

### Phase 1: Add shared builtin classification

#### Files

- primarily `common/Builtins.v`
- possibly `backend/Builtins2.v`
- plus import repair in backend consumers

#### Actions

1. Move the existing protocol-builtin recognizers
   (`is_green_smove_builtin*`, `is_blue_smove_builtin*`,
   `is_vote_builtin*`) out of `backend/RTL.v` and into
   `common/Builtins.v`.
2. Define a predicate/boolean for protocol builtins if those moved
   predicates are not enough, especially for handling `check`
   explicitly.
3. Define `builtin_can_replicate_bf : builtin_function -> bool`.
4. Define `builtin_can_replicate : external_function -> bool` by
   recognizing `EF_builtin name sg`, using `lookup_builtin_function`,
   and dispatching to the builtin-function-level classifier.
5. Define `builtin_can_fault` and keep it aligned with
   `builtin_can_replicate` for the first implementation.
6. Add propositional forms and reflection lemmas alongside the
   builtin definitions, then update backend users to import them from
   there.

#### Exit criteria

- there is one obvious classification point
- TMR, faulty semantics, coloring, checker, and oracle can all consume
  it directly from `common/Builtins.v`

### Phase 2: Validate the proof-critical semantic property early

#### Files

- primarily `common/Builtins.v`
- possibly `common/Events.v`
- supporting proof experimentation in `backend/RTLtolerant.v`

#### Actions

1. State explicitly what the tolerant proof needs for the safe builtin
   class.
2. Check whether the existing `builtin_function_sem_lessdef` and
   `known_builtin_sem_lessdef` lemmas are sufficient as-is.
3. If they are not, prove the smallest strengthening/adaptation needed
   at the `builtin_function` layer, then lift it through
   `known_builtin_sem`.

#### Design constraint

The property should be formulated against the actual fault model,
not just against `Vundef` in isolation.

#### Exit criteria

- the semantic support for the new faulted-builtin case is proved or
  clearly characterized
- the main technical risk is retired before changing multiple passes

### Phase 3: Update the TMR pass, spec, and proof

#### Files

- `backend/RTLtmr.v`
- `backend/RTLtmrspec.v`
- `backend/RTLtmrproof.v`

#### Actions

1. Extend `transf_instr` so that replicable builtins are treated like
   safe `Iop`s:
   - emit one builtin in the green world
   - emit one builtin in the blue world
   - keep the original builtin in the regular world
2. Keep White-only builtins on the current
   "vote arguments, run once, copy result" path.
3. Preserve the dedicated special handling of `smove` and `vote`.
   `check` is outside the intended TMR path for this plan; if it is
   still classified, keep it conservative and do not treat it as a safe
   replicated builtin.
4. Use the existing `AST.map_builtin_arg` and `map_builtin_res`
   helpers instead of introducing duplicate remapping utilities.
5. Add a new `match_Ibuiltin_safe`-style case to `RTLtmrspec.v`.

#### Proof work

1. Generalize the existing `Iop` proof pattern in `RTLtmrproof.v`.
2. Prove the builtin-argument remapping facts needed for shadow
   execution.
3. Reuse known builtin purity/determinism where possible.

#### Exit criteria

- transformed code shape reflects the new split
- `backend/RTLtmrspec.vo` and `backend/RTLtmrproof.vo` rebuild

### Phase 4: Update color spec, checker, and inference oracle

#### Files

- `backend/RTLcolor.v`
- `backend/RTLcolorcheck.v`
- `backend/RTLinfercolor.ml`

#### Actions

1. Add a `wc_Ibuiltin_safe` rule analogous to `wc_Iop_safe`.
2. Keep `smove` and `vote` on their current dedicated rules.
3. Keep non-replicable builtins, including `check`, on the current
   generic White-only rule.
4. Mirror the split in `check_col_instr`.
5. Update `RTLinfercolor.ml` so the oracle assigns basic colors to
   safe builtins instead of forcing them to White.

#### Design intent

If the TMR pass can replicate a builtin but the coloring checker or
oracle still forces it to White, the system becomes internally
inconsistent. These three components must move together.

#### Exit criteria

- checker accepts replicated safe builtins
- checker remains conservative for all other builtins
- oracle produces colorings compatible with the new spec
- `backend/RTLcolor.vo` and `backend/RTLcolorcheck.vo` rebuild

### Phase 5: Relax faulty RTL and finish the tolerant proof

#### Files

- `backend/RTLfault.v`
- `backend/RTLtolerant.v`

#### Actions

1. Change `zap_allowed` so that `Ibuiltin ef ...` is faultable exactly
   when `builtin_can_fault ef`.
2. Keep protocol and White-only builtins non-faultable.
3. Add the new replicated-safe-builtin proof case to
   `RTLtolerant.v`.
4. Split the `exec_Ibuiltin` reasoning in `RTLtolerant.v` into:
   - safe replicated builtin case
   - protocol builtin cases (`smove`, `vote`)
   - other White-only builtin case
5. Audit helper lemmas and case splits that currently rely on the
   blanket "all generic builtins are conservative" discipline.

For `check`, no new TMR-side proof case should be required under the
intended usage assumption, because `check` is DMR-specific and is not
expected to appear when establishing the TMR faulty-refinement theorem.

#### Exit criteria

- faultable builtins match the TMR/coloring classification
- `backend/RTLtolerant.vo` rebuilds

## Expected proof difficulty

### Low risk

- shared classification definitions
- color spec/checker updates
- color inference oracle update
- `zap_allowed` change itself

### Medium risk

- TMR transformation and matching-spec update
- TMR proof case for replicated safe builtins

### High risk

- finishing the new faulted-builtin case in `RTLtolerant.v`
- validating that the semantic monotonicity lemma used there is exactly
  strong enough for the `val_compat`-based fault model

## Approximate file touch list

- `common/Builtins.v`
- `common/Events.v`
- `backend/RTLtmr.v`
- `backend/RTLtmrspec.v`
- `backend/RTLtmrproof.v`
- `backend/RTLcolor.v`
- `backend/RTLcolorcheck.v`
- `backend/RTLinfercolor.ml`
- `backend/RTLfault.v`
- `backend/RTLtolerant.v`

## Success criteria

The plan is complete when all of the following hold:

1. There is a single shared builtin classification consumed by TMR,
   faulty semantics, coloring, checker, and oracle.
2. Safe builtins are triplicated by TMR.
3. The color system accepts those replicated builtins with basic colors.
4. Faulty RTL allows faults on exactly that safe builtin class.
5. The tolerant proof continues to establish the intended refinement.

## Follow-up: Decide whether to refactor `is_protected`

## Files

- `backend/RTL.v`
- any downstream files touched during proof repair

## Recommendation

Do not fold builtin classification into `is_protected`.

Reasons:

- `is_protected` is currently about `operation`, not
  `external_function`.
- the name is already semantically overloaded
- builtins need a separate classification anyway because protocol
  builtins are pure but still special

If desired, a later cleanup can rename the `operation` concept to
something like:

- `op_must_run_white`
- `op_cannot_replicate`

That should be treated as a follow-up refactor, not part of the first
semantic change.

Separately, this builtin-policy patch set is a good opportunity to
remove the existing protocol-builtin recognizers from `backend/RTL.v`
entirely, since they belong with the builtin definitions and should
not remain duplicated across modules.

## Open questions

## 1. Exact first-pass whitelist

The first implementation needs an explicit list of recognized builtins
that are treated as safe.

Recommended approach:

- start with total standard/platform builtins only
- exclude any builtin whose semantics returns `None`
- exclude all replicate builtins from this fork

This is simple to audit and explain.

## 2. Whether `check` builtins should remain special forever

Even though `check` builtins are pure stubs at RTL, they are part of the
fault-tolerance protocol and should stay out of the generic safe-builtin
bucket unless there is a proof-driven reason to merge them later.

For this patch set, the practical stance is simpler:

- treat `check` as DMR-only
- assume DMR and TMR are not used together when reasoning about the TMR
  theorem path
- avoid spending proof effort on making `check` fit the new TMR-side
  builtin policy unless mixed DMR+TMR support becomes a real goal

## 3. Loads

This plan only addresses builtins. Loads have a similar issue in the
current model, but they require a separate design because they are not
builtins and interact with memory directly.

Keep that out of scope for the first patch set.

## Recommended implementation order

1. Add shared builtin classification.
2. Validate the proof-critical semantic property early.
3. Update TMR transform, spec, and proof.
4. Update color spec/checker/oracle.
5. Update faulty semantics and the tolerant proof.
6. Reassess naming cleanup only after the semantic change works.

## Validation

After each phase, rebuild the smallest affected proof target first, then
the full chain.

Recommended checks:

- `make backend/RTLtmr.vo`
- `make backend/RTLtmrproof.vo`
- `make backend/RTLcolor.vo`
- `make backend/RTLcolorcheck.vo`
- `make backend/RTLtolerant.vo`
- `make driver/Complements.vo`
- `make check-admitted`

## Deliverable

A consistent builtin policy in which:

- ordinary safe known builtins are replicated and faultable
- protocol / partial / unknown builtins remain White-only
- TMR transformation, color checking, and faulty RTL all agree on the
  classification
