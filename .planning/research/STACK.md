# Technology Stack

**Project:** Improved Builtin Treatment in TMR
**Researched:** 2026-03-14

## Recommended Stack

This is a Coq proof engineering project within an existing codebase (CompCert 3.17 fork). The "stack" is not about choosing frameworks but about choosing Coq representation patterns, proof techniques, and module organization for the new builtin classification system.

### Core Representation: Boolean Function on `builtin_function`

| Technology | Version | Purpose | Why |
|------------|---------|---------|-----|
| Boolean function `builtin_can_replicate_bf` | N/A | Primary classification of `builtin_function` values | Matches the established `is_protectedb` pattern already used for `operation` classification in this codebase. Boolean functions are directly computable in extracted OCaml, consumable by the checker, and amenable to reflection. |
| Inductive predicate (propositional form) | N/A | NOT recommended for the primary classification | The codebase already has a cautionary example: `is_vote_builtin`, `is_green_smove_builtin`, etc. are inductive predicates with ~30 lines each for definition + boolean + reflection lemma. This triple is tedious and error-prone. The `is_protectedb`/`is_protected` pair shows the same pattern. For the new classification, start with the boolean and derive the propositional form only if needed. |
| Wrapper `builtin_can_replicate` on `external_function` | N/A | Bridge from `external_function` (used in instructions) to the `builtin_function`-level classifier | Necessary because `Ibuiltin` carries `external_function`, not `builtin_function`. Must pattern-match on `EF_builtin name sg`, call `lookup_builtin_function`, then dispatch. |

**Confidence:** HIGH -- directly grounded in existing codebase patterns (`is_protectedb`, `is_vote_builtinb`).

### Reflection Lemma Structure

| Technology | Version | Purpose | Why |
|------------|---------|---------|-----|
| `reflect` from Coq stdlib | Coq 8.x | Bidirectional bool/Prop bridge | Standard Coq idiom. The codebase already uses `reflect` extensively (see `is_protectedb_spec`, `is_vote_builtinb_spec`, `eqb_spec` in `RTLcolor.v`). |
| Single reflection lemma per boolean | N/A | `builtin_can_replicate_bf_spec : forall b, reflect (builtin_can_replicate_prop b) (builtin_can_replicate_bf b)` | Proof by `destruct b; simpl; try left; try right; try constructor; auto`. This is the exact proof shape used for `is_protectedb_spec`. |

**Confidence:** HIGH -- the `reflect` pattern is used identically in at least 5 places in the existing backend code.

### Semantic Property Lemmas

| Technology | Version | Purpose | Why |
|------------|---------|---------|-----|
| `builtin_function_sem_lessdef` | Existing | Core semantic monotonicity for safe builtins under `Val.lessdef` | Already proved in `common/Builtins.v`. The `_t` (total) builtin constructors guarantee `Some` results on well-typed inputs, and `Val.lessdef` is the standard CompCert value refinement. |
| New `builtin_sem_val_compat` lemma | To build | Semantic monotonicity for safe builtins under `val_compat` | This is the key proof obligation. `val_compat` is strictly weaker than `Val.lessdef` (it allows `Vint i` to be compatible with `Vint j` for any `i, j`), so the existing `lessdef` lemma is NOT directly sufficient. A new lemma is needed. See detailed analysis below. |

**Confidence:** MEDIUM -- the existing `lessdef` lemma structure is clear, but the `val_compat`-level property requires new proof work whose difficulty depends on each builtin's semantics.

### Module Organization

| Technology | Version | Purpose | Why |
|------------|---------|---------|-----|
| Define classification in `common/Builtins.v` | N/A | Single source of truth | `builtin_function`, `lookup_builtin_function`, and `builtin_function_sem` all live there. Consumers in the backend import from this module. This is where `builtin_function_sem_lessdef` already lives. |
| Move protocol recognizers from `backend/RTL.v` | N/A | Consolidate builtin knowledge | `is_vote_builtin`, `is_green_smove_builtin`, `is_blue_smove_builtin` currently live in `backend/RTL.v` (lines 1063-1265) but are about `external_function` matching specific builtin names/signatures. They belong with the builtin definitions, not with RTL instruction semantics. |
| Keep `is_protected` in `backend/RTL.v` | N/A | Orthogonal concern | `is_protected` classifies `operation` values, not `external_function`. These are different types serving different roles. Do not conflate them. |

**Confidence:** HIGH -- follows directly from the existing module structure and the PROJECT.md design decisions.

## Detailed Technical Analysis

### Why Boolean Function, Not Inductive

The codebase has two competing patterns for classifying instruction-level entities:

**Pattern A (inductive + boolean + reflect):** Used for `is_protected`, `is_vote_builtin`, `is_green_smove_builtin`, `is_blue_smove_builtin`. Each requires:
1. An `Inductive` with one constructor per case (~15 lines)
2. A `Definition` boolean function (~15 lines)
3. A `Lemma ... : reflect ...` (~15 lines)

**Pattern B (boolean primary):** Used implicitly by the checker (`RTLcolorcheck.v`) which only ever calls the boolean forms.

For `builtin_can_replicate_bf`, Pattern B (boolean primary) is the right choice because:

1. **The checker is the primary consumer.** `RTLcolorcheck.v` calls `is_protectedb` directly, never `is_protected`. The new classifier will be consumed the same way.
2. **The TMR pass needs a computable decision.** `transf_instr` in `RTLtmr.v` branches on `is_protectedb op`. The new code will branch on `builtin_can_replicate ef`.
3. **The coloring oracle (OCaml) needs a boolean.** `RTLinfercolor.ml` will call the extracted boolean.
4. **The propositional form is only needed in proofs** that reason about the coloring spec (`wc_Ibuiltin_safe`) and the tolerant simulation. These proofs can use `destruct (builtin_can_replicate_bf b) eqn:H` directly.

If a propositional form proves necessary later (e.g., for pattern matching in proof scripts), it can be derived mechanically from the boolean. The existing `is_protectedb_spec` reflection lemma proves this is straightforward.

### The `val_compat` vs `Val.lessdef` Gap

This is the most important technical point in the stack decision.

**What `val_compat` means (from `RTLfault.v`):**
```coq
Inductive val_compat : val -> val -> Prop :=
| val_compat_undef : forall v, val_compat Vundef v
| val_compat_int : forall i j, val_compat (Vint i) (Vint j)
| val_compat_long : forall i j, val_compat (Vlong i) (Vlong j)
| val_compat_float : forall x y, val_compat (Vfloat x) (Vfloat y)
| val_compat_single : forall x y, val_compat (Vsingle x) (Vsingle y)
| val_compat_ptr : forall b1 b2 ofs1 ofs2, val_compat (Vptr b1 ofs1) (Vptr b2 ofs2).
```

**What `Val.lessdef` means:**
`Val.lessdef v1 v2` requires `v1 = v2` or `v1 = Vundef`.

**The gap:** Under `val_compat`, a faulted `Vint 42` is compatible with `Vint 0`. Under `Val.lessdef`, it is not. The existing `builtin_function_sem_lessdef` says: if the builtin succeeds on `vargs`, it also succeeds on any `vargs'` that are `Val.lessdef`-related, and the results are `Val.lessdef`-related. This does NOT cover the fault model's needs.

**What the tolerant proof actually needs:** For a safe replicated builtin with faulted inputs, the proof needs to show that the builtin still produces `Some vres'` (it does not get stuck), and that the result is `val_compat`-related to the unfaulted result. The key property is:

```
builtin_function_sem b vargs = Some vres ->
Forall2 val_compat vargs vargs' ->
exists vres', builtin_function_sem b vargs' = Some vres'
              /\ val_compat vres vres'.
```

**Why this is provable for `_t` (total) builtins:** The `_t` constructors (`mkbuiltin_n1t`, `mkbuiltin_n2t`, `mkbuiltin_v1t`, `mkbuiltin_v2t`, `mkbuiltin_v3t`) have a specific structure: they use `proj_num` to extract numeric components and `inj_num` to inject results. When inputs are `val_compat`-related:

- `proj_num Tint Vundef (Vint i) k` returns `k i`
- `proj_num Tint Vundef (Vint j) k` returns `k j`
- Both produce `Some (inj_num tres (...))` -- they do not get stuck
- The results are `val_compat` because they have the same constructor

For `_p` (partial) builtins, this fails: `Val.divls (Vlong 1) (Vlong 0) = None`, so a faulted divisor of 0 would cause the builtin to get stuck. This confirms the `_t`/`_p` boundary in the plan.

**The `mkbuiltin_v1t`/`mkbuiltin_v2t` subtlety:** `BI_addl` uses `mkbuiltin_v2t` with `Val.addl`, not `mkbuiltin_n2t`. `Val.addl` handles pointer arithmetic:
```
Val.addl (Vlong i) (Vlong j) = Vlong (Int64.add i j)
Val.addl (Vptr b ofs) (Vlong j) = Vptr b (Ptrofs.add ofs (Ptrofs.of_int64 j))
```

Under `val_compat`, if `Vlong i` is faulted to `Vlong j`, `Val.addl` still returns a `Vlong`, so `val_compat` holds. But if `Vptr b1 ofs1` is faulted to `Vptr b2 ofs2`, the result is `Vptr b2 (...)` which is still a `Vptr`, so `val_compat` also holds. The critical check is that the function never returns `None` on type-preserving inputs. For `Val.addl`, this is true.

For `Val.subl`, there is a subtlety: `Val.subl (Vptr b1 ofs1) (Vptr b2 ofs2)` checks `eq_block b1 b2` and returns `None` if blocks differ. Under `val_compat`, faulted pointers can point to different blocks, so `Val.subl` is NOT safe. But `BI_subl` uses `mkbuiltin_v2t` with `Val.subl`, and `Val.subl` with two `Vptr` args from different blocks returns `Vundef` (not `None`). Re-checking... Actually `Val.subl` is a total function (`val -> val -> val`), wrapped by `mkbuiltin_v2t` which always returns `Some`. So it IS safe at the `option val` level -- it just might return `Vundef`. And `val_compat Vundef (Vundef)` holds trivially. So `BI_subl` is fine.

**Recommendation:** The `val_compat` monotonicity lemma should be proved per-builtin-constructor-family:

1. `mkbuiltin_n1t`/`mkbuiltin_n2t`/`mkbuiltin_n3t`: Prove once generically. These use `proj_num`/`inj_num` which guarantee `Some` on same-constructor inputs.
2. `mkbuiltin_v1t`/`mkbuiltin_v2t`/`mkbuiltin_v3t`: Case-by-case, because the wrapped function might have pointer-sensitivity. But since these are total (`val -> ... -> val`), the wrapper always returns `Some`, so the "does not get stuck" part is automatic.
3. `mkbuiltin_v1p`/`mkbuiltin_v2p`/`mkbuiltin_n1p`/`mkbuiltin_n2p`: EXCLUDED from the safe class. These can return `None`.

**Confidence:** MEDIUM -- the analysis is sound but the per-builtin verification for `mkbuiltin_vNt` cases needs actual Coq proof work. The risk is moderate because the argument structure is uniform.

### The `_t` vs `_p` Classification Implementation

The classification maps directly onto the `standard_builtin` type:

```coq
Definition standard_builtin_can_replicate (b: standard_builtin) : bool :=
  match b with
  | BI_fabs | BI_fabsf | BI_fsqrt => true
  | BI_negl => true
  | BI_addl | BI_subl | BI_mull => true
  | BI_i16_bswap | BI_i32_bswap | BI_i64_bswap => true
  | BI_i64_umulh | BI_i64_smulh => true
  | BI_i64_shl | BI_i64_shr | BI_i64_sar => true
  | BI_i64_stod | BI_i64_utod | BI_i64_stof | BI_i64_utof => true
  (* Partial / UB-sensitive -- excluded *)
  | BI_select _ => false   (* pointer-sensitive conditional *)
  | BI_unreachable => false (* always None *)
  | BI_i64_sdiv | BI_i64_udiv | BI_i64_smod | BI_i64_umod => false (* division by zero *)
  | BI_i64_dtos | BI_i64_dtou => false  (* NaN/overflow -> None *)
  end.
```

For platform builtins (x86):
```coq
Definition platform_builtin_can_replicate (b: platform_builtin) : bool :=
  match b with
  | BI_fmin | BI_fmax => true  (* mkbuiltin_n2t, always total *)
  end.
```

For replicate builtins (protocol):
```coq
Definition replicate_builtin_can_replicate (b: replicate_builtin) : bool :=
  false.  (* Protocol builtins have dedicated handling *)
```

The top-level:
```coq
Definition builtin_can_replicate_bf (b: builtin_function) : bool :=
  match b with
  | BI_standard b => standard_builtin_can_replicate b
  | BI_platform b => platform_builtin_can_replicate b
  | BI_replicate b => false
  end.
```

The `external_function` wrapper:
```coq
Definition builtin_can_replicate (ef: external_function) : bool :=
  match ef with
  | EF_builtin name sg =>
      match lookup_builtin_function name sg with
      | Some bf => builtin_can_replicate_bf bf
      | None => false
      end
  | _ => false
  end.
```

**Confidence:** HIGH -- directly enumerates the existing `standard_builtin` and `platform_builtin` types with clear semantics-driven rationale for each case.

### Architecture Portability

| Architecture | Platform Builtins | Classification | Notes |
|-------------|-------------------|----------------|-------|
| x86-64 | `BI_fmin`, `BI_fmax` | Both safe (total `mkbuiltin_n2t`) | Only platform with non-empty `platform_builtin` |
| RISC-V | (empty type) | N/A | `match b with end` exhaustively handles the empty type |
| aarch64 | (empty type) | N/A | Same as RISC-V |
| ARM | (empty type) | N/A | Same as RISC-V |
| PowerPC | (empty type) | N/A | Same as RISC-V |

Because `platform_builtin_can_replicate` is defined per-architecture in `Builtins1.v`, the empty-type architectures get `match b with end` which is vacuously total and correct. No conditional compilation or architecture parameterization is needed.

**Confidence:** HIGH -- verified by reading all 5 architecture `Builtins1.v` files.

### Proof Technique for the Tolerant Simulation

The existing proof pattern in `RTLtolerant.v` for the safe `Iop` case uses `eval_operation_val_compat` (proved in `RTLfault.v`). This lemma takes:

1. `~ is_protected op`
2. `rs_compat rs1 rs2` (pointwise `val_compat`)
3. Both register maps successfully evaluate the operation

And concludes `val_compat v v'` between the results.

The analogous lemma for safe builtins would be:

```
builtin_sem_val_compat :
  forall b vargs1 vargs2 vres1 vres2,
  builtin_can_replicate_bf b = true ->
  Forall2 val_compat vargs1 vargs2 ->
  builtin_function_sem b vargs1 = Some vres1 ->
  builtin_function_sem b vargs2 = Some vres2 ->
  val_compat vres1 vres2.
```

This follows the same shape as `eval_operation_val_compat` and can be proved by:
1. Case analysis on `b`
2. For each case, unfolding the `builtin_function_sem` definition
3. Inverting the `Forall2 val_compat` hypothesis to get per-argument `val_compat`
4. Using the structure of `proj_num`/`inj_num` or the specific `Val.*` function to show the results have matching constructors

The proof should additionally establish totality under `val_compat` inputs:

```
builtin_sem_val_compat_total :
  forall b vargs1 vargs2 vres1,
  builtin_can_replicate_bf b = true ->
  Forall2 val_compat vargs1 vargs2 ->
  builtin_function_sem b vargs1 = Some vres1 ->
  exists vres2, builtin_function_sem b vargs2 = Some vres2.
```

This is the "does not get stuck" half. For `_t` builtins it follows because `proj_num` returns `Vundef` on wrong-constructor inputs but returns a computed value on same-constructor inputs, and `val_compat` guarantees same-constructor.

**Confidence:** MEDIUM -- the proof strategy is clear and the structure matches existing code, but the per-case verification has not been done in Coq.

## Alternatives Considered

| Category | Recommended | Alternative | Why Not |
|----------|-------------|-------------|---------|
| Primary representation | Boolean function | Inductive predicate | Boolean is directly computable, avoids boilerplate, matches `is_protectedb` pattern. Inductive requires 3x the code for definition + boolean + reflection. |
| Classification granularity | Per-`builtin_function` variant match | Typeclass on `builtin_sem` | Typeclass would require annotating each builtin's `builtin_sem` with totality/purity evidence. The `builtin_sem` record already has `bs_inject` but NOT totality. Adding a typeclass would require changing the `builtin_sem` record or creating a separate typeclass hierarchy. Too invasive for the existing code. |
| Classification location | `common/Builtins.v` | `backend/RTLfault.v` or `backend/RTL.v` | The classifier is about `builtin_function` and its semantics, both defined in `common/Builtins.v`. Putting it in a backend file would create an import cycle or a misplaced dependency. |
| `val_compat` lemma location | `common/Builtins.v` alongside `builtin_function_sem_lessdef` | `backend/RTLfault.v` | Putting it in `Builtins.v` requires importing `val_compat` from the backend, creating a circular dependency. The lemma should go in `backend/RTLfault.v` where `val_compat` is defined, or in a new bridge file. |
| Alignment of `can_replicate` and `can_fault` | Same boolean | Independent booleans | For the first implementation, they should be definitionally equal (`builtin_can_fault = builtin_can_replicate`). This simplifies all proofs and can be relaxed later if a use case for divergence arises. |
| Protocol builtin handling | Keep existing `is_vote_builtin` etc. in the moved location | Fold into `builtin_can_replicate` | Protocol builtins already have dedicated coloring rules (`wc_Ibuiltin_smove_green`, `wc_Ibuiltin_vote`) and TMR handling. They are not "generic" builtins -- they are part of the fault-tolerance protocol. Folding them into a generic classifier would obscure the architecture. |

## Installation / Setup

No new dependencies. All work is within the existing Coq/OCaml codebase.

```bash
# After making changes, verify:
make backend/RTLfault.vo       # val_compat lemma
make common/Builtins.vo        # classification definitions
make backend/RTLcolor.vo       # coloring spec
make backend/RTLcolorcheck.vo  # checker
make backend/RTLtmr.vo         # TMR pass
make backend/RTLtmrproof.vo    # TMR proof
make backend/RTLtolerant.vo    # tolerant proof (the hard one)
make driver/Complements.vo     # top-level theorem
```

## Key Technical Decisions Summary

| Decision | Choice | Rationale | Confidence |
|----------|--------|-----------|------------|
| Representation | Boolean function on `builtin_function` | Matches `is_protectedb` pattern; directly computable; avoids inductive boilerplate | HIGH |
| Reflection | `reflect` lemma proved by `destruct b` | Standard codebase pattern, 5+ existing examples | HIGH |
| `val_compat` property | New lemma, case analysis per builtin | Existing `lessdef` lemma insufficient; `val_compat` is strictly weaker | MEDIUM |
| `val_compat` lemma location | `backend/RTLfault.v` or new bridge file | Cannot go in `common/Builtins.v` due to import direction | HIGH |
| Safe builtin boundary | `_t` constructors only; exclude `_p`, `BI_select`, `BI_unreachable` | `_t` are total on same-constructor inputs; `_p` can return `None` on faulted inputs | HIGH |
| `can_replicate` = `can_fault` | Identical for first implementation | Simplifies proofs; no known use case for divergence | HIGH |
| Protocol builtins | Excluded from generic classification; retain dedicated handling | Architecturally distinct; already have specialized coloring/TMR rules | HIGH |
| Module location | `common/Builtins.v` for classification; backend for `val_compat` lemma | Follows existing import graph direction | HIGH |

## Sources

All findings are grounded in direct reading of the CompCert codebase files listed below. No external sources were needed because this is an internal Coq proof engineering project.

- `common/Builtins.v` -- `builtin_function` type, `builtin_function_sem`, `builtin_function_sem_lessdef`
- `common/Builtins0.v` -- `builtin_sem` record, `mkbuiltin_*` constructors, `_t`/`_p` naming convention
- `common/Events.v` -- `known_builtin_sem`, `builtin_or_external_sem`, `extcall_properties`
- `backend/Builtins2.v` -- `replicate_builtin`, `vote_type`, `VoteSemantics`
- `backend/RTL.v` -- `is_protected`/`is_protectedb`, `is_vote_builtin`, `is_green_smove_builtin`, `is_blue_smove_builtin`
- `backend/RTLcolor.v` -- `wc_instruction` rules: `wc_Iop_safe`, `wc_Iop_protected`, `wc_Ibuiltin`, `wc_Ibuiltin_smove_green`, `wc_Ibuiltin_vote`
- `backend/RTLcolorcheck.v` -- boolean color checker using `is_protectedb`
- `backend/RTLfault.v` -- `val_compat`, `zap_allowed`, `maybe_zap`, `eval_operation_val_compat`
- `backend/RTLtolerant.v` -- usage of `eval_operation_val_compat` in tolerant simulation
- `backend/RTLtmr.v` -- `transf_instr` branching on `is_protectedb`
- `backend/RTLtmrspec.v` -- `match_Iop_safe`, `match_Iop_protected`
- `backend/RTLtmrproof.v` -- proof patterns for safe/protected Iop cases
- `x86/Builtins1.v` -- platform builtins: `BI_fmin`, `BI_fmax` (total, `mkbuiltin_n2t`)
- `riscV/Builtins1.v`, `aarch64/Builtins1.v` -- empty platform builtin types
- `plans/builtin-treatment-plan.md` -- detailed implementation plan
- `.planning/PROJECT.md` -- project requirements and constraints
