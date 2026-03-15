# Feature Landscape: Builtin Classification for TMR Replication and Faulting

**Domain:** Formal verification -- builtin treatment in a fault-tolerant CompCert fork
**Researched:** 2026-03-14

## Inventory of All Builtins

Before classifying, here is the complete inventory of builtins in the codebase, organized by source file and construction method. The `_t` vs `_p` suffix on the helper that constructs each builtin's semantics is the first-order signal of totality.

### Standard Builtins (`common/Builtins0.v`)

| Builtin | Constructor | Total? | Semantics | Pointer-involving? |
|---------|-------------|--------|-----------|-------------------|
| `BI_fabs` | `mkbuiltin_n1t` | Yes | `Float.abs` | No |
| `BI_fabsf` | `mkbuiltin_n1t` | Yes | `Float32.abs` | No |
| `BI_fsqrt` | `mkbuiltin_n1t` | Yes | `Float.sqrt` | No |
| `BI_negl` | `mkbuiltin_n1t` | Yes | `Int64.neg` | No |
| `BI_addl` | `mkbuiltin_v2t` | Yes | `Val.addl` | Yes (ptr64) |
| `BI_subl` | `mkbuiltin_v2t` | Yes | `Val.subl` | Yes (ptr64, eq_block) |
| `BI_mull` | `mkbuiltin_v2t` | Yes | `Val.mull'` | No |
| `BI_i16_bswap` | `mkbuiltin_n1t` | Yes | byte-swap 16 | No |
| `BI_i32_bswap` | `mkbuiltin_n1t` | Yes | byte-swap 32 | No |
| `BI_i64_bswap` | `mkbuiltin_n1t` | Yes | byte-swap 64 | No |
| `BI_i64_umulh` | `mkbuiltin_n2t` | Yes | `Int64.mulhu` | No |
| `BI_i64_smulh` | `mkbuiltin_n2t` | Yes | `Int64.mulhs` | No |
| `BI_i64_shl` | `mkbuiltin_v2t` | Yes | `Val.shll` | No |
| `BI_i64_shr` | `mkbuiltin_v2t` | Yes | `Val.shrlu` | No |
| `BI_i64_sar` | `mkbuiltin_v2t` | Yes | `Val.shrl` | No |
| `BI_i64_stod` | `mkbuiltin_n1t` | Yes | `Float.of_long` | No |
| `BI_i64_utod` | `mkbuiltin_n1t` | Yes | `Float.of_longu` | No |
| `BI_i64_stof` | `mkbuiltin_n1t` | Yes | `Float32.of_long` | No |
| `BI_i64_utof` | `mkbuiltin_n1t` | Yes | `Float32.of_longu` | No |
| `BI_select t` | `mkbuiltin` (custom) | **Partial** | match on `Vint` first arg | Yes (normalize) |
| `BI_unreachable` | `mkbuiltin` (custom) | **No** | always `None` | N/A |
| `BI_i64_sdiv` | `mkbuiltin_v2p` | **Partial** | `Val.divls` | No |
| `BI_i64_udiv` | `mkbuiltin_v2p` | **Partial** | `Val.divlu` | No |
| `BI_i64_smod` | `mkbuiltin_v2p` | **Partial** | `Val.modls` | No |
| `BI_i64_umod` | `mkbuiltin_v2p` | **Partial** | `Val.modlu` | No |
| `BI_i64_dtos` | `mkbuiltin_n1p` | **Partial** | `Float.to_long` | No |
| `BI_i64_dtou` | `mkbuiltin_n1p` | **Partial** | `Float.to_longu` | No |

### x86 Platform Builtins (`x86/Builtins1.v`)

| Builtin | Constructor | Total? | Semantics | Pointer-involving? |
|---------|-------------|--------|-----------|-------------------|
| `BI_fmin` | `mkbuiltin_n2t` | Yes | `Float.compare`-based min | No |
| `BI_fmax` | `mkbuiltin_n2t` | Yes | `Float.compare`-based max | No |

### RISC-V Platform Builtins (`riscV/Builtins1.v`)

Empty type -- no platform builtins defined.

### AArch64 Platform Builtins (`aarch64/Builtins1.v`)

Empty type -- no platform builtins defined.

### Replicate (Protocol) Builtins (`backend/Builtins2.v`)

| Builtin | Purpose | Semantics |
|---------|---------|-----------|
| `BI_smove_int_green` | Shadow-move green int | `smove_int_sem` |
| `BI_smove_long_green` | Shadow-move green long | `smove_long_sem` |
| `BI_smove_single_green` | Shadow-move green single | `smove_single_sem` |
| `BI_smove_float_green` | Shadow-move green float | `smove_float_sem` |
| `BI_smove_int_blue` | Shadow-move blue int | `smove_int_sem` |
| `BI_smove_long_blue` | Shadow-move blue long | `smove_long_sem` |
| `BI_smove_single_blue` | Shadow-move blue single | `smove_single_sem` |
| `BI_smove_float_blue` | Shadow-move blue float | `smove_float_sem` |
| `BI_vote_int` | Majority vote on ints | `vote_sem` / `vote3_sem` |
| `BI_vote_long` | Majority vote on longs | `vote_sem` / `vote3_sem` |
| `BI_vote_single` | Majority vote on singles | `vote_sem` / `vote3_sem` |
| `BI_vote_float` | Majority vote on floats | `vote_sem` / `vote3_sem` |
| `BI_check_int` | DMR check on ints | `check_sem` |
| `BI_check_long` | DMR check on longs | `check_sem` |
| `BI_check_single` | DMR check on singles | `check_sem` |
| `BI_check_float` | DMR check on floats | `check_sem` |

---

## Table Stakes

Features that MUST be in the initial implementation for correctness and completeness.

### 1. Shared classification predicate (`builtin_can_replicate`)

| Feature | Why Expected | Complexity | Notes |
|---------|--------------|------------|-------|
| Boolean `builtin_can_replicate : external_function -> bool` | Single source of truth consumed by TMR, faulting, coloring, checker, oracle | Low | Pattern-match on `EF_builtin`, lookup, then classify by `builtin_function` variant |
| Propositional form + reflection lemma | Proofs in RTLtolerant.v need `Prop`-level reasoning, not just `bool` | Low | Standard `reflect` pattern |
| `builtin_can_fault` aligned with `builtin_can_replicate` | Faulty RTL semantics must agree with TMR on which builtins get replicated | Low | Can literally be `= builtin_can_replicate` for first cut |

### 2. Pure numerical total builtins in the safe whitelist

These are the absolute minimum -- builtins constructed with `mkbuiltin_n1t`/`mkbuiltin_n2t`/`mkbuiltin_n3t` that operate purely on numerical types with no pointer involvement and no partiality. A faulted input of `val_compat` shape (same constructor, different payload) always produces a result of the same constructor.

| Feature | Why Expected | Complexity | Notes |
|---------|--------------|------------|-------|
| `BI_fabs` safe | Pure `Float.abs`, total, numerical-only | Low | `mkbuiltin_n1t Tfloat Xfloat` -- `proj_num` on `Vfloat` only |
| `BI_fabsf` safe | Pure `Float32.abs`, total, numerical-only | Low | Same pattern as `BI_fabs` |
| `BI_fsqrt` safe | Pure `Float.sqrt`, total, numerical-only | Low | IEEE 754 sqrt is total (NaN -> NaN) |
| `BI_negl` safe | Pure `Int64.neg`, total, numerical-only | Low | `mkbuiltin_n1t Tlong Xlong` |
| `BI_mull` safe | Pure `Val.mull'`, total, no pointers | Low | `mkbuiltin_v2t` but args are ints, result is long |
| `BI_i16_bswap` safe | Pure byte-swap, total, numerical-only | Low | `mkbuiltin_n1t Tint` |
| `BI_i32_bswap` safe | Pure byte-swap, total, numerical-only | Low | `mkbuiltin_n1t Tint` |
| `BI_i64_bswap` safe | Pure byte-swap, total, numerical-only | Low | `mkbuiltin_n1t Tlong` |
| `BI_i64_umulh` safe | Pure `Int64.mulhu`, total, numerical-only | Low | `mkbuiltin_n2t Tlong Tlong` |
| `BI_i64_smulh` safe | Pure `Int64.mulhs`, total, numerical-only | Low | `mkbuiltin_n2t Tlong Tlong` |
| `BI_i64_stod` safe | Pure `Float.of_long`, total, numerical-only | Low | `mkbuiltin_n1t Tlong Xfloat` |
| `BI_i64_utod` safe | Pure `Float.of_longu`, total, numerical-only | Low | `mkbuiltin_n1t Tlong Xfloat` |
| `BI_i64_stof` safe | Pure `Float32.of_long`, total, numerical-only | Low | `mkbuiltin_n1t Tlong Xsingle` |
| `BI_i64_utof` safe | Pure `Float32.of_longu`, total, numerical-only | Low | `mkbuiltin_n1t Tlong Xsingle` |
| x86 `BI_fmin` safe | Pure float comparison+select, total, numerical-only | Low | `mkbuiltin_n2t Tfloat Tfloat Xfloat` |
| x86 `BI_fmax` safe | Pure float comparison+select, total, numerical-only | Low | `mkbuiltin_n2t Tfloat Tfloat Xfloat` |

**Val_compat argument for `mkbuiltin_nNt` builtins:** These use `proj_num` which returns `Vundef` when the input value's constructor does not match the expected type. Under `val_compat`, a faulted `Vint i` stays `Vint j` (for some `j`), so `proj_num Tint` still succeeds and produces a numerical result. If the input were somehow `Vundef`, `proj_num` returns `Vundef` which is still `val_compat` with anything. The key insight: `mkbuiltin_nNt` builtins always produce `Some (inj_num ...)` or `Some Vundef` on well-arityied inputs -- they never return `None` for the inner computation.

### 3. Protocol builtins excluded from safe classification

| Feature | Why Expected | Complexity | Notes |
|---------|--------------|------------|-------|
| All `BI_replicate` builtins excluded | `smove`, `vote`, `check` have dedicated coloring/TMR handling | Low | `builtin_can_replicate (BI_replicate _) = false` |
| Unrecognized `EF_builtin` excluded | Fall through `lookup_builtin_function` to external call semantics -- not pure | Low | When lookup returns `None`, classify as unsafe |

### 4. `zap_allowed` relaxation for safe builtins

| Feature | Why Expected | Complexity | Notes |
|---------|--------------|------------|-------|
| `zap_allowed (Ibuiltin ef args res s) = builtin_can_fault ef` | Currently `False` for all builtins; must match the classification | Low | One-line change to the definition |

### 5. TMR pass replicates safe builtins

| Feature | Why Expected | Complexity | Notes |
|---------|--------------|------------|-------|
| `transf_instr` emits per-color copies for safe builtins | Analogous to existing `Iop` triplication | Med | Reuse `AST.map_builtin_arg`/`map_builtin_res` for renaming |
| White-only builtins keep current "vote-execute-copy" path | No regression for unsafe builtins | Low | Existing code path |

### 6. Color spec/checker/oracle accept safe builtins with basic colors

| Feature | Why Expected | Complexity | Notes |
|---------|--------------|------------|-------|
| `wc_Ibuiltin_safe` rule in `RTLcolor.v` | Analogous to `wc_Iop_safe` | Med | Same well-colored structure, different instruction constructor |
| `check_col_instr` handles safe builtins | Must accept checker input from TMR | Med | Mirror the existing Iop split |
| Oracle assigns basic colors to safe builtins | Inference must produce colorings the checker accepts | Low | OCaml change in `RTLinfercolor.ml` |

---

## Differentiators

Features that COULD be in the safe whitelist but need careful analysis. Not blocking, but valuable.

### 1. `BI_addl` and `BI_subl` -- total but pointer-involving

| Feature | Value Proposition | Complexity | Notes |
|---------|-------------------|------------|-------|
| `BI_addl` safe (conditionally) | More builtins participate in TMR | Med | Uses `Val.addl`, which on `ptr64=true` can involve pointer arithmetic. Under `val_compat`, `Vptr b1 ofs1` maps to `Vptr b2 ofs2` -- addition still produces `Vptr`. The `_v2t` constructor ensures totality. But the val_compat proof for the result needs care: `Val.addl (Vptr b1 ofs1) (Vlong n)` produces `Vptr b1 (ofs1+n)`, while the faulted version produces `Vptr b2 (ofs2+n')` -- both are `Vptr`, so `val_compat` holds. |
| `BI_subl` safe (conditionally) | More builtins participate in TMR | High | Uses `Val.subl`, which on `ptr64=true` involves `eq_block` -- subtracting pointers from different blocks returns `Vundef`. Analogous to `is_protected Osubl` for the `Osubl` operation. The same `Archi.ptr64`-dependent protection logic applies. If `ptr64=false`, subtraction of two longs is safe. If `ptr64=true`, cross-block subtraction can get stuck. Recommend: follow the same conditional logic as `is_protected_Osubl`. |

### 2. `BI_i64_shl`, `BI_i64_shr`, `BI_i64_sar` -- total but shift-amount-sensitive

| Feature | Value Proposition | Complexity | Notes |
|---------|-------------------|------------|-------|
| `BI_i64_shl` safe | 64-bit shift left | Med | Uses `Val.shll`, which returns `Vundef` when `Int.ltu` fails (shift amount >= 64). Under `val_compat`, a faulted shift amount `Vint j` still passes through `Int.ltu` -- it either succeeds (producing `Vlong`) or fails (producing `Vundef`). Either way, `val_compat` holds since `Vundef` is compatible with everything. The existing `val_compat_shll_imm` lemma in `RTLfault.v` already handles this pattern for `Iop` shifts with immediate amounts, but builtin shifts take the amount as a runtime value, so both arguments can be faulted. |
| `BI_i64_shr` safe | 64-bit logical shift right | Med | Same analysis as `BI_i64_shl` via `Val.shrlu` |
| `BI_i64_sar` safe | 64-bit arithmetic shift right | Med | Same analysis as `BI_i64_shl` via `Val.shrl` |

**Key subtlety:** For `Iop` shifts, the second argument (shift amount) is often an immediate `Vint n` that cannot be faulted. For `Ibuiltin` shifts, both arguments come from registers and can be faulted. The `val_compat` analysis still works because `Val.shll (Vlong i) (Vint j)` always returns either `Vlong _` or `Vundef`, both of which satisfy `val_compat`. But a new proof lemma may be needed -- the existing `val_compat_shll_imm` assumes the shift amount is a fixed `Vint n`, not a faulted register.

**Recommendation:** Include in the safe whitelist. The proof obligation is a moderate generalization of existing lemmas (`val_compat_shll_imm` -> `val_compat_shll` without `_imm`). The `mkbuiltin_v2t` constructor guarantees totality at the builtin level.

### 3. Architecture-conditional classification

| Feature | Value Proposition | Complexity | Notes |
|---------|-------------------|------------|-------|
| `builtin_can_replicate` varies by `Archi.ptr64` for `BI_subl` | Correct classification on both 32-bit and 64-bit targets | Med | Same pattern as `is_protected_Osubl`. For `BI_addl`, no architecture dependency needed (both ptr+long and long+long cases produce `val_compat` results). |
| RISC-V/AArch64 platform builtins are vacuously safe | No platform builtins defined for these targets | Low | Empty inductive type -- the match is exhaustive with zero cases |

---

## Anti-Features

Features to explicitly NOT build or NOT classify as safe.

### 1. Partial builtins must NOT be safe

| Anti-Feature | Why Avoid | What to Do Instead |
|--------------|-----------|-------------------|
| `BI_select` in safe whitelist | Returns `None` when first argument is not `Vint`. Under `val_compat`, a faulted `Vint` stays `Vint` (so the match succeeds), but the first arg could also be `Vundef` from a prior fault, causing `None` and a stuck execution. Additionally, `BI_select` uses `Val.normalize` which involves pointer handling. More fundamentally, it uses a custom `mkbuiltin` constructor, not the `_t` family. | Keep White-only |
| `BI_unreachable` in safe whitelist | Always returns `None` -- execution always gets stuck | Keep White-only |
| `BI_i64_sdiv` / `BI_i64_udiv` in safe whitelist | `mkbuiltin_v2p` -- division by zero returns `None`. Under faulted inputs, the divisor could become zero when it was nonzero before. | Keep White-only |
| `BI_i64_smod` / `BI_i64_umod` in safe whitelist | `mkbuiltin_v2p` -- same division-by-zero concern as div. Parallel to `is_protected Omod*` for operations. | Keep White-only |
| `BI_i64_dtos` / `BI_i64_dtou` in safe whitelist | `mkbuiltin_n1p` -- float-to-long conversion can fail (out-of-range, NaN). Parallel to `is_protected Olongoffloat` / `Olongofsingle` for operations. | Keep White-only |

### 2. Protocol builtins must NOT be generic-safe

| Anti-Feature | Why Avoid | What to Do Instead |
|--------------|-----------|-------------------|
| `smove` builtins as replicable | They ARE the replication mechanism -- they move values between color worlds. Treating them as generic safe builtins would create circular logic in the color system. | Dedicated coloring rules (existing) |
| `vote` builtins as replicable | They ARE the voting mechanism -- they aggregate values across color worlds. They have dedicated TMR/coloring/tolerant-proof treatment. | Dedicated coloring rules (existing) |
| `check` builtins as replicable | DMR-specific. Not on the TMR theorem path. Even though `check_sem` is trivially total (always returns `Vundef`), it is a protocol instruction with dedicated meaning. | Keep out of scope; conservative White-only if encountered |

### 3. Unrecognized builtins must NOT be safe

| Anti-Feature | Why Avoid | What to Do Instead |
|--------------|-----------|-------------------|
| Treating any `EF_builtin name sg` with failed lookup as safe | When `lookup_builtin_function name sg = None`, the builtin falls through to `external_functions_sem`, which has general external-call semantics: may produce traces, may modify memory. Not pure, not deterministic. | Require successful lookup as a precondition for any safe classification |

### 4. Loads are NOT builtins and must NOT be conflated

| Anti-Feature | Why Avoid | What to Do Instead |
|--------------|-----------|-------------------|
| Folding load treatment into builtin classification | `Iload` is a separate instruction kind that interacts with memory directly. Its fault model is fundamentally different (memory addresses can fault, memory contents can differ). Mixing this with pure-computation builtin classification creates unnecessary coupling. | Separate design effort (explicitly out of scope per PROJECT.md) |

### 5. Merging with `is_protected`

| Anti-Feature | Why Avoid | What to Do Instead |
|--------------|-----------|-------------------|
| Defining `builtin_can_replicate` as part of or dependent on `is_protected` | `is_protected` classifies `operation` values, not `external_function` values. They are different types with different semantics. Protocol builtins are pure but still non-replicable -- `is_protected` has no concept of protocol builtins. | Keep `builtin_can_replicate` as an independent predicate on `external_function`, defined in `common/Builtins.v` |

---

## Feature Dependencies

```
                 builtin_can_replicate (definition)
                            |
              +-------------+-------------+
              |             |             |
         zap_allowed    TMR pass     Color spec
         relaxation    replication    wc_Ibuiltin_safe
              |             |             |
              |             |        +----+----+
              |             |        |         |
              |         TMR spec   Color     Color
              |         update    checker    oracle
              |             |        |         |
              +------+------+--------+---------+
                     |
              Tolerant proof
              (new safe-builtin case)
                     |
              Semantic property validation
              (val_compat monotonicity for total builtins)
```

Key ordering constraints:

1. `builtin_can_replicate` definition MUST come first -- all consumers depend on it
2. Semantic property validation SHOULD come before TMR pass and tolerant proof work -- it retires the main proof risk early
3. TMR pass, color spec, and `zap_allowed` can proceed in parallel after the classification exists
4. Color checker and oracle depend on color spec
5. Tolerant proof depends on ALL of the above being consistent

---

## MVP Recommendation

Prioritize:

1. **Shared classification predicate** -- everything else depends on this
2. **Pure numerical total builtins** (the 14 `mkbuiltin_nNt` standard builtins + 2 x86 platform builtins) -- these are the easiest to prove safe and cover the most common arithmetic helpers
3. **Semantic property validation** -- prove `val_compat` monotonicity for the `mkbuiltin_nNt` class before investing in TMR/coloring changes

Defer:

- `BI_addl`: pointer involvement makes `val_compat` proof slightly more complex than pure numerical builtins, though likely doable. Include in a second pass once the `mkbuiltin_nNt` class is proven.
- `BI_subl`: architecture-conditional safety mirrors `is_protected_Osubl`. Include only after `BI_addl` is validated, since it is strictly harder.
- `BI_i64_shl` / `BI_i64_shr` / `BI_i64_sar`: total via `mkbuiltin_v2t` but need a generalized `val_compat` lemma (both arguments faulted, not just the value with a fixed immediate). Medium proof effort. Include in a second pass.
- `BI_mull`: uses `Val.mull'` via `mkbuiltin_v2t`. The semantics take two `Vint` and produce `Vlong`. Under `val_compat`, two faulted `Vint` inputs produce a `Vlong` result, which is `val_compat` with the original `Vlong` result. Safe to include, but since it uses `mkbuiltin_v2t` (value-level, not numerical-level), it is a slightly different proof pattern than the pure `mkbuiltin_nNt` builtins. Recommend grouping with the `BI_addl`/shift second pass.

**First-cut whitelist (16 builtins):**
- `BI_fabs`, `BI_fabsf`, `BI_fsqrt`, `BI_negl`
- `BI_i16_bswap`, `BI_i32_bswap`, `BI_i64_bswap`
- `BI_i64_umulh`, `BI_i64_smulh`
- `BI_i64_stod`, `BI_i64_utod`, `BI_i64_stof`, `BI_i64_utof`
- x86: `BI_fmin`, `BI_fmax`
- (Also safe but deferred to second pass: `BI_mull`)

**Second-cut whitelist (add 6 more, 22 total):**
- `BI_mull`
- `BI_addl` (unconditionally -- pointer-involving but still total and val_compat-safe)
- `BI_subl` (conditionally on `Archi.ptr64 = false`, matching `is_protected_Osubl`)
- `BI_i64_shl`, `BI_i64_shr`, `BI_i64_sar` (generalized val_compat lemmas needed)

---

## The `_t` / `_p` Split Concretely

The `Builtins0.v` constructors implement a layered system:

### Value-level constructors (operate on `val` directly)

- `mkbuiltin_v1t` / `mkbuiltin_v2t` / `mkbuiltin_v3t`: **Total**. The underlying function `val -> val` always produces a result. The builtin returns `Some` when given the correct arity, `None` only on arity mismatch (which cannot happen at well-typed RTL instruction execution).
- `mkbuiltin_v1p` / `mkbuiltin_v2p`: **Partial**. The underlying function `val -> option val` can return `None` even with correct arity. This corresponds to division-by-zero, out-of-range conversions, etc.

### Numerical-level constructors (operate on `int`/`int64`/`float`/`float32`)

- `mkbuiltin_n1t` / `mkbuiltin_n2t` / `mkbuiltin_n3t`: **Total and numerical-only**. These wrap numerical functions through `proj_num` (which extracts `int`/`int64`/`float`/`float32` from `val`, returning `Vundef` on type mismatch) and `inj_num` (which wraps the result back into `val`). They never involve pointers. Under `val_compat`, a faulted `Vint i` becomes `Vint j` which `proj_num Tint` still successfully extracts.
- `mkbuiltin_n1p` / `mkbuiltin_n2p`: **Partial and numerical-only**. The underlying numerical function can return `None`. Used for float-to-integer conversions that fail on out-of-range values.

### Custom constructors (not `_t` or `_p`)

- `BI_select`: Uses raw `mkbuiltin` with a hand-written match on `Vint n :: v1 :: v2 :: nil`. Partial -- returns `None` when the condition argument is not `Vint`.
- `BI_unreachable`: Uses raw `mkbuiltin` with `fun vargs => None`. Always stuck.
- Protocol builtins: Use `mkbuiltin_v2t` / `mkbuiltin_v3t` with custom semantics.

### Summary: the `_t` / `_p` boundary IS the replication boundary

| Constructor family | Total? | Pointer-free? | Safe for replication? |
|-------------------|--------|---------------|----------------------|
| `mkbuiltin_n*t` | Yes | Yes | **Yes** -- strongest case |
| `mkbuiltin_v*t` | Yes | Maybe | **Likely yes** -- needs per-builtin `val_compat` analysis |
| `mkbuiltin_n*p` | No | Yes | **No** -- can return `None` on faulted inputs |
| `mkbuiltin_v*p` | No | Maybe | **No** -- can return `None` on faulted inputs |
| Custom `mkbuiltin` | Varies | Varies | **No** -- must be analyzed individually; none currently qualify |

This is the structural foundation for the classification. The `_t` suffix is a reliable positive signal; the `_p` suffix is a reliable negative signal; custom constructors require individual analysis and should default to unsafe.

---

## Sources

- `common/Builtins0.v` -- standard builtin definitions, `_t`/`_p` constructors (HIGH confidence, direct code inspection)
- `common/Builtins.v` -- builtin lookup and `builtin_function_sem_lessdef` (HIGH confidence)
- `x86/Builtins1.v` -- x86 platform builtins `BI_fmin`/`BI_fmax` (HIGH confidence)
- `riscV/Builtins1.v` -- empty platform builtin type (HIGH confidence)
- `aarch64/Builtins1.v` -- empty platform builtin type (HIGH confidence)
- `backend/Builtins2.v` -- protocol builtins (smove, vote, check) (HIGH confidence)
- `backend/RTLfault.v` -- `zap_allowed`, `val_compat`, `maybe_zap` (HIGH confidence)
- `backend/RTL.v` -- `is_protected`, `res_of_instruction` (HIGH confidence)
- `common/Events.v` -- `known_builtin_sem`, `builtin_or_external_sem` (HIGH confidence)
- `plans/builtin-treatment-plan.md` -- detailed implementation plan (HIGH confidence, project-internal)
