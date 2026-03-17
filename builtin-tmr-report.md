# Technical Report: Safe Builtin Replication in TMR

## Summary

This report documents the implementation of safe builtin replication in
the CompCert TMR (Triple Modular Redundancy) fault tolerance extension
in the current tree on branch `improve-builtins-tmr`, relative to
baseline commit `061e68a8` and current `HEAD` `9e1b59d6` (32 commits
from the baseline). The work follows the plan in
`plans/builtin-treatment-plan.md`.

Previously, all `Ibuiltin` instructions were treated conservatively:
arguments were majority-voted, the builtin executed once in the regular
(White) world, and the result was copied to shadow registers. This is
sound but overly restrictive. The change identifies a safe subset of
builtins that can be triplicated like ordinary `Iop` instructions,
allowing faults on their inputs to be corrected by voting on outputs.

All proof targets compile with no `Admitted` lemmas, and the extracted
compiler rebuilds with the color oracle aligned to the verified
classification and checker.

## Motivation

Under the original design, a single-fault corruption of a register
feeding a safe arithmetic builtin (e.g., `__builtin_fabs`) could not
be corrected because the builtin read only the voted (single-copy)
value. After triplication, each color world executes its own copy of
the builtin, and the subsequent majority vote on the results masks the
fault -- exactly as it already does for `Iop` instructions.

## Classification

### Definition site

A shared boolean classifier `builtin_can_replicate` was added to
`common/Builtins.v`, the module where `builtin_function`,
`lookup_builtin_function`, and `builtin_function_sem` are defined.
This gives one canonical decision point consumed by all
relevant consumers (TMR pass, TMR spec/proof, color spec, color
checker, color oracle, faulty semantics, tolerant proof).

### Structure

The classifier has two layers:

- `builtin_can_replicate_bf : builtin_function -> bool` -- exhaustive
  match on `builtin_function` constructors.
- `builtin_can_replicate : external_function -> bool` -- dispatches
  `EF_builtin name sg` through `lookup_builtin_function`, returns
  `false` for all other `external_function` constructors.
- `builtin_can_fault : external_function -> bool` -- currently
  definitionally equal to `builtin_can_replicate`, defined separately
  for future divergence.

### Whitelist

On the current `x86_64-linux` configuration, the following builtins are
classified as replicable. `BI_subl` is conditional and is included only
when `Archi.ptr64 = false`.

| Category | Builtins |
|----------|----------|
| Float ops | `BI_fabs`, `BI_fabsf`, `BI_fsqrt` |
| 64-bit integer | `BI_negl`, `BI_addl`, `BI_mull` |
| 64-bit integer (conditional) | `BI_subl` (only when `Archi.ptr64 = false`) |
| Byte swap | `BI_i16_bswap`, `BI_i32_bswap`, `BI_i64_bswap` |
| Wide multiply | `BI_i64_umulh`, `BI_i64_smulh` |
| Conversions | `BI_i64_stod`, `BI_i64_utod`, `BI_i64_stof`, `BI_i64_utof` |
| Platform (x86) | `BI_fmin`, `BI_fmax` |

### Excluded builtins

| Category | Builtins | Reason |
|----------|----------|--------|
| Shifts | `BI_i64_shl`, `BI_i64_shr`, `BI_i64_sar` | `val_compat` unprovable when shift amount is faulted (see below) |
| Partial | `BI_i64_sdiv/udiv/smod/umod`, `BI_i64_dtos/dtou` | Semantics returns `None` on some inputs |
| Control | `BI_select`, `BI_unreachable` | Semantically fragile |
| Protocol | `smove`, `vote`, `check` | TMR/DMR protocol builtins with dedicated handling |

## File-by-file changes

### `common/Builtins.v` (+404 lines)

- `builtin_can_replicate_bf`, `builtin_can_replicate`, `builtin_can_fault`
  definitions.
- Reflection lemma `builtin_can_replicate_bf_spec` and convenience
  lemmas connecting the boolean to propositional forms.
- Protocol-builtin recognizers migrated from `backend/RTL.v`:
  `is_green_smove_builtin{,b}`, `is_blue_smove_builtin{,b}`,
  `is_vote_builtin{,b}`, `is_vote_runtime{,b}`, and their reflection
  and cross-exclusion lemmas.

### `backend/RTL.v` (-280 lines)

- Removed all protocol-builtin recognizers (now in `Builtins.v`).

### `backend/RTLfault.v` (+362 lines)

- `zap_allowed` for `Ibuiltin ef _ _ _` changed from `False` to
  `builtin_can_fault ef = true`.
- New section `VAL_COMPAT_OPS` proving `val_compat` monotonicity for
  safe builtins, the key semantic property needed by the tolerant proof:
  - `val_compat_proj_num_inj`, `val_compat_proj_num_inj2`:
    `val_compat` preserved through `proj_num`/`inj_num` chains.
  - `val_compat_mkbuiltin_n1t`, `val_compat_mkbuiltin_n2t`:
    generic monotonicity for 1-arg and 2-arg numerical builtins.
  - `builtin_sem_val_compat_addl`, `_mull`, `_subl`:
    lifting `Val.*` lemmas to the `standard_builtin_sem` wrapper.
  - Shift-restricted lemmas (`_shl_restricted`, `_shr_restricted`,
    `_sar_restricted`) and documented proof that the general case is
    unprovable (`builtin_sem_val_compat_shl_UNPROVABLE`).
  - Unified dispatcher `builtin_sem_val_compat` gated by
    `builtin_can_replicate_bf = true`, excluding shift builtins.
  - `standard_builtin_sem_val_compat`,
    `platform_builtin_sem_val_compat`: per-class dispatchers.

### `backend/RTLtmr.v` (+40 lines)

- `transf_instr` now matches on `Ibuiltin ef bargs bres succ`:
  - If `builtin_can_replicate ef = true` and `bres = BR res`:
    emits three independent `Ibuiltin` instructions (green, blue,
    original), each with arguments remapped via `map_builtin_arg`
    and result written to the corresponding shadow register.
  - Otherwise falls through to the original vote-run-copy path.

### `backend/RTLtmrspec.v` (+189 lines)

- New inductive `rm_builtin_arg` / `rm_builtin_args` relating
  triplicated builtin arguments through the register map, covering
  all `builtin_arg` constructors (`BA`, `BA_int`, `BA_long`,
  `BA_float`, `BA_single`, `BA_loadstack`, `BA_addrstack`,
  `BA_loadglobal`, `BA_addrglobal`, `BA_splitlong`, `BA_addptr`).
- New `match_Ibuiltin_safe` constructor in `match_instr`.
- `NOT_SAFE` premise added to `match_Ibuiltin_2` for mutual
  exclusivity.
- `rm_builtin_arg_map`, `rm_builtin_args_map`: connecting
  `map_builtin_arg` to the relational spec.
- `state_incr_match_instr` and `transf_instr_match_instr` proofs
  updated for the new constructors.

### `backend/RTLtmrproof.v` (+297 lines)

- `external_call_can_replicate_E0`: replicable builtins produce `E0`
  and leave memory unchanged.
- `eval_builtin_arg_rm_{2,3}`: green/blue-world `eval_builtin_arg`
  remapping through `rm_builtin_arg` and `match_regsets`.
- `eval_builtin_args_rm_{2,3}`: list-lifted versions.
- `match_Ibuiltin_safe` case in `step_simulation`: three independent
  `exec_Ibuiltin` steps (green at `pc`, blue at `n1`, original at
  `n2`), with `match_regsets` re-established for the successor state
  via `match_regsets_update` and register distinctness from `rm_wf`.

### `backend/RTLcolor.v` (+10 lines)

- New `wc_Ibuiltin_safe` constructor analogous to `wc_Iop_safe`:
  requires `builtin_can_replicate ef = true`, basic color for result,
  all argument registers colored the same basic color, and frame
  condition on live registers.
- `builtin_can_replicate ef = false` premise added to the generic
  `wc_Ibuiltin` constructor for mutual exclusivity.

### `backend/RTLcolorcheck.v` (+86 lines net)

- Safe-builtin branch in `check_col_instr`: when
  `builtin_can_replicate ef = true` and `bres = BR res`, checks
  `is_basicb (col succ res)`, all argument registers match the result
  color, and the frame condition.
- `check_col_instr_sound` proof updated for both the new safe case
  and the modified generic case.

### `backend/RTLinfercolor.ml`

- The oracle now calls the extracted Coq classifier
  `Builtins.builtin_can_replicate` directly instead of maintaining a
  hand-copied OCaml whitelist.
- Safe builtin constraints now mirror the checker's strengthened
  `wc_Ibuiltin_safe` rule: argument registers are equated with the
  result color, and every live non-result register is constrained to
  preserve its color across the instruction.
- Non-replicable builtins still fall through to the existing White-only
  constraints.
- This removes the previous oracle/checker mismatch for shift builtins
  and keeps future policy changes centralized in `common/Builtins.v`.

### `backend/RTLtolerant.v` (+330 lines)

- `maybe_zap_preserves_match_states`: handles `wc_Ibuiltin_safe` via
  `builtin_can_fault` congruence.
- Helper lemmas in `TOLERANCE` section:
  - `safe_external_call_E0`, `safe_external_call_mem`: replicable
    builtins produce empty traces and unchanged memory.
  - `safe_external_call_total`: given `val_compat` arguments and
    extended memory, a safe builtin call succeeds.
  - `safe_external_call_val_compat`: lifting `builtin_sem_val_compat`
    to the `external_call` level.
  - `eval_builtin_arg{,s}_val_compat`: lifting `rs_compat` and
    `Mem.extends` to `eval_builtin_arg` via `val_compat`.
- `faulty_progress`: safe builtins use
  `eval_builtin_args_val_compat` + `safe_external_call_total` +
  `external_call_Three_Two'` for progress; protocol builtins
  eliminated by `vm_compute` on `builtin_can_replicate`.
- `step_simulation`:
  - **Non-faulted safe builtin**: `Val.lessdef` of results via
    `external_call_mem_extends` + `external_call_Three_Two'` +
    `external_call_deterministic`.
  - **Faulted safe builtin**: `val_compat` of results via
    `safe_external_call_val_compat` + transitivity through
    `Val.lessdef`. Frame condition uses the strengthened
    `wc_Ibuiltin_safe` premise (arg registers maintain color).

### Minor import fixes

`backend/Novotes.v`, `backend/Novotesproof.v`,
`backend/RTLagreement.v`: added `Require Import Builtins` since the
protocol-builtin recognizers migrated from `RTL.v` to `Builtins.v`.

## Key design decisions

### 1. Shifts excluded from replication

The 64-bit shift builtins (`BI_i64_shl`, `BI_i64_shr`, `BI_i64_sar`)
use `Int.ltu` to range-check the shift amount. Under `val_compat`,
the shift amount can be faulted to a different `Vint` value, causing
`Int.ltu` to succeed on the non-faulted side and fail on the faulted
side. This produces `Vlong` vs `Vundef`, which violates `val_compat`.
The file `RTLfault.v` contains `builtin_sem_val_compat_shl_UNPROVABLE`
documenting this impossibility. Restricted lemmas for same-shift-amount
are proved but not needed since shifts are excluded from the whitelist.

### 2. Strengthened `wc_Ibuiltin_safe` frame condition

The initial `wc_Ibuiltin_safe` color rule only required the result
register to maintain its color across the instruction. The faulted
case in `step_simulation` also needs argument registers to preserve
their color (since `match_rs` depends on color stability). The frame
condition was strengthened to mirror `wc_Iop_safe`: argument registers
must have the same color as the result, and all live registers other
than the result must preserve color from `pc` to `succ`. The checker
was updated accordingly.

### 3. Protocol-builtin migration

The protocol-builtin recognizers (`is_green_smove_builtin`,
`is_blue_smove_builtin`, `is_vote_builtin`, `is_vote_runtime`) were
migrated from `backend/RTL.v` to `common/Builtins.v`. This
consolidates all builtin classification in one module and removes
280 lines from `RTL.v`. Six downstream consumers required explicit
`Require Import Builtins` additions.

### 4. Separate `builtin_can_fault`

`builtin_can_fault` is defined as a separate function equal to
`builtin_can_replicate`. This allows future divergence if some
replicable builtins are proven fault-immune (i.e., their replicated
copies always agree regardless of faults, making them faultable but
correction via voting is unnecessary).

### 5. Oracle alignment matters operationally

`RTLinfercolor.ml` is unverified, but it is still on the compiler's
critical path: `Driver.ml` runs the oracle and then rejects programs
whose inferred coloring fails the verified checker. Because of that,
oracle/checker disagreement is not merely a proof hygiene issue; it can
turn into a compile-time failure. The final oracle update therefore
matters for both consistency and usability.

## Proof architecture

The proof decomposes into three independent verification layers:

1. **TMR backward simulation** (`RTLtmrproof.v`): The three
   `Ibuiltin` target steps (green, blue, original) each evaluate the
   same builtin with the same arguments (via `eval_builtin_args_rm_2/3`
   and `match_regsets`), producing the same result. The key insight is
   that `external_call_can_replicate_E0` guarantees `E0` trace and
   unchanged memory, so the three steps compose cleanly. Register
   distinctness from `rm_wf` ensures the intermediate writes don't
   interfere.

2. **Color system soundness** (`RTLcolorcheck.v`): The checker mirrors
   the `wc_Iop_safe` pattern. For safe builtins, it verifies
   `is_basicb` on the result color, uniform argument color, and the
   frame condition. The soundness proof (`check_col_instr_sound`)
   handles safe and generic builtins in separate branches gated by
   `builtin_can_replicate`.

3. **Tolerant backward simulation** (`RTLtolerant.v`): The most
   complex part. The non-faulted case uses `Val.lessdef` of builtin
   results via `external_call_mem_extends`. The faulted case uses
   `val_compat` of results: `safe_external_call_val_compat` lifts
   `builtin_sem_val_compat` from the `builtin_function` level to
   `external_call`, chaining through `external_call_Three_Two'` and
   `external_call_deterministic` to relate the Three-voting source
   result to the Two-voting target result.

## Validation

- All 13 changed `.v` files compile to `.vo` with no `Admitted` lemmas.
- `make ccomp` succeeds after rebuilding the extracted compiler with the
  updated oracle.
- A small `__builtin_fabs` regression example that keeps the builtin
  argument live across the call compiles successfully under `-tmr`,
  exercising the safe-builtin oracle/checker path end to end.
- The `RTLinfercolor.ml` oracle is unverified by design, but its output
  is validated by the verified checker at compile time.
