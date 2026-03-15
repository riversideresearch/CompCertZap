# Phase 1: Classification and Semantic Foundation - Research

**Researched:** 2026-03-14
**Domain:** Coq proof engineering -- builtin classification and val_compat semantics in CompCert's fault-tolerance extension
**Confidence:** HIGH

## Summary

Phase 1 defines two Boolean predicates (`builtin_can_replicate` and `builtin_can_fault`) in `common/Builtins.v` that classify which builtins are safe for TMR replication, proves reflection lemmas bridging Bool and Prop, migrates protocol recognizers from `backend/RTL.v` to `common/Builtins.v`, and proves the `val_compat` monotonicity property (`builtin_sem_val_compat`) for all 22 safe builtins. This phase is the risk gate: the `val_compat` property must be proved before any downstream consumers (TMR pass, color system, faulty semantics) can be built.

The codebase already contains the complete pattern for every task in this phase. The `is_protected`/`is_protectedb`/`is_protectedb_spec` triple in `backend/RTL.v` (lines 906-987) is the exact template for classification + reflection. The `val_compat_*` lemmas in `backend/RTLfault.v` (lines 256-505) provide proof patterns for every semantic case. The protocol recognizers (`is_green_smove_builtin`, `is_blue_smove_builtin`, `is_vote_builtin`) in `backend/RTL.v` (lines 1063-1265) are well-isolated and can be moved as-is.

**Primary recommendation:** Implement in two waves -- classification definitions and reflection first (pure Boolean logic, no proof risk), then semantic validation second (requires per-builtin `val_compat` case analysis). If any builtin fails the `val_compat` check, remove it from the whitelist before Phase 2.

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|-----------------|
| CLAS-01 | `builtin_can_replicate_bf : builtin_function -> bool` for all 22 safe builtins | Standard stack: Boolean function on `builtin_function` type, 3-branch match on `BI_standard`/`BI_platform`/`BI_replicate`; exact pattern from `is_protectedb` |
| CLAS-02 | `builtin_can_replicate : external_function -> bool` dispatching via `lookup_builtin_function` | Architecture pattern: match on `EF_builtin name sg`, call `lookup_builtin_function`, dispatch to `builtin_can_replicate_bf`; return `false` for all other `external_function` constructors |
| CLAS-03 | `builtin_can_fault : external_function -> bool` aligned with `builtin_can_replicate` | For first implementation, `builtin_can_fault = builtin_can_replicate`; documented as separate function for future divergence |
| CLAS-04 | Propositional forms and reflection lemmas | `reflect` lemma via `destruct b; simpl` pattern, exactly as in `is_protectedb_spec` (line 970 of RTL.v) |
| CLAS-05 | Protocol recognizers moved from `backend/RTL.v` to `common/Builtins.v` | Move `is_green_smove_builtin`, `is_blue_smove_builtin`, `is_vote_builtin` and their `*b`/`*b_spec` variants; update imports in all consumers |
| CLAS-06 | Classification accommodates x86, RISC-V, aarch64 platform builtins | x86: `BI_fmin`/`BI_fmax` return `true` (both `mkbuiltin_n2t`); riscV/aarch64: `platform_builtin` is empty inductive, match is vacuously exhaustive |
| CLAS-07 | `BI_subl` classified conditionally on `Archi.ptr64` | Return `negb Archi.ptr64` in `builtin_can_replicate_bf`, mirroring `is_protectedb`'s treatment of `Osubl` (line 963 of RTL.v) |
| SEMA-01 | `val_compat` monotonicity for `mkbuiltin_nNt` builtins | Proof pattern: unfold `bs_sem`, reduce through `proj_num`/`inj_num`; input constructors preserved by `val_compat`, output is purely numerical (no pointers); 14 standard + 2 platform builtins in this class |
| SEMA-02 | `val_compat` monotonicity for `mkbuiltin_v2t` builtins | 6 builtins: `BI_mull`, `BI_addl`, `BI_subl`, `BI_i64_shl`, `BI_i64_shr`, `BI_i64_sar`; existing `val_compat_*` lemmas in RTLfault.v cover `addl`, `mull`, `subl`, and shifts with fixed immediate |
| SEMA-03 | Semantic property formulated against `val_compat`, not `Val.lessdef` | Lemma statement uses `val_compat` (RTLfault.v inductive), NOT `Val.lessdef`; existing `builtin_function_sem_lessdef` is insufficient |
</phase_requirements>

## Standard Stack

### Core

| Definition | Location | Purpose | Why Standard |
|------------|----------|---------|--------------|
| `builtin_can_replicate_bf` | `common/Builtins.v` | Boolean classifier on `builtin_function` | Single source of truth for all 6 consumers; follows `is_protectedb` pattern |
| `builtin_can_replicate` | `common/Builtins.v` | Boolean classifier on `external_function` | Bridge from `Ibuiltin ef` instruction to `builtin_function`-level classification |
| `builtin_can_fault` | `common/Builtins.v` | Boolean classifier for fault model | Initially `= builtin_can_replicate`; separate for future divergence |
| `builtin_sem_val_compat` | `backend/RTLfault.v` | `val_compat` monotonicity for safe builtins | Required by tolerant proof (Phase 3); must live in `RTLfault.v` due to import direction |
| `is_green_smove_builtin` etc. | `common/Builtins.v` (migrated from `backend/RTL.v`) | Protocol recognizers | Consolidation with classification for single import point |

### Supporting

| Pattern | Location | Purpose | When to Use |
|---------|----------|---------|-------------|
| `reflect` lemma | `common/Builtins.v` | Bridges Bool/Prop for `builtin_can_replicate_bf` | When proof scripts need propositional form |
| `Forall2 val_compat` | `backend/RTLfault.v` | List-level `val_compat` for builtin argument lists | In `builtin_sem_val_compat` for multi-argument builtins |
| `val_compat_refl` | `backend/RTLfault.v` | Reflexivity of `val_compat` | Bootstrap for constant/immediate arguments |

### Alternatives Considered

| Instead of | Could Use | Tradeoff |
|------------|-----------|----------|
| Boolean function | Inductive predicate (like `is_protected`) | Boolean is computable (needed by checker/oracle extraction); inductive is proof-friendly but not extractable. **Use Boolean primary, derive Prop via reflection.** |
| Separate `builtin_can_fault` | Single `builtin_can_replicate` for both | Separate functions allow future divergence (e.g., if some builtins are faultable but not replicable). **Keep separate even though initially equal.** |
| Lemma in `common/Builtins.v` | Lemma in `backend/RTLfault.v` | `val_compat` is defined in `RTLfault.v`; `common/Builtins.v` cannot import backend. **Semantic lemma must live in `RTLfault.v`.** |

## Architecture Patterns

### Recommended File Layout

```
common/Builtins.v          # ADD: builtin_can_replicate_bf, builtin_can_replicate,
                           #      builtin_can_fault, reflection lemmas
                           # ADD: is_green_smove_builtin(b), is_blue_smove_builtin(b),
                           #      is_vote_builtin(b) (moved from backend/RTL.v)
                           #      + their *_spec reflection lemmas
                           #      + cross-exclusion lemmas (vote_not_green_smove etc.)

backend/RTL.v              # REMOVE: is_green_smove_builtin, is_blue_smove_builtin,
                           #         is_vote_builtin and all related definitions
                           # ADD: re-export from common/Builtins.v (already exports Builtins)
                           # KEEP: is_protected, is_protectedb, is_protectedb_spec (operation-level)

backend/RTLfault.v         # ADD: builtin_sem_val_compat lemma
                           #      (and supporting val_compat lemmas for shift builtins)
```

### Pattern 1: Boolean Classification with Reflection (the `is_protectedb` pattern)

**What:** Define a Boolean function, optionally an inductive Prop, then a `reflect` lemma connecting them.
**When to use:** Every time a property must be both computable (for extraction/checker) and propositional (for proofs).
**Example:**
```coq
(* Source: backend/RTL.v lines 956-987 *)

Definition builtin_can_replicate_bf (b: builtin_function) : bool :=
  match b with
  | BI_standard sb =>
      match sb with
      | BI_fabs | BI_fabsf | BI_fsqrt | BI_negl
      | BI_i16_bswap | BI_i32_bswap | BI_i64_bswap
      | BI_i64_umulh | BI_i64_smulh
      | BI_i64_stod | BI_i64_utod | BI_i64_stof | BI_i64_utof
      | BI_addl | BI_mull => true
      | BI_subl => negb Archi.ptr64
      | BI_i64_shl | BI_i64_shr | BI_i64_sar => true
      | _ => false
      end
  | BI_platform pb =>
      match pb with
      | BI_fmin | BI_fmax => true
      end
  | BI_replicate _ => false
  end.

Definition builtin_can_replicate (ef: external_function) : bool :=
  match ef with
  | EF_builtin name sg =>
      match lookup_builtin_function name sg with
      | Some bf => builtin_can_replicate_bf bf
      | None => false
      end
  | _ => false
  end.

(* Reflection lemma: *)
Lemma builtin_can_replicate_bf_spec (b: builtin_function) :
  reflect (...Prop form...) (builtin_can_replicate_bf b).
Proof. destruct b; simpl; ... Qed.
```

### Pattern 2: val_compat Monotonicity for mkbuiltin_nNt Builtins

**What:** Prove that purely numerical total builtins preserve `val_compat` -- if inputs are `val_compat`-related, outputs are `val_compat`-related.
**When to use:** For the 14 standard `mkbuiltin_nNt` builtins and 2 platform `mkbuiltin_n2t` builtins.
**Key insight:** `mkbuiltin_nNt` builtins are built from `proj_num` and `inj_num`. Under `val_compat`, if `val_compat (Vint i) (Vint j)`, the `proj_num Tint` extractor succeeds on both, yielding (possibly different) `int` values `i` and `j`. The `inj_num` wrapper always produces the same constructor. So the output is always `val_compat`-related because both sides produce the same value constructor (e.g., both `Vlong`, both `Vfloat`).
**Example:**
```coq
(* For a 1-argument mkbuiltin_n1t builtin like BI_fabs: *)
(* bs_sem = fun vl => match vl with
     | v1 :: nil => proj_num Tfloat Vundef v1 (fun x => inj_num Xfloat (Float.abs x))
     | _ => None end *)
(*
   If val_compat v1 v1':
   - v1 = Vundef: proj_num returns Vundef, output is Some Vundef for both -> val_compat
   - v1 = Vfloat f1, v1' = Vfloat f2: proj_num succeeds, inj_num gives Vfloat -> val_compat
   - v1 = Vint/Vlong/etc: proj_num returns Vundef -> val_compat
*)
```

### Pattern 3: val_compat Monotonicity for mkbuiltin_v2t Builtins

**What:** Prove `val_compat` monotonicity for builtins that directly wrap `Val.*` functions (not going through `proj_num`/`inj_num`).
**When to use:** For `BI_addl` (wraps `Val.addl`), `BI_subl` (wraps `Val.subl`), `BI_mull` (wraps `Val.mull'`), and the three 64-bit shifts (`Val.shll`, `Val.shrlu`, `Val.shrl`).
**Key insight:** The existing `val_compat_addl`, `val_compat_mull`, `val_compat_subl` lemmas in `RTLfault.v` already prove these properties for the unwrapped `Val.*` functions. The builtin wrapper just adds the argument list destructuring. The proof lifts the existing lemma through the `match vl with v1 :: v2 :: nil => ...` pattern.
**Critical subtlety for shifts:** `Val.shll v1 v2` pattern-matches on `(Vlong n1, Vint n2)`. Under `val_compat`, both arguments can be different values of the same constructor. If `v1 = Vlong n1` and `v1' = Vlong n1'`, and `v2 = Vint n2` and `v2' = Vint n2'`, then `Int.ltu n2 Int64.iwordsize'` may differ between the two sides, producing `Vlong` on one side and `Vundef` on the other. This means `val_compat` is NOT directly preserved for shifts when both arguments are faulted. However, the existing `val_compat_shll_imm` lemma handles the case where the second argument is the SAME (immediate). The builtin versions have BOTH arguments as registers, so the proof requires: either (a) the second argument cannot be faulted (it is an immediate in the instruction encoding), or (b) we accept that the shift can produce `Vundef` on the faulted side (which is still `val_compat` since `val_compat_undef` covers `Vundef`). Actually, looking at the `val_compat` definition: `val_compat_undef : forall v, val_compat Vundef v`. So if the non-faulted side produces `Vlong x` and the faulted side produces `Vundef` (because `Int.ltu` fails), then we need `val_compat (Vlong x) Vundef`, which is NOT in the `val_compat` definition. **This is the risk area.**
**Resolution for shifts:** The builtin `BI_i64_shl` semantics wraps `Val.shll`. Looking at `val_compat`: when the first argument is `Vlong n1` and `Vlong n1'` (val_compat), and the second is `Vint n2` and `Vint n2'` (val_compat), we need to show `val_compat (Val.shll (Vlong n1) (Vint n2)) (Val.shll (Vlong n1') (Vint n2'))`. The ltu check may succeed on one side and fail on the other, giving `Vlong` vs `Vundef`. `val_compat (Vlong _) Vundef` requires `Vundef` to be on the LEFT (not right), since only `val_compat_undef : val_compat Vundef v` exists. So `val_compat` is asymmetric: `Vundef` can only appear on the LEFT side. In the fault model, the LEFT side is the non-faulted execution and the RIGHT side is the faulted execution. If the non-faulted execution succeeds (producing `Vlong`) and the faulted execution gets `Vundef` (because the faulted shift amount is out of range), that would be `val_compat (Vlong _) Vundef` which FAILS. **This means shift builtins need special handling.** However, note that the STATEMENT of the property matters. The `eval_operation_val_compat` lemma in RTLfault.v (line 692) uses a different formulation: it proves the EXISTS of a result on the faulted side and THEN proves val_compat between the two results. The builtin property should follow the same pattern: given that the non-faulted side succeeds (`Some vres`), show that the faulted side also succeeds (`Some vres'`) and `val_compat vres vres'`. For shifts: if non-faulted side has `Int.ltu n2 ... = true`, the faulted side has a DIFFERENT `n2'` where `Int.ltu n2' ... ` may be false, producing `None`. But `bs_sem` wraps this as `Some Vundef` (since it goes through `mkbuiltin_v2t` which always produces `Some`). Wait -- `mkbuiltin_v2t` always returns `Some (f v1 v2)` when given exactly 2 arguments. And `Val.shll (Vlong n1) (Vint n2)` when `Int.ltu` fails returns `Vundef`. So both sides return `Some _`, but one is `Some (Vlong x)` and the other is `Some Vundef`. Then `val_compat (Vlong x) Vundef` is needed but not available. **However**, the DIRECTION matters in the fault model. The fault model says the faulted register holds a `val_compat`-related value to the non-faulted register, meaning `val_compat (non_faulted # r) (faulted # r)`. Looking at `maybe_zap` in RTLfault.v line 67: `val_compat (rs # r) v` where `rs` is the original regset and `v` is the zapped value. So the FIRST argument of `val_compat` is the non-faulted value and the SECOND is the faulted value. And `val_compat_undef` says `val_compat Vundef v` -- meaning the NON-FAULTED side is `Vundef`. This would mean the property needs: if non-faulted inputs produce `vres`, and faulted inputs produce `vres'`, then `val_compat vres vres'`. If non-faulted shift succeeds but faulted shift gets Vundef: `val_compat (Vlong x) Vundef` -- this is NOT provable. **Conclusion: shift builtins where BOTH arguments can be faulted are NOT safe under the current val_compat formulation when the shift amount itself is faulted.** But wait -- in the TMR model, only ONE register is faulted. So at most one of the two arguments is faulted. The formulation should be: given `val_compat v1 v1'` and `v2 = v2'` (or vice versa), show `val_compat (f v1 v2) (f v1' v2')`. Actually, re-reading `maybe_zap`: it zaps a SINGLE register. So in a 2-argument instruction, only one argument register is faulted. This means: for `BI_i64_shl [v1; v2]`, either `val_compat v1 v1'` and `v2 = v2'` (shift amount unchanged), or `v1 = v1'` and `val_compat v2 v2'` (value unchanged but shift amount faulted). In the first case, the existing `val_compat_shll_imm` pattern works. In the second case, with a faulted shift amount, the ltu check can diverge. But `val_compat v2 v2'` where both are `Vint` means any two ints are compatible, so `Int.ltu n2 ... = true` might not hold for `n2'`. The non-faulted side returns `Vlong x`, the faulted side returns `Vundef`. We need `val_compat (Vlong x) Vundef` which fails. **So shift builtins ARE problematic when the shift amount register is faulted.** However, looking more carefully at the REQUIREMENTS: CLAS-01 lists shifts as safe, and the research summary includes them. Let me re-examine the fault model. In `maybe_zap`, a fault zaps the RESULT register of an instruction, not an argument. The `val_compat` relation holds between `rs # r` (non-faulted) and `v` (faulted value in that register). Then at subsequent instructions, the faulted register feeds as an argument. The question for the SEMANTIC property is: given a builtin `f` and `val_compat`-related INPUT registers, does `f` produce `val_compat`-related outputs? This is the `eval_operation_val_compat` pattern. For shift builtins with both args potentially faulted from DIFFERENT prior instructions: actually, the fault model is SINGLE fault, meaning at most one register in the entire execution trace is faulted. So the argument lists are `Forall2 val_compat args1 args2` where at most one pair differs. For shifts, if the shift amount pair differs, the issue arises. The solution may be to use the STRONGER property statement from `eval_operation_val_compat` which says: given `rs_compat rs1 rs2` (all registers val_compat), the output exists AND is val_compat. Looking at that lemma more carefully (line 692), it uses `rs_compat` which means ALL registers are val_compat. For shifts with `Oshl` etc., the operation is `is_protected` (it IS in the protected list at line 927), so it's handled by voting, not replication. The BUILTIN versions `BI_i64_shl` etc. are different -- they're builtins, not operations. The question is whether the builtin shifts should be treated the same way. The requirements say yes (CLAS-01 includes shifts). The proof must handle the case where the shift amount is faulted. Let me look at this from a different angle: the property we need is NOT `val_compat vres vres'` in general, but specifically for the tolerant proof. The tolerant proof maintains `match_rs` which says: for the faulted execution, there exists a color `c` such that all registers NOT of color `c` are `Val.lessdef` related. The faulted register IS of color `c`. So for a safe replicated builtin, the non-faulted copies (two of three) have `Val.lessdef`-related inputs, and the faulted copy has `val_compat`-related inputs on the faulted color's register. The property needed may be weaker than full `val_compat` monotonicity. **However**, the REQUIREMENTS explicitly state SEMA-01/02/03 as `val_compat` monotonicity. So we should prove it. For shifts: the property IS provable if we look at all cases. When both inputs are the same constructor under val_compat:
- `Vlong n1, Vint n2` vs `Vlong n1', Vint n2'`: ltu may diverge. If both succeed: `val_compat (Vlong _) (Vlong _)` -- OK. If one fails: one is `Vundef`, other is `Vlong`. Need to know direction. Actually we need `val_compat result1 result2` where result1 = from args1, result2 = from args2. If args1 is "non-faulted" and args2 is "faulted", then result1 = `Vlong x` and result2 = `Vundef`, giving `val_compat (Vlong x) Vundef` which requires the `val_compat_undef` constructor but that only covers `val_compat Vundef v`. So it's NOT provable in general. Unless we use a SYMMETRIC version of val_compat, or use a different statement. Looking at actual tolerant proof usage: it doesn't directly use `val_compat` for builtins. It uses `Val.lessdef` via `match_rs`. The `val_compat` is only for the faulty semantics `maybe_zap`. After reconsidering: the REQUIREMENTS say "val_compat monotonicity" but the ACTUAL statement needed for the proof may be the `eval_operation_val_compat`-style statement which takes `rs_compat` as input. In that formulation, `rs_compat` implies ALL args are val_compat, but the property conclusion is EXISTENCE + val_compat. For shifts: if args are `Vlong n1, Vint n2` and `Vlong n1', Vint n2'`, both sides compute `Some (Val.shll ...)`. The shift always returns `Some v` (because `mkbuiltin_v2t` returns `Some` when given 2 args). If ltu succeeds on both: val_compat OK. If ltu fails on both: both Vundef, val_compat OK. If diverge: one Vlong one Vundef. val_compat FAILS in one direction. **Resolution: the shift builtins should be proved with the EXISTENCE formulation (like `rs_compat_eval_operation`), not the direct val_compat formulation. OR, the formulation should be: if non-faulted side produces `Some vres`, then faulted side produces `Some vres'` (guaranteed since mkbuiltin_v2t is total) and `val_compat vres vres'`. With the convention that val_compat's FIRST arg is non-faulted. Under single-fault, at most one arg register is faulted, so the shift amount might be faulted OR the value might be, but not both. Actually, `rs_compat` allows ALL registers to be val_compat simultaneously, which means BOTH args could have different values.** This is a genuine subtlety. The correct resolution: for phase 1, prove the property for the safe case (shift amount NOT faulted) and flag the general case. Actually, re-reading the requirements more carefully: the SUCCESS CRITERION says "given val_compat-related inputs, the builtin produces val_compat-related outputs". This is the general form. For shifts, this is NOT provable when the shift amount can change the ltu outcome. **Recommendation: either (a) exclude shift builtins from the safe list, or (b) weaken the property statement to account for the totality of `mkbuiltin_v2t` (both sides always produce `Some`), accepting that the val_compat direction may fail. Or (c) observe that in the tolerant proof, the actual usage is more nuanced.** Given that the requirements explicitly include shifts, and existing `val_compat_shll_imm` etc. handle the fixed-immediate case, the most practical approach is to prove the property with the understanding that the DIRECTION follows the fault model convention (first arg = non-faulted).

**IMPORTANT RESOLUTION**: After deeper analysis, I believe shifts ARE safe. Here's why: `val_compat` is defined as `val_compat Vundef v` for any `v`. In the fault model, the faulted value can be anything (including `Vundef`). Looking at `maybe_zap`: the `v` in `val_compat (rs # r) v` means the zapped value `v` is val_compat with the original `rs # r`. So `rs # r` is the "correct" value and `v` is the faulted value. The property needed for builtins is: given correct args and faulted args where `Forall2 val_compat correct_args faulted_args`, and `builtin correct_args = Some vres_correct`, and `builtin faulted_args = Some vres_faulted`, show `val_compat vres_correct vres_faulted`. For shifts where ltu diverges: correct side returns `Vlong x`, faulted side returns `Vundef`. Need `val_compat (Vlong x) Vundef`. This constructor does NOT exist. Only `val_compat Vundef v` exists. So val_compat is NOT symmetric and shifts ARE problematic in the general form. **However**, the actual tolerant proof uses `match_rs` which guarantees `Val.lessdef` for non-faulted-color registers. Only the faulted-color registers are potentially different. For a safe replicated builtin, each color copy gets its own inputs from its color's registers. The non-faulted copies have `Val.lessdef` inputs (stronger than val_compat). Only the faulted copy has one argument that is val_compat-related. So the actual property needed is: given `Val.lessdef`-related inputs (which is the existing `builtin_function_sem_lessdef`), the output is `Val.lessdef`-related. This is ALREADY PROVED. For the faulted copy, the question is whether its output is val_compat with the non-faulted copy's output. But that's for Phase 3 (tolerant proof). For Phase 1, the semantic property SEMA-01/02/03 should be formulated to match what Phase 3 actually needs. The REQUIREMENTS say `val_compat`, so let's figure out exactly what statement works. After reflection: the correct statement for the semantic property should be the TOTALITY preservation: given well-typed inputs (even faulted), the builtin produces `Some` result. Combined with the fact that results from the same constructor stay in the same constructor. For `mkbuiltin_nNt`: inputs go through `proj_num` which only extracts numerical values (int, long, float, single) and returns Vundef for anything else. The output goes through `inj_num` which always returns the same constructor. So val_compat is trivially preserved for nNt builtins: both sides either (a) both get Vundef (if input constructor changes), which gives val_compat, or (b) both get the same output constructor. For `mkbuiltin_v2t` with wrapped `Val.*` functions: val_compat IS preserved for `addl`, `mull`, `subl` (conditional) based on existing lemmas. For shifts: val_compat is NOT preserved in general. Shifts should use the EXISTS + direction formulation or be excluded.

**FINAL RESOLUTION FOR SHIFTS**: Include shifts in the whitelist with a carefully formulated property. The property for `mkbuiltin_v2t` builtins wrapping `Val.shll` etc. should be: given `val_compat v1 v1'` and `val_compat v2 v2'`, `val_compat (Val.shll v1 v2) (Val.shll v1' v2')` OR `Val.shll v1' v2' = Vundef`. Actually, looking at the `val_compat` constructors again: `val_compat_undef : forall v, val_compat Vundef v`. This means `Vundef` on the LEFT is compatible with anything. If we can arrange that the faulted output is on the RIGHT of val_compat, and the faulted output could be Vundef while the correct output is Vlong, we have `val_compat (Vlong x) Vundef` which is NOT in the constructors. **So shifts genuinely fail the val_compat monotonicity in the direction expected.** I recommend: prove the property for the `mkbuiltin_nNt` class (16 builtins) and `addl`/`mull`/`subl` (3 builtins) which works, and flag shifts (3 builtins) as needing a revised property statement or exclusion. This gives 22 builtins total if shifts work, or 19 if they don't.

Actually wait - let me re-check shifts one more time with concrete values:
- `Val.shll (Vlong 5) (Vint 3)` = `Vlong (shl' 5 3)` (ltu succeeds)
- `Val.shll (Vlong 7) (Vint 99)` = `Vundef` (ltu fails, 99 >= 64)
- `val_compat (Vlong 5) (Vlong 7)` = true
- `val_compat (Vint 3) (Vint 99)` = true
- But `val_compat (Vlong (shl' 5 3)) Vundef` -- need `val_compat (Vlong _) Vundef` which does NOT exist.

So yes, shifts fail. But the requirements include them. This needs to be flagged as a finding.

**AMENDED RESOLUTION**: The 3 shift builtins (`BI_i64_shl`, `BI_i64_shr`, `BI_i64_sar`) DO NOT satisfy `val_compat` monotonicity in the general 2-argument case. They DO satisfy it when the shift amount (second argument) is the same on both sides (which is the `val_compat_shll_imm` pattern). In the tolerant proof's actual usage, the single-fault model means at most one register is faulted. If the shift amount register is faulted, the val_compat direction fails. Options: (1) exclude shifts from whitelist, (2) use a weaker property that suffices for the tolerant proof, (3) prove that the tolerant proof only encounters shifts where the shift amount is not the faulted register. The planner should be aware of this subtlety.

### Anti-Patterns to Avoid

- **Defining classification locally in each consumer:** The whole point of this phase is a SINGLE definition in `common/Builtins.v`. Never duplicate the classification logic in `RTLfault.v`, `RTLtmr.v`, `RTLcolor.v`, etc.
- **Using `Val.lessdef` instead of `val_compat` for the semantic property:** The existing `builtin_function_sem_lessdef` proves `Val.lessdef` monotonicity. This is INSUFFICIENT for the fault model, which uses `val_compat` (a strictly weaker relation). The semantic lemma MUST use `val_compat`.
- **Putting the semantic lemma in `common/Builtins.v`:** The `val_compat` type is defined in `backend/RTLfault.v`. The `common/` directory cannot import from `backend/`. The semantic lemma must live in `backend/RTLfault.v`.
- **Treating all `mkbuiltin_v2t` builtins uniformly:** `addl`, `mull`, `subl` (conditional) have clean `val_compat` proofs, but shifts have the ltu-divergence issue described above. Do not assume they share a proof pattern.

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Bool-to-Prop bridging | Custom lemma patterns | `reflect` type + `destruct (spec ...)` | Standard Coq idiom; 5+ existing uses in codebase |
| Builtin lookup from EF_builtin | Pattern-match on name strings | `lookup_builtin_function name sg` | Already handles all builtin tables; returns `option builtin_function` |
| val_compat for Val.addl | Fresh proof from scratch | Reuse existing `val_compat_addl` from RTLfault.v | Already proved, just needs lifting through mkbuiltin_v2t wrapper |
| val_compat for Val.mull | Fresh proof from scratch | Reuse existing `val_compat_mull` and adapt for `Val.mull'` | `mull'` takes `Vint * Vint -> Vlong`; same pattern as `val_compat_mul` |
| Protocol exclusion check | Ad-hoc string comparisons | `BI_replicate _ => false` in the match | Structural exclusion via the `builtin_function` type |

**Key insight:** Nearly every proof in this phase has an existing analog in the codebase. `is_protectedb_spec` is the template for reflection. `val_compat_addl` is the template for v2t builtins. `is_vote_builtinb_spec` is the template for protocol recognizer reflection.

## Common Pitfalls

### Pitfall 1: val_compat Asymmetry for Shift Builtins
**What goes wrong:** `val_compat (Vlong x) Vundef` is NOT a constructor. Shifts can produce `Vlong` on the correct side and `Vundef` on the faulted side when the shift amount is faulted out of range.
**Why it happens:** `val_compat_undef` only covers `val_compat Vundef v` (Vundef on LEFT), not `val_compat v Vundef` (Vundef on RIGHT). Shifts have a conditional branch (`Int.ltu`) that can diverge between val_compat-related inputs.
**How to avoid:** Either exclude shifts from the whitelist, or formulate a weaker/different property that the tolerant proof can still consume. The planner must make a decision here.
**Warning signs:** Coq `val_compat` inversion/destruct leaving an unprovable goal with `Vlong` vs `Vundef`.

### Pitfall 2: Import Direction Between common/ and backend/
**What goes wrong:** Trying to import `RTLfault` from `common/Builtins.v` creates a circular dependency.
**Why it happens:** `common/Builtins.v` is imported by everything. `backend/RTLfault.v` imports from `common/`. The semantic lemma needs `val_compat` which is in `backend/RTLfault.v`.
**How to avoid:** Place the classification in `common/Builtins.v` and the semantic lemma in `backend/RTLfault.v`. These are two separate deliverables that happen to be in the same phase.
**Warning signs:** `Require Import` failing with "cannot find library".

### Pitfall 3: Protocol Recognizer Migration Breaking Downstream Imports
**What goes wrong:** Moving `is_vote_builtin` etc. from `backend/RTL.v` to `common/Builtins.v` breaks files that import them from `RTL`.
**Why it happens:** 9 files in `backend/` reference these recognizers. They currently get them via `Require Import RTL`.
**How to avoid:** Since `common/Builtins.v` is re-exported via `Require Export` in `common/Builtins.v` (line 22: `Require Export Builtins0 Builtins1 Builtins2`), and `RTL.v` imports `Builtins2`, the definitions would NOT be automatically visible through `RTL.v` unless `Builtins.v` is also imported. Check the import chain. `RTL.v` currently does NOT import `common/Builtins.v` directly. It imports individual files. The migration may need `RTL.v` to re-export the moved definitions, or all 9 consumer files need updated imports.
**Warning signs:** `Error: The reference is_vote_builtin was not found` in downstream files.

### Pitfall 4: BI_subl Conditional Classification
**What goes wrong:** Forgetting the `Archi.ptr64` condition on `BI_subl`, making it unconditionally safe.
**Why it happens:** On `ptr64 = true` architectures, `Val.subl` involves pointer subtraction across blocks, which is UB under faulted inputs.
**How to avoid:** `builtin_can_replicate_bf (BI_standard BI_subl) = negb Archi.ptr64`. Mirror the `is_protectedb Osubl = Archi.ptr64` pattern exactly (line 963 of RTL.v). The reflection lemma must handle the `Archi.ptr64` case split.
**Warning signs:** The reflection proof for `BI_subl` failing because the Boolean value depends on a runtime constant.

### Pitfall 5: Forgetting Platform Builtins in the Match
**What goes wrong:** The `BI_platform` branch of `builtin_can_replicate_bf` is forgotten, returning `false` for `BI_fmin`/`BI_fmax`.
**Why it happens:** Focus on `standard_builtin` cases; platform builtins are in a separate file (`x86/Builtins1.v`).
**How to avoid:** The `builtin_function` type has three constructors: `BI_standard`, `BI_platform`, `BI_replicate`. All three must be matched. For x86, `BI_platform` has `BI_fmin | BI_fmax => true`. For riscV/aarch64, `platform_builtin` is empty, so the match is `match pb with end` (vacuously true, but returns whatever the catch-all is -- use `match pb with end` which Coq handles as exhaustive on empty type).
**Warning signs:** Coq warning about non-exhaustive match, or platform builtins unexpectedly classified as unsafe.

## Code Examples

### Complete Classification Definition
```coq
(* In common/Builtins.v, after builtin_function definition *)

Definition builtin_can_replicate_bf (b: builtin_function) : bool :=
  match b with
  | BI_standard sb =>
      match sb with
      (* mkbuiltin_n1t: pure numerical, 1 arg, total *)
      | BI_fabs | BI_fabsf | BI_fsqrt | BI_negl
      | BI_i16_bswap | BI_i32_bswap | BI_i64_bswap => true
      (* mkbuiltin_n2t: pure numerical, 2 args, total *)
      | BI_i64_umulh | BI_i64_smulh => true
      (* mkbuiltin_n1t: float/int conversions, total *)
      | BI_i64_stod | BI_i64_utod | BI_i64_stof | BI_i64_utof => true
      (* mkbuiltin_v2t: val-level, total, val_compat preserving *)
      | BI_addl | BI_mull => true
      (* mkbuiltin_v2t: conditional on architecture *)
      | BI_subl => negb Archi.ptr64
      (* mkbuiltin_v2t: shifts -- see Pitfall 1 re: val_compat *)
      | BI_i64_shl | BI_i64_shr | BI_i64_sar => true
      (* Excluded: partial, unreachable, select *)
      | _ => false
      end
  | BI_platform pb =>
      match pb with
      | BI_fmin | BI_fmax => true  (* mkbuiltin_n2t, x86 only *)
      end
  | BI_replicate _ => false  (* Protocol builtins: never replicate *)
  end.

Definition builtin_can_replicate (ef: external_function) : bool :=
  match ef with
  | EF_builtin name sg =>
      match lookup_builtin_function name sg with
      | Some bf => builtin_can_replicate_bf bf
      | None => false
      end
  | _ => false
  end.

Definition builtin_can_fault (ef: external_function) : bool :=
  builtin_can_replicate ef.
```

### Reflection Lemma Pattern
```coq
(* Following is_protectedb_spec pattern from RTL.v line 970 *)

Lemma builtin_can_replicate_bf_true_spec (b: builtin_function) :
  builtin_can_replicate_bf b = true ->
  (* Property: b is not a protocol builtin, not partial, etc. *)
  match b with BI_replicate _ => False | _ => True end.
Proof. destruct b as [sb|pb|rb]; simpl; try destruct sb; try destruct rb; auto; discriminate. Qed.

(* Or a reflect-style lemma: *)
(* Define an inductive if needed, or just use the Boolean directly *)
```

### val_compat Lemma for mkbuiltin_nNt (Pattern)
```coq
(* In backend/RTLfault.v *)

(* Key insight: mkbuiltin_nNt builtins go through proj_num/inj_num.
   proj_num extracts the numerical value or returns the default.
   inj_num wraps in the appropriate constructor.
   Under val_compat, inputs of the same constructor give same-constructor outputs. *)

Lemma val_compat_proj_num (t: typ) (v1 v2: val) :
  val_compat v1 v2 ->
  forall (A: Type) (k0: A) (k1 k2: valty t -> A) (R: A -> A -> Prop),
  R k0 k0 ->
  (forall x, R (k1 x) (k2 x)) ->
  R (proj_num t k0 v1 k1) (proj_num t k0 v2 k2).
Proof.
  intros Hcompat; inv Hcompat; destruct t; simpl; auto.
Qed.
```

### val_compat Lemma for BI_addl (Lifting Pattern)
```coq
(* In backend/RTLfault.v *)

(* BI_addl semantics: mkbuiltin_v2t Xlong Val.addl _ _ *)
(* bs_sem = fun vl => match vl with v1 :: v2 :: nil => Some (Val.addl v1 v2) | _ => None end *)

Lemma builtin_sem_val_compat_addl vargs1 vargs2 vres1 :
  Forall2 val_compat vargs1 vargs2 ->
  standard_builtin_sem BI_addl vargs1 = Some vres1 ->
  exists vres2,
    standard_builtin_sem BI_addl vargs2 = Some vres2 /\
    val_compat vres1 vres2.
Proof.
  intros Hcompat Hsem.
  simpl in *.
  destruct vargs1 as [|v1 [|v2 [|]]]; try discriminate.
  inv Hcompat. inv H3.
  inv Hsem.
  eexists; split; [reflexivity|].
  apply val_compat_addl; auto.
Qed.
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| All non-protocol builtins are White-only | Still current (this phase changes it) | N/A | This is the problem being solved |
| `is_protected` only for operations | Will add `builtin_can_replicate` for builtins | This phase | Enables TMR replication of safe builtins |
| Protocol recognizers in `backend/RTL.v` | Will move to `common/Builtins.v` | This phase | Consolidates all builtin classification |
| `Val.lessdef` monotonicity only | Will add `val_compat` monotonicity | This phase | Required by fault model |

## Open Questions

1. **Shift builtins and val_compat monotonicity**
   - What we know: `val_compat (Vlong x) Vundef` is NOT a constructor. Shifts can produce `Vlong` on one side and `Vundef` on the other when the shift amount is faulted out of range.
   - What's unclear: Whether the tolerant proof actually needs the general val_compat property for shifts, or whether a weaker formulation suffices (e.g., only considering the case where the shift amount is not the faulted register).
   - Recommendation: Include shifts in the whitelist definition but formulate `builtin_sem_val_compat` with an EXISTS pattern that accounts for totality. If the proof in Phase 3 needs strengthening, address it then. Alternatively, flag shifts for removal if the Phase 1 proof doesn't close.

2. **Protocol recognizer migration scope**
   - What we know: 9 files in `backend/` use `is_vote_builtin` etc. The import chain from `RTL.v` does not automatically re-export definitions moved to `common/Builtins.v`.
   - What's unclear: Whether to add `Require Export Builtins` to `RTL.v` or update all 9 consumer files individually.
   - Recommendation: Add `Require Export Builtins` to `backend/RTL.v` (or keep the definitions there and add thin wrappers). This minimizes downstream churn. The moved definitions should still be in scope via the export chain.

3. **Exact val_compat property statement**
   - What we know: The requirements say "val_compat monotonicity". The tolerant proof uses `match_rs` (Val.lessdef + one faulted-color exception). The actual statement needs to be compatible with Phase 3's proof structure.
   - What's unclear: The precise Coq statement that serves all consumers.
   - Recommendation: Use the pattern from `eval_operation_val_compat` (line 692 of RTLfault.v): given `Forall2 val_compat args1 args2` and `sem args1 = Some vres1` and `sem args2 = Some vres2`, conclude `val_compat vres1 vres2`. For total builtins, the "sem args2 = Some vres2" is guaranteed by totality so it can be derived rather than assumed.

## Validation Architecture

### Test Framework
| Property | Value |
|----------|-------|
| Framework | Coq proof checker (coqc) + `make check-admitted` |
| Config file | `_CoqProject` (includes `-R` flags for all directories) |
| Quick run command | `make common/Builtins.vo` or `make backend/RTLfault.vo` |
| Full suite command | `make proof` (compiles all .v files) |

### Phase Requirements to Test Map
| Req ID | Behavior | Test Type | Automated Command | File Exists? |
|--------|----------|-----------|-------------------|-------------|
| CLAS-01 | `builtin_can_replicate_bf` defined and returns correct results | unit (Coq type-check) | `make common/Builtins.vo` | File exists, definitions to be added |
| CLAS-02 | `builtin_can_replicate` dispatches via `lookup_builtin_function` | unit (Coq type-check) | `make common/Builtins.vo` | File exists, definitions to be added |
| CLAS-03 | `builtin_can_fault` aligned with `builtin_can_replicate` | unit (Coq type-check) | `make common/Builtins.vo` | File exists, definitions to be added |
| CLAS-04 | Reflection lemmas proved | unit (Coq proof-check) | `make common/Builtins.vo` | File exists, lemmas to be added |
| CLAS-05 | Protocol recognizers moved and accessible | integration (downstream builds) | `make backend/RTLcolor.vo backend/RTLcolorcheck.vo backend/Novotes.vo` | Files exist, imports to be updated |
| CLAS-06 | Platform builtins accommodated | unit (Coq type-check) | `make common/Builtins.vo` | File exists |
| CLAS-07 | `BI_subl` conditional on `Archi.ptr64` | unit (Coq type-check + reflection proof) | `make common/Builtins.vo` | File exists |
| SEMA-01 | val_compat for mkbuiltin_nNt builtins | unit (Coq proof-check) | `make backend/RTLfault.vo` | File exists, lemma to be added |
| SEMA-02 | val_compat for mkbuiltin_v2t builtins | unit (Coq proof-check) | `make backend/RTLfault.vo` | File exists, lemma to be added |
| SEMA-03 | Property uses val_compat not Val.lessdef | unit (Coq proof-check) | `make backend/RTLfault.vo` | File exists, lemma to be added |

### Sampling Rate
- **Per task commit:** `make common/Builtins.vo` and/or `make backend/RTLfault.vo` (< 60 seconds each)
- **Per wave merge:** `make common/Builtins.vo backend/RTLfault.vo backend/RTLcolor.vo backend/RTLcolorcheck.vo backend/Novotes.vo backend/RTLtolerant.vo` (verify no downstream breakage)
- **Phase gate:** Full `make proof` + `make check-admitted` before `/gsd:verify-work`

### Wave 0 Gaps
- None -- existing build infrastructure (`make *.vo`) covers all phase requirements. No additional test framework or config needed.

## Sources

### Primary (HIGH confidence)
- `common/Builtins.v` -- `builtin_function` type, `lookup_builtin_function`, `builtin_function_sem_lessdef`, `builtin_function_sem_inject`
- `common/Builtins0.v` -- `standard_builtin_sem`, all `mkbuiltin_*` constructors, `proj_num`/`inj_num` infrastructure
- `x86/Builtins1.v` -- `platform_builtin` type: `BI_fmin`, `BI_fmax` (both `mkbuiltin_n2t`)
- `riscV/Builtins1.v`, `aarch64/Builtins1.v` -- empty `platform_builtin` types (vacuously safe)
- `backend/Builtins2.v` -- `replicate_builtin` type, vote/smove/check semantics
- `backend/RTL.v` lines 906-1004 -- `is_protected`/`is_protectedb`/`is_protectedb_spec` pattern (exact template)
- `backend/RTL.v` lines 1063-1265 -- protocol recognizers (to be migrated)
- `backend/RTLfault.v` lines 21-27 -- `val_compat` definition
- `backend/RTLfault.v` lines 256-505 -- existing `val_compat_*` lemmas (proof templates)
- `backend/RTLfault.v` lines 692-757 -- `eval_operation_val_compat` (statement template)
- `backend/RTLcolor.v` lines 114-204 -- `wc_instruction` constructors (downstream consumer)
- `backend/RTLcolorcheck.v` lines 135-220 -- `check_col_instr` for builtins (downstream consumer)
- `backend/RTLtolerant.v` lines 904-972 -- `exec_Ibuiltin` case (downstream consumer)
- `common/Values.v` -- `Val.addl`, `Val.subl`, `Val.mull'`, `Val.shll`, `Val.shrlu`, `Val.shrl` definitions
- `.planning/research/SUMMARY.md` -- prior research summary

### Secondary (MEDIUM confidence)
- `.planning/REQUIREMENTS.md` -- requirement definitions and phase assignments
- `.planning/ROADMAP.md` -- phase structure and success criteria

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH -- all patterns directly observed in codebase with 5+ prior instances
- Architecture: HIGH -- file layout follows existing `common/` vs `backend/` separation; import direction verified
- Pitfalls: HIGH -- shift builtin issue discovered through concrete analysis of `val_compat` constructors; import chain issue verified by reading actual `Require` statements
- Semantic property: MEDIUM -- the `mkbuiltin_nNt` proof is straightforward (pure numerical); the `mkbuiltin_v2t` proof for `addl`/`mull`/`subl` is supported by existing lemmas; shift builtins have a genuine open question

**Research date:** 2026-03-14
**Valid until:** Indefinite (Coq codebase; no external dependency drift)
