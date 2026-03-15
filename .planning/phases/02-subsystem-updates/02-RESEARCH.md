# Phase 2: Subsystem Updates - Research

**Researched:** 2026-03-14
**Domain:** TMR pass, color system, and faulty semantics updates for safe builtins in CompCert
**Confidence:** HIGH

## Summary

Phase 2 applies the shared builtin classification (established in Phase 1) across three subsystems in parallel: the TMR pass (`RTLtmr.v` / `RTLtmrspec.v` / `RTLtmrproof.v`), the color system (`RTLcolor.v` / `RTLcolorcheck.v` / `RTLinfercolor.ml`), and the faulty semantics (`RTLfault.v`). Each subsystem needs to distinguish safe (replicable) builtins from White-only builtins, using the `builtin_can_replicate` predicate from `common/Builtins.v`.

The key structural insight is that safe builtins should be treated identically to safe `Iop` instructions in each subsystem. The existing codebase already has the `Iop` safe/protected split working across all three subsystems, so the changes follow a clear pattern: add a parallel case for `Ibuiltin` that mirrors `Iop_safe` handling. The RTLfault.v change is a one-liner. The color system changes are straightforward pattern additions. The TMR pass + spec + proof changes are the most involved but follow established patterns closely.

**Primary recommendation:** Split into three parallel plans: (1) TMR pass with spec and proof, (2) color system (spec + checker + oracle), (3) faulty semantics. The faulty semantics change is trivial and could be combined with another plan, but keeping it separate maintains clean phase structure. Given coarse granularity, combining faulty semantics with the color system plan is preferable.

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|-----------------|
| TMR-01 | `transf_instr` emits per-color copies for safe builtins | Mirror `Iop` safe branch; use `builtin_can_replicate ef` to gate, remap args via `map_builtin_arg`, remap res via `map_builtin_res` |
| TMR-02 | White-only builtins keep current vote-then-run-once path | Existing catch-all `_ =>` branch already handles this; just ensure new safe branch only fires when `builtin_can_replicate ef = true` |
| TMR-03 | Protocol builtins retain dedicated handling | Protocol builtins are `BI_replicate`, for which `builtin_can_replicate_bf` returns `false`, so they never enter safe branch |
| TMR-04 | Safe builtin arg/result remapping uses `map_builtin_arg`/`map_builtin_res` | These exist in `common/AST.v`; for `BA r` args they just remap registers, exactly what's needed |
| TMR-05 | `match_Ibuiltin_safe` case added to `RTLtmrspec.v` | New constructor parallel to `match_Iop_safe` with `rm_l` on args and three code entries for green/blue/regular copies |
| TMR-06 | TMR proof generalized with safe-builtin case | New case in `exec_Ibuiltin` handler parallel to safe Iop; uses `eval_builtin_arg` remapping facts |
| COLR-01 | `wc_Ibuiltin_safe` rule in `RTLcolor.v` | New constructor parallel to `wc_Iop_safe`: `builtin_can_replicate ef = true`, `is_basic (col succ res)`, all args same color as res, preservation for non-arg/res |
| COLR-02 | `check_col_instr` accepts replicated safe builtins | Add `builtin_can_replicate ef` check before the generic else branch in the Ibuiltin case, mirror safe Iop checker logic |
| COLR-03 | Oracle assigns basic colors to safe builtins | Modify `Ibuiltin'` case in `instr_constraints` to use safe-Iop-style constraints when `builtin_can_replicate ef = true` |
| COLR-04 | Non-replicable builtins remain White-only | Existing else branch already forces White; the new safe branch is gated by `builtin_can_replicate` |
| FALT-01 | `zap_allowed` returns `builtin_can_fault ef` for `Ibuiltin` | Change `Ibuiltin _ _ _ _ => False` to `Ibuiltin ef _ _ _ => builtin_can_fault ef` |
| FALT-02 | Protocol and White-only builtins remain non-faultable | `builtin_can_fault = builtin_can_replicate`, which returns `false` for protocol builtins and unknown externals |
| INTG-01 | `RTLtmr.vo` builds | Verified by `make backend/RTLtmr.vo` |
| INTG-02 | `RTLtmrproof.vo` builds | Verified by `make backend/RTLtmrproof.vo` |
| INTG-03 | `RTLcolor.vo` builds | Verified by `make backend/RTLcolor.vo` |
| INTG-04 | `RTLcolorcheck.vo` builds | Verified by `make backend/RTLcolorcheck.vo` |
</phase_requirements>

## Standard Stack

### Core
| Library/File | Purpose | Why Standard |
|-------------|---------|--------------|
| `common/Builtins.v` | `builtin_can_replicate`, `builtin_can_fault`, protocol recognizers | Phase 1 output; single source of truth for classification |
| `common/AST.v` | `map_builtin_arg`, `map_builtin_res` | Standard CompCert utilities for remapping builtin arg/res structures |
| `common/Events.v` | `eval_builtin_arg`, `eval_builtin_args`, `external_call` | Standard CompCert builtin evaluation infrastructure |
| `backend/RTL.v` | `instruction`, `regs_of_builtin_args`, `args_of_instruction` | Core RTL definitions |

### Supporting
| File | Purpose | When to Use |
|------|---------|-------------|
| `backend/RTLreplicateSpecCommon.v` | Shared spec utilities (`smoveR`, `maj_voteR`, etc.) | TMR spec and proof work |
| `backend/RTLgen.v` | State+error monad (`mon`, `reserve_instr`, `update_instr`) | TMR pass transformation code |
| `backend/RTLtyping.v` | `regenv`, `wt_function`, `wt_regset` | TMR proof well-typedness |
| `backend/ProofLiveness.v` | Liveness analysis for color system | Color spec/checker |

## Architecture Patterns

### Pattern 1: Safe Iop Triplication (existing pattern to mirror)

**What:** For non-protected `Iop op args res succ`, the TMR pass emits three copies: one with green-mapped args/res, one with blue-mapped args/res, and the original. The spec has `match_Iop_safe` with `rm_l` relating the three arg lists. The color spec has `wc_Iop_safe` requiring `is_basic (col succ res)` and all args matching the result color.

**When to use:** Safe builtins must follow this exact same pattern.

**TMR pass code (existing Iop safe branch, RTLtmr.v:197-209):**
```coq
(* Safe Iop: emit green copy at pc, blue at n1, original at n2 *)
do n1 <- reserve_instr;
do n2 <- reserve_instr;
do _ <- update_instr pc
         (Iop op (List.map (fun arg => fst (rm # arg)) args)
            (fst (rm # dst)) n1);
do _ <- update_instr n1
         (Iop op (List.map (fun arg => snd (rm # arg)) args)
            (snd (rm # dst)) n2);
update_instr n2 instr
```

**Safe builtin analog:** The same pattern but using `Ibuiltin ef (map (map_builtin_arg fst_rm) bargs) (map_builtin_res fst_rm bres) n1` etc. IMPORTANT: Only `BA r` arguments will typically appear for safe builtins, but using `map_builtin_arg` handles all cases correctly including `BA_splitlong`. The result MUST be `BR r` for the common case; `BR_none` and `BR_splitlong` need consideration.

### Pattern 2: Color Spec Builtin Case Split (existing)

**What:** The `wc_instruction` inductive in `RTLcolor.v` already has five Ibuiltin cases: `wc_Ibuiltin_smove_green`, `wc_Ibuiltin_smove_blue`, `wc_Ibuiltin_vote`, and the generic `wc_Ibuiltin`. The generic case requires all args White and result White. A new `wc_Ibuiltin_safe` case goes before the generic case.

**Structure:**
```coq
| wc_Ibuiltin_safe : forall ef bargs bres succ,
    builtin_can_replicate ef = true ->
    ~ is_green_smove_builtin ef ->    (* discharge overlap *)
    ~ is_blue_smove_builtin ef ->
    ~ is_vote_builtin ef ->
    (* mirror wc_Iop_safe constraints *)
    ...
    wc_instruction pc (Ibuiltin ef bargs bres succ)
```

**Key insight:** The overlap exclusions (`~ is_green_smove_builtin ef` etc.) are provably true because `builtin_can_replicate_bf (BI_replicate _) = false`, but keeping them explicit makes the checker proof simpler. Actually, since `builtin_can_replicate` returns `false` for all protocol builtins (they are `BI_replicate` variants), the `builtin_can_replicate ef = true` hypothesis alone is sufficient to exclude smove/vote/check. The overlap exclusions for the generic `wc_Ibuiltin` case need updating: add `builtin_can_replicate ef = false` (or `~ builtin_can_replicate ef = true`).

### Pattern 3: Checker Case Priority (existing)

**What:** In `RTLcolorcheck.v`, the `check_col_instr` function checks builtins in priority order: green_smove > blue_smove > vote > else. The safe builtin check needs to be inserted before the generic else:

```
green_smove > blue_smove > vote > safe_builtin > generic_white
```

**Implementation:** Add `if builtin_can_replicate ef then ... else` wrapping the generic case. The `builtin_can_replicate` function is defined in `common/Builtins.v` and operates on `external_function`, so it's directly usable in the checker.

### Pattern 4: Oracle Constraint Generation (existing)

**What:** In `RTLinfercolor.ml`, the `instr_constraints` function generates union-find constraints per instruction. The `Ibuiltin'` case currently has: green_smove > blue_smove > vote > else (force White). The safe builtin case should mirror the `Iop'` safe case:

```ocaml
(* For safe builtins, constrain args to result color like safe Iop *)
let res_color = get succ_col res in
List.iter (fun arg -> union (get col arg) res_color) arg_regs;
(* preserve non-arg/res registers *)
```

### Anti-Patterns to Avoid

- **Do not add a `Require Import Builtins` to RTLtmrspec.v unless needed:** The spec file needs `builtin_can_replicate` only if it appears in the match relation. Check if `RTLtmr.v` already imports Builtins (it imports `Builtins2` which re-exports from `Builtins`). Actually, `common/Builtins.v` does `Require Export Builtins0 Builtins1 Builtins2`, so importing `Builtins` gives everything. The spec file may need its own import if it references `builtin_can_replicate` directly.

- **Do not hand-roll `builtin_arg` remapping:** Use `AST.map_builtin_arg` with appropriate projection function, not manual pattern matching on `BA`/`BA_int`/etc.

- **Do not break the generic Ibuiltin case for non-replicable builtins:** The existing `wc_Ibuiltin` constructor and the generic else branch must continue to handle all builtins for which `builtin_can_replicate ef = false` AND that are not protocol builtins. The negation premise on the generic case may need updating.

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Remapping builtin args | Manual BA/BA_int/BA_long pattern match | `AST.map_builtin_arg (fun r => fst (rm # r))` | Handles all 11 constructors automatically |
| Remapping builtin result | Manual BR/BR_none/BR_splitlong match | `AST.map_builtin_res (fun r => fst (rm # r))` | Handles splitlong correctly |
| Checking if builtin is safe | String matching on builtin names | `builtin_can_replicate ef` from Builtins.v | Central classification, already proved correct |
| Protocol exclusion proofs | Case-by-case name analysis | `builtin_can_replicate_bf_false_replicate` lemma | Already proved in Phase 1 |

## Common Pitfalls

### Pitfall 1: Builtin Argument Structure Mismatch
**What goes wrong:** Safe builtins use `builtin_arg` (list of `BA r`, `BA_int n`, etc.) not plain `list reg`. The remapping must handle the full `builtin_arg` type, not just `BA r`.
**Why it happens:** `Iop` uses plain `list reg` for args, so naively copying the Iop pattern leads to type errors.
**How to avoid:** Use `map_builtin_arg` for remapping. For the spec (`rm_l` analogue), define a relation over `list (builtin_arg reg)` that relates green/blue/original arg lists.
**Warning signs:** Type errors mentioning `builtin_arg reg` vs `list reg`.

### Pitfall 2: Generic wc_Ibuiltin Overlap
**What goes wrong:** After adding `wc_Ibuiltin_safe`, the generic `wc_Ibuiltin` case may still accept safe builtins (since its negation premises only exclude protocol builtins). This creates ambiguity that makes the checker soundness proof harder.
**Why it happens:** The generic case currently only excludes `is_green_smove_builtin`, `is_blue_smove_builtin`, `is_vote_builtin`. Safe builtins are none of these.
**How to avoid:** Add `builtin_can_replicate ef = false` (or the negation) as a premise to the generic `wc_Ibuiltin` case. This ensures the cases are mutually exclusive.
**Warning signs:** The checker soundness proof (`check_col_instr_sound`) gets stuck because it cannot determine which constructor to apply.

### Pitfall 3: Builtin Result Not Always BR
**What goes wrong:** Some builtins have `BR_none` or `BR_splitlong` results. The safe builtin triplication assumes `BR r` for copy-to-shadows.
**Why it happens:** The safe builtins classified by `builtin_can_replicate_bf` all have single-register results (`BR`), but the Coq type system doesn't enforce this at the type level.
**How to avoid:** In the TMR pass, the safe builtin branch only fires when `res_of_instruction` returns `Some r` (i.e., `BR r`). For `BR_none`, the instruction has no result, so no shadows needed -- but this case shouldn't arise for any builtin with `builtin_can_replicate = true`. For `BR_splitlong`, same consideration. The match spec and proof should include a premise that `bres = BR res1` for safe builtins.
**Warning signs:** `res_of_instruction` returning `None` for a builtin with `BR_none` result.

### Pitfall 4: Eval_builtin_args Remapping in Proof
**What goes wrong:** The TMR proof for `exec_Ibuiltin` currently uses `eval_builtin_args_proper` to show that voting arguments produces the same values. For the safe builtin case, we instead need to show that remapped arguments (green/blue world) evaluate to the same values as the original, similar to `match_regs_1_2_eval_operation`.
**Why it happens:** The proof pattern is different from the White-only case. In the safe case, we're showing three independent evaluations produce the same result; in the White case, we're showing voted arguments + one evaluation produce the same result.
**How to avoid:** Develop a lemma analogous to `match_regs_1_2_eval_operation` but for `eval_builtin_args` with `map_builtin_arg`. The key insight: for `BA r` arguments, `eval_builtin_arg` just reads the register, so remapping `r` to `fst (rm # r)` and reading from `rs'` (where `rs' # (fst (rm # r)) = rs # r` by `match_regsets`) gives the same value.
**Warning signs:** Getting stuck on `eval_builtin_args` goals with remapped argument lists.

### Pitfall 5: Oracle Safe Builtin Detection in OCaml
**What goes wrong:** The oracle (`RTLinfercolor.ml`) needs to call `builtin_can_replicate` (an extracted Coq function) to determine if a builtin is safe. But the extraction may produce an unwieldy function.
**Why it happens:** `builtin_can_replicate` calls `lookup_builtin_function` which does string comparisons across all builtin tables.
**How to avoid:** The extracted `Builtins.builtin_can_replicate` function should be directly usable. Import it and call it in the `Ibuiltin'` case. Since the oracle is unverified OCaml, correctness doesn't depend on it -- only the checker matters.
**Warning signs:** OCaml compilation errors from extracted code, or the oracle failing to assign basic colors.

### Pitfall 6: zap_allowed Changing from Prop to bool
**What goes wrong:** `zap_allowed` currently returns `Prop` (`False` for Ibuiltin). Changing it to `builtin_can_fault ef` returns `bool` which is a `Prop` via coercion but has different proof obligations.
**Why it happens:** `False` is a `Prop`, `builtin_can_fault ef` is `bool`. The `bool -> Prop` coercion treats `true` as `True` and `false` as `False`.
**How to avoid:** Actually, looking at the code more carefully, `zap_allowed` returns `Prop`. The `~ is_protected op` case returns `Prop` via the negation. For `Ibuiltin`, we need to return a `Prop` that is `True` when `builtin_can_fault ef = true` and `False` when `builtin_can_fault ef = false`. Options: (a) `builtin_can_fault ef = true` (a Prop), or (b) `Is_true (builtin_can_fault ef)` which is the coercion, or (c) define it directly. The simplest approach: `if builtin_can_fault ef then True else False`. Or just use the Coq `bool -> Prop` coercion: `Is_true (builtin_can_fault ef)`.
**Warning signs:** Type mismatch between `Prop` and `bool` in `zap_allowed`.

## Code Examples

### TMR Pass: Safe Builtin Branch in transf_instr

```coq
(* In the Ibuiltin case of transf_instr, add before the generic catch-all: *)
| Ibuiltin ef bargs bres succ =>
    if builtin_can_replicate ef then
      (* Safe builtin: emit three copies like safe Iop *)
      match bres with
      | BR res =>
          let (res2, res3) := rm # res in
          do n1 <- reserve_instr;
          do n2 <- reserve_instr;
          do _ <- update_instr pc
                   (Ibuiltin ef
                      (List.map (map_builtin_arg (fun r => fst (rm # r))) bargs)
                      (BR res2) n1);
          do _ <- update_instr n1
                   (Ibuiltin ef
                      (List.map (map_builtin_arg (fun r => snd (rm # r))) bargs)
                      (BR res3) n2);
          update_instr n2 instr
      | _ =>
          (* BR_none or BR_splitlong: fall through to generic *)
          do n <- maj_vote_regs re rm (dedup (args_of_instruction instr)) pc;
          match res_of_instruction instr, succ_of_instruction instr with
          | Some res, Some succ' =>
              do m <- reserve_instr;
              do _ <- copy_to_shadows rm (re res) res m succ';
              update_instr n (change_succ instr m)
          | _, _ => update_instr n instr
          end
      end
    else
      (* Non-replicable: vote args, run once, copy result *)
      do n <- maj_vote_regs re rm (dedup (args_of_instruction instr)) pc;
      match res_of_instruction instr, succ_of_instruction instr with
      | Some res, Some succ' =>
          do m <- reserve_instr;
          do _ <- copy_to_shadows rm (re res) res m succ';
          update_instr n (change_succ instr m)
      | _, _ => update_instr n instr
      end
```

### TMR Spec: match_Ibuiltin_safe Constructor

```coq
| match_Ibuiltin_safe :
  forall ef bargs1 bargs2 bargs3 res1 res2 res3 n1 n2 succ
    (CAN_REP : builtin_can_replicate ef = true)
    (BARGS : rm_l_bargs rm bargs1 bargs2 bargs3)  (* new relation *)
    (RM_RES : rm !! res1 = (res2, res3))
    (PC : c ! pc = Some (Ibuiltin ef bargs2 (BR res2) n1))
    (N1 : c ! n1 = Some (Ibuiltin ef bargs3 (BR res3) n2))
    (N2 : c ! n2 = Some (Ibuiltin ef bargs1 (BR res1) succ)),
    match_instr re rm c pc (Ibuiltin ef bargs1 (BR res1) succ)
```

Note: `rm_l_bargs` is a new relation over `list (builtin_arg reg)` analogous to `rm_l` over `list reg`. For `BA r` arguments, it requires `rm !! r = (r2, r3)` and maps to `BA r2` / `BA r3`. For non-register args (BA_int, BA_long, etc.), all three lists carry the same argument unchanged.

### Color Spec: wc_Ibuiltin_safe Constructor

```coq
| wc_Ibuiltin_safe : forall ef bargs bres succ,
    builtin_can_replicate ef = true ->
    (* Result must be BR with basic color *)
    forall res, bres = BR res ->
    is_basic (col succ res) ->
    (* All register args share result color *)
    Forall (builtin_arg_forall (fun r => col pc r = col succ res)) bargs ->
    (* Non-arg/res registers preserved *)
    Regset.For_all (fun r =>
      ~ Exists (in_builtin_arg r) bargs ->
      r <> res ->
      col pc r = col succ r) (live !! pc) ->
    wc_instruction pc (Ibuiltin ef bargs (BR res) succ)
```

### Faulty Semantics: Updated zap_allowed

```coq
Definition zap_allowed (i : instruction) : Prop :=
  match i with
  | Iop op _ _ _ => ~ is_protected op
  | Iload _ _ _ _ _ => False
  | Istore _ _ _ _ _ => False
  | Icall _ _ _ _ _ => False
  | Itailcall _ _ _ => False
  | Ibuiltin ef _ _ _ => builtin_can_fault ef = true
  | _ => True
  end.
```

### Color Checker: Safe Builtin Check

```coq
(* In check_col_instr, Ibuiltin case, after vote check, before generic: *)
else if builtin_can_replicate ef then
  match bres with
  | BR res =>
      is_basicb (col succ res) &&
      forallb (builtin_arg_forallb (fun r => col pc r =? col succ res)) bargs &&
      Regset.for_all
        (fun r => existsb (in_builtin_argb r) bargs ||
                  Pos.eqb r res ||
                  (col pc r =? col succ r))
        (live !! pc)
  | _ => false  (* safe builtins must have BR result for replication *)
  end
else
  (* existing generic White-only check *)
```

### Oracle: Safe Builtin Constraints

```ocaml
(* In instr_constraints, Ibuiltin' case, add before generic else: *)
else if Builtins.builtin_can_replicate ef then
  match bres with
  | BR res ->
     let succ_col = Array.get cols succ in
     let res_color = get succ_col res in
     let arg_regs = List.concat_map regs_of_builtin_arg bargs in
     List.iter (fun arg -> union (get col arg) res_color) arg_regs;
     List.iter (fun r ->
         if not (List.mem r arg_regs || r = res) then
           union (get col r) (get succ_col r)
       ) live
  | _ ->
     (* Fall through to generic White handling *)
     ...
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| All builtins White-only, non-faultable | Safe builtins replicated like Iop | Phase 2 (this work) | Expands fault tolerance coverage to ~22 builtins |
| Protocol recognizers in RTL.v | Protocol recognizers in Builtins.v | Phase 1 (01-02) | Cleaner imports, single location |
| No shared classification | `builtin_can_replicate` in Builtins.v | Phase 1 (01-01) | Single source of truth |

## Open Questions

1. **rm_l_bargs relation design**
   - What we know: Need a relation over `list (builtin_arg reg)` that relates green/blue/original arg lists. For `BA r` args, maps registers through `rm`. For constant args (`BA_int`, `BA_long`, etc.), all three copies are identical.
   - What's unclear: Whether to define a new inductive `rm_l_bargs` or use `Forall3` with a per-element relation. Also whether `BA_splitlong` and `BA_addptr` need register remapping (they do, recursively).
   - Recommendation: Define `rm_builtin_arg` inductively relating single `builtin_arg reg` triples, then lift to lists. This mirrors the existing `rm_l` / `rm_l_map_rm` pattern.

2. **Proof effort for eval_builtin_args remapping**
   - What we know: Need to show that `eval_builtin_args` with remapped args in `rs'` produces the same values as with original args in `rs`, given `match_regsets`. For `BA r`, this is just a register lookup. For compound args (`BA_splitlong`, `BA_addptr`), it's recursive.
   - What's unclear: Whether existing lemmas (`eval_builtin_args_proper`, etc.) can be reused directly or need extension.
   - Recommendation: Write a custom `eval_builtin_args_map` lemma. The structure parallels `match_regs_1_2_eval_operation` but for the `builtin_arg` evaluator.

3. **Generic wc_Ibuiltin premise update**
   - What we know: The generic `wc_Ibuiltin` case needs to exclude safe builtins to maintain mutual exclusivity with `wc_Ibuiltin_safe`.
   - What's unclear: Best way to express the exclusion -- `builtin_can_replicate ef = false` or `~ (builtin_can_replicate ef = true)`.
   - Recommendation: Use `builtin_can_replicate ef = false` for boolean definitional equality, which simplifies checker soundness proofs. This is the same pattern used for `is_protectedb`.

## Validation Architecture

### Test Framework
| Property | Value |
|----------|-------|
| Framework | Coq proof checker (coqc) + make |
| Config file | `Makefile`, `_CoqProject` |
| Quick run command | `make backend/RTLtmr.vo` (single file) |
| Full suite command | `make -j$(nproc) all` |

### Phase Requirements -> Test Map
| Req ID | Behavior | Test Type | Automated Command | File Exists? |
|--------|----------|-----------|-------------------|-------------|
| TMR-01 | transf_instr emits per-color builtin copies | proof/build | `make backend/RTLtmr.vo` | yes (modify) |
| TMR-02 | White-only path unchanged | proof/build | `make backend/RTLtmr.vo` | yes (verify no regression) |
| TMR-03 | Protocol builtins unchanged | proof/build | `make backend/RTLtmr.vo` | yes (verify no regression) |
| TMR-04 | map_builtin_arg/res used | code review | Manual | N/A |
| TMR-05 | match_Ibuiltin_safe in spec | proof/build | `make backend/RTLtmrspec.vo` | yes (modify) |
| TMR-06 | TMR proof safe builtin case | proof/build | `make backend/RTLtmrproof.vo` | yes (modify) |
| COLR-01 | wc_Ibuiltin_safe rule | proof/build | `make backend/RTLcolor.vo` | yes (modify) |
| COLR-02 | checker accepts safe builtins | proof/build | `make backend/RTLcolorcheck.vo` | yes (modify) |
| COLR-03 | oracle infers basic colors | build/test | `make ccomp && ./ccomp test.c -tmr` | yes (modify) |
| COLR-04 | non-replicable White-only | proof/build | `make backend/RTLcolorcheck.vo` | yes (verify) |
| FALT-01 | zap_allowed relaxed | proof/build | `make backend/RTLfault.vo` | yes (modify) |
| FALT-02 | protocol non-faultable | proof/build | `make backend/RTLfault.vo` | yes (verify) |
| INTG-01 | RTLtmr.vo builds | build | `make backend/RTLtmr.vo` | yes |
| INTG-02 | RTLtmrproof.vo builds | build | `make backend/RTLtmrproof.vo` | yes |
| INTG-03 | RTLcolor.vo builds | build | `make backend/RTLcolor.vo` | yes |
| INTG-04 | RTLcolorcheck.vo builds | build | `make backend/RTLcolorcheck.vo` | yes |

### Sampling Rate
- **Per task commit:** `make backend/{modified_file}.vo`
- **Per wave merge:** `make -j$(nproc) proof` (full proof compilation)
- **Phase gate:** All four .vo files build + `make ccomp` succeeds

### Wave 0 Gaps
None -- existing build infrastructure covers all phase requirements. All files to be modified already exist and build.

## Sources

### Primary (HIGH confidence)
- Direct code analysis of `backend/RTLtmr.v` (lines 179-223) -- current `transf_instr` structure
- Direct code analysis of `backend/RTLtmrspec.v` (lines 149-230) -- current `match_instr` constructors
- Direct code analysis of `backend/RTLtmrproof.v` (lines 1776-1924, 2196-2306) -- current exec_Iop and exec_Ibuiltin proof cases
- Direct code analysis of `backend/RTLcolor.v` (lines 115-206) -- current `wc_instruction` constructors
- Direct code analysis of `backend/RTLcolorcheck.v` (lines 82-221) -- current `check_col_instr` function
- Direct code analysis of `backend/RTLinfercolor.ml` (lines 277-325) -- current `instr_constraints` Ibuiltin case
- Direct code analysis of `backend/RTLfault.v` (lines 53-62) -- current `zap_allowed` definition
- Direct code analysis of `common/Builtins.v` (lines 99-209) -- Phase 1 classification output
- Direct code analysis of `common/AST.v` -- `map_builtin_arg`, `map_builtin_res` definitions

### Secondary (MEDIUM confidence)
- `.planning/REQUIREMENTS.md` -- Phase 2 requirement specifications
- `.planning/ROADMAP.md` -- Phase dependency and success criteria
- `.planning/STATE.md` -- Phase 1 completion context and decisions

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH - direct code analysis of all relevant files
- Architecture: HIGH - patterns directly observed in existing Iop safe/protected handling
- Pitfalls: HIGH - identified from concrete code structure and type system constraints
- Code examples: MEDIUM - derived from patterns but not yet compiled/verified

**Research date:** 2026-03-14
**Valid until:** 2026-04-14 (stable codebase, no external dependencies changing)
