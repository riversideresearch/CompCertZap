# Phase 3: Faulty Simulation Proof - Research

**Researched:** 2026-03-04
**Domain:** Coq proof engineering -- backward simulation proof with liveness-bounded register matching
**Confidence:** HIGH

## Summary

Phase 3 completes the faulty backward simulation proof in `backend/RTLtolerant.v` by swapping `Liveness.analyze` to `ProofLiveness.analyze` and fixing all proof obligations that currently fail. The file is 2611 lines and currently fails to compile at line 1367 in the `faulty_progress` lemma's `Iop` case, where the proof needs to show that instruction argument registers are in the live set -- exactly the property that `ProofLiveness` (built in Phase 1) guarantees.

The core change is surgical: replace 2 occurrences of `Liveness.analyze` with `ProofLiveness.analyze` in `match_stackframes` (line 68) and `match_states` (line 91), add `Require Import ProofLiveness`, add per-instruction helper lemmas that prove args are in the live set using `ProofLiveness.analyze_solution` and `ProofLiveness.reg_list_live_in`, update `forall2_lessdef_match_rs_init_regs` to accept a `live` parameter, and add a `match_rs_weaken` monotonicity lemma. The existing proof structure (2500+ lines of instruction-case proofs) should remain largely intact because the change only affects how we establish `Val.lessdef` for argument registers -- which is currently the broken part.

**Primary recommendation:** Make all changes in a single plan since they form one atomic proof obligation -- RTLtolerant.vo either compiles or it doesn't.

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|-----------------|
| FSIM-01 | RTLtolerant.v references ProofLiveness.analyze in match_stackframes and match_states | Lines 68 and 91: change `Liveness.analyze` to `ProofLiveness.analyze`; add `Require Import ProofLiveness` |
| FSIM-02 | Per-instruction membership helpers prove args are in live set | Combine `ProofLiveness.analyze_solution` + `ProofLiveness.reg_list_live_in` for each instruction form |
| FSIM-03 | match_rs_weaken lemma: smaller live set preserves match_rs | Follows directly from match_rs being universally quantified over `Regset.In r live` |
| FSIM-04 | forall2_lessdef_match_rs_init_regs updated for live parameter | Add `live : Regset.t` parameter; proof structure unchanged, just add `intros _ Hlive` in each case |
| FSIM-05 | step_simulation proof complete for all instruction cases | Currently complete (lines 1689-2543); after FSIM-01 change, needs `LIVE` goals filled by `WC_LIVE` from `inv WC_FUN` |
| FSIM-06 | faulty_progress proof complete for all instruction cases | Currently breaks at line 1367 (Iop case); needs FSIM-02 helpers to prove args in live set |
| FSIM-07 | faulty_backward_simulation theorem proved | Already structurally proved (lines 2576-2609); depends on step_simulation and faulty_progress compiling |
| FSIM-08 | RTLtolerant.vo compiles with zero Admitted | Integration test: `make backend/RTLtolerant.vo` succeeds |
</phase_requirements>

## Architecture Patterns

### Current File Structure (RTLtolerant.v, 2611 lines)

```
Lines 1-18:     Imports (needs ProofLiveness added)
Lines 23-48:    match_rs, match_rs_upto definitions (already take live parameter)
Lines 50-115:   match_stackframes, match_states (LIVE hypothesis needs change)
Lines 117-138:  Initial state/wc utility lemmas
Lines 140-231:  TOLERANCE section: maybe_zap, fault order lemmas
Lines 233-288:  Utility: final_state_dec, inv_Forall2, inv_rs tactics
Lines 290-918:  val_compat infrastructure (fully proved, no changes needed)
Lines 919-1005: Known builtin / external call lemmas (fully proved)
Lines 1006-1060: list_lessdef_mod_1, vote lessdef lemmas (fully proved)
Lines 1061-1300: smove/vote E0 and mem lemmas (fully proved)
Lines 1300-1332: forall2_lessdef, find_function_lessdef (fully proved)
Lines 1333-1600: faulty_progress (BROKEN at line 1367)
Lines 1601-1687: forall2_lessdef_match_rs_init_regs (needs FSIM-04 update)
Lines 1689-2543: step_simulation (compiles now, may need LIVE adjustment)
Lines 2545-2609: faulty_simulation + faulty_backward_simulation theorem
Lines 2611:      End TOLERANCE
```

### Pattern 1: Liveness Membership via Transfer Function

**What:** Prove that instruction argument registers are in `live!!pc` by combining `ProofLiveness.analyze_solution` with `ProofLiveness.reg_list_live_in`.

**When to use:** Every instruction case in `faulty_progress` and `step_simulation` where we need `Val.lessdef (rs1#r) (rs2#r)` for an argument register `r` and the hypothesis `RS: match_rs (live!!pc) ...` requires `Regset.In r (live!!pc)`.

**Example (Iop args membership):**
```coq
(* Given: *)
(*   LIVE: ProofLiveness.analyze f = Some live *)
(*   Hpc: (fn_code f) ! pc = Some (Iop op args res succ) *)
(*   Hin: In r args *)
(* Goal: Regset.In r (live !! pc) *)

assert (Hsub: Regset.Subset (ProofLiveness.transfer f succ (live !! succ)) (live !! pc)).
{ eapply ProofLiveness.analyze_solution; eauto. simpl; auto. }
apply Hsub.
unfold ProofLiveness.transfer. rewrite Hpc.
apply ProofLiveness.reg_list_live_in. exact Hin.
```

**Factored helper lemma pattern:**
```coq
Lemma args_in_live_iop f live pc op args res succ r :
  ProofLiveness.analyze f = Some live ->
  (fn_code f) ! pc = Some (Iop op args res succ) ->
  In r args ->
  Regset.In r (live !! pc).
Proof.
  intros LIVE Hpc Hin.
  assert (Hsub: Regset.Subset (ProofLiveness.transfer f succ (live !! succ)) (live !! pc))
    by (eapply ProofLiveness.analyze_solution; eauto; simpl; auto).
  apply Hsub. unfold ProofLiveness.transfer. rewrite Hpc.
  apply ProofLiveness.reg_list_live_in. exact Hin.
Qed.
```

### Pattern 2: match_rs Weakening

**What:** If registers match on a bigger live set, they match on any subset.

**Example:**
```coq
Lemma match_rs_weaken s1 s2 col faulted rs1 rs2 :
  Regset.Subset s1 s2 ->
  match_rs s2 col faulted rs1 rs2 ->
  match_rs s1 col faulted rs1 rs2.
Proof.
  unfold match_rs; intros Hsub RS.
  destruct faulted.
  - destruct RS as (c & Hc & RS).
    exists c; split; auto.
    intros r Hr Hcol. apply RS; auto. apply Hsub; auto.
  - intros r Hr. apply RS. apply Hsub; auto.
Qed.
```

### Pattern 3: Deriving LIVE from WC_FUN

**What:** After `inv WC_FUN`, the `WC_LIVE: ProofLiveness.analyze f = Some live0` hypothesis becomes available. Use this to fill `LIVE` fields in new `match_states` constructors.

**When to use:** Every instruction case in `step_simulation` that constructs a new `match_states` via `econstructor; eauto`. After the FSIM-01 change, `eauto` should automatically unify `WC_LIVE` with the `LIVE` field. But if the `live` names differ (e.g., `live` from old `match_states` vs `live0` from `inv WC_FUN`), manual `rewrite` or explicit instantiation may be needed.

**Critical subtlety:** The live map from `match_states` (call it `live`) and the live map from `wc_function` (call it `live0`) must be the same. Since both come from `ProofLiveness.analyze f`, and the analysis is deterministic, `live = live0`. But you may need:
```coq
assert (live = live0) by congruence. subst.
```

### Pattern 4: Per-Instruction Helper Lemma Family

**What:** One helper per instruction form that proves args are in the live set. The pattern is uniform across all instruction types but the transfer function clause varies.

**Instruction forms needing helpers:**
| Instruction | Args to prove live | Transfer function clause |
|---|---|---|
| Iop | `args` | `reg_list_live args (reg_dead res after)` |
| Iload | `args` | `reg_list_live args (reg_dead dst after)` |
| Istore | `args`, `src` | `reg_list_live args (reg_live src after)` |
| Icall | `args`, `ros` (if `inl r`) | `reg_list_live args (reg_sum_live ros ...)` |
| Itailcall | `args`, `ros` (if `inl r`) | `reg_list_live args (reg_sum_live ros ...)` |
| Ibuiltin | `params_of_builtin_args args` | `reg_list_live (params_of_builtin_args args) ...` |
| Icond | `args` | `reg_list_live args after` |
| Ijumptable | `arg` | `reg_live arg after` |
| Ireturn | `optarg` | `reg_option_live optarg empty` |

### Anti-Patterns to Avoid

- **Duplicating the `analyze_solution` + `reg_list_live_in` chain inline in every case:** Factor it into helper lemmas. The same pattern repeats 10+ times.
- **Changing the match_rs definition itself:** The definition is correct as-is. Only the LIVE hypothesis source changes.
- **Modifying proofs that already work:** The `val_compat_*` infrastructure (lines 290-918) needs zero changes. Don't touch it.

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Args in live set | Manual Regset membership arithmetic | `ProofLiveness.analyze_solution` + `ProofLiveness.reg_list_live_in` | Already proved in Phase 1; the whole point of ProofLiveness |
| Live set monotonicity | Case-by-case rewrites | `match_rs_weaken` lemma | Factored once, used everywhere |
| Regset.Subset for successor | Manual fixpoint reasoning | `ProofLiveness.analyze_solution` | Kildall solver guarantee |

## Common Pitfalls

### Pitfall 1: Live Map Identity Confusion
**What goes wrong:** After `inv Hmatch` and `inv WC_FUN`, you have two `live` maps: one from the match_states hypothesis and one from wc_function. They have different names but must be equal.
**Why it happens:** `inv` generates fresh names. `econstructor; eauto` may fail if the names don't unify.
**How to avoid:** Assert `live = live0` by `congruence` (both are `Some` results of the same `ProofLiveness.analyze f` call) and then `subst` immediately after inverting.
**Warning signs:** `eauto` failing to close goals that "should" work, or leftover goals about `live0 !! pc` when the context has `match_rs (live !! pc) ...`.

### Pitfall 2: Successor Node in analyze_solution
**What goes wrong:** `ProofLiveness.analyze_solution` requires `In succ (successors_instr i)`. Different instructions define successors differently. For `Icond`, both `ifso` and `ifnot` are successors. For `Ijumptable`, the successor is `list_nth_z tbl n`.
**Why it happens:** The `In succ (successors_instr i)` obligation is easy to overlook.
**How to avoid:** Each helper lemma must explicitly show the relevant successor is in `successors_instr i`. For simple instructions this is `simpl; auto`. For Icond it's `simpl; destruct b0; auto`. For Ijumptable use `eapply list_nth_z_in`.
**Warning signs:** Goals of the form `In ?succ (successors_instr (Icond ...))` left unsolved.

### Pitfall 3: The forall2_lessdef_match_rs_init_regs Live Parameter
**What goes wrong:** After adding `live` parameter, the call site at line 2476 fails because `apply forall2_lessdef_match_rs_init_regs; assumption` no longer works -- it needs the `live` argument.
**Why it happens:** `econstructor; eauto` on line 2474 will produce a goal `match_rs (live !! (fn_entrypoint f)) ...`. The lemma now takes `live` explicitly.
**How to avoid:** The lemma should universally quantify over `live` so `apply` infers it. Alternatively, use `eapply`.
**Warning signs:** "Cannot unify" errors at the `exec_function_internal` case.

### Pitfall 4: faulty_progress vs step_simulation Proof Structures
**What goes wrong:** Assuming both lemmas need the same fixes.
**Why it happens:** `faulty_progress` proves the faulty side can step (given a matching 3-voting state). `step_simulation` proves the 3-voting side can step when the faulty side steps. They use `match_rs` in opposite directions.
**How to avoid:** In `faulty_progress`, we need args in live set to extract `Val.lessdef` from `RS`. In `step_simulation`, we construct a new `match_states` and need to provide `LIVE` for the new state. Different proof obligations.

### Pitfall 5: Ibuiltin Vote Sub-Cases
**What goes wrong:** Vote builtins have a different structure (3 specific named arguments: arg1, arg2, arg3 with specific colors Red, Green, Blue) vs general builtins that use `params_of_builtin_args`.
**Why it happens:** The wc_instruction has separate constructors: `wc_Ibuiltin_smove_green`, `wc_Ibuiltin_smove_blue`, `wc_Ibuiltin_vote`, `wc_Ibuiltin` (general).
**How to avoid:** Handle vote cases by directly using the color hypotheses (e.g., `col pc arg1 = Red`) to prove lessdef, rather than the generic `reg_list_live_in` path. For smoves and votes, the args are known explicitly.
**Warning signs:** The `inv_wc` tactic producing 4 sub-cases for Ibuiltin.

## Code Examples

### Complete Helper: Iop Args Membership
```coq
(* Source: ProofLiveness.v analyze_solution + reg_list_live_in *)
Lemma iop_args_in_live f live pc op args res succ r :
  ProofLiveness.analyze f = Some live ->
  (fn_code f) ! pc = Some (Iop op args res succ) ->
  In r args ->
  Regset.In r (live !! pc).
Proof.
  intros LIVE Hpc Hin.
  eapply ProofLiveness.analyze_solution in LIVE; eauto.
  2: { simpl; auto. }
  apply LIVE. unfold ProofLiveness.transfer. rewrite Hpc.
  apply ProofLiveness.reg_list_live_in; auto.
Qed.
```

### Complete Helper: Istore Args/Src Membership
```coq
Lemma istore_args_in_live f live pc chunk addr args src succ r :
  ProofLiveness.analyze f = Some live ->
  (fn_code f) ! pc = Some (Istore chunk addr args src succ) ->
  In r args ->
  Regset.In r (live !! pc).
Proof.
  intros LIVE Hpc Hin.
  eapply ProofLiveness.analyze_solution in LIVE; eauto.
  2: { simpl; auto. }
  apply LIVE. unfold ProofLiveness.transfer. rewrite Hpc.
  apply ProofLiveness.reg_list_live_in; auto.
Qed.

Lemma istore_src_in_live f live pc chunk addr args src succ :
  ProofLiveness.analyze f = Some live ->
  (fn_code f) ! pc = Some (Istore chunk addr args src succ) ->
  Regset.In src (live !! pc).
Proof.
  intros LIVE Hpc.
  eapply ProofLiveness.analyze_solution in LIVE; eauto.
  2: { simpl; auto. }
  apply LIVE. unfold ProofLiveness.transfer. rewrite Hpc.
  apply ProofLiveness.reg_list_live_incl.
  apply Regset.add_1. reflexivity.
Qed.
```

### Using match_rs_weaken in step_simulation Inop Case
```coq
(* When the successor has a different live set *)
(* Current proof pattern at line 1707-1712: *)
econstructor; eauto.
  inv WC_FUN.
  apply wc_fn_code in H; inv H.
  (* Now have: RS : match_rs (live !! pc) (col pc) b rs1 rs2 *)
  (* Goal:    match_rs (live !! succ) (col succ) b rs1 rs2 *)
  (* wc_Inop gives: Regset.For_all (fun r => col pc r = col succ r) (live !! pc) *)
  eapply match_rs_weaken.
  2: { exact RS. }
  (* Goal: Regset.Subset (live !! succ) (live !! pc) *)
  (* NOT what we want -- the live sets go the other direction *)
  (* Actually, for Inop: transfer f succ (live!!succ) = live!!succ *)
  (* So analyze_solution gives: Subset (live!!succ) (live!!pc) *)
  eapply ProofLiveness.analyze_solution; eauto. simpl; auto.
```

### match_rs_weaken Definition
```coq
Lemma match_rs_weaken s1 s2 col faulted rs1 rs2 :
  Regset.Subset s1 s2 ->
  match_rs s2 col faulted rs1 rs2 ->
  match_rs s1 col faulted rs1 rs2.
Proof.
  unfold match_rs; intros Hsub RS.
  destruct faulted.
  - destruct RS as (c & Hc & RS).
    exists c; split; auto.
    intros r Hr Hcol. apply RS; auto.
  - intros r Hr. apply RS. apply Hsub; auto.
Qed.
```

### Updated forall2_lessdef_match_rs_init_regs (FSIM-04)
```coq
Lemma forall2_lessdef_match_rs_init_regs live args1 args2 col b params :
  Forall2 Val.lessdef args1 args2 ->
  match_rs live col b (init_regs args1 params) (init_regs args2 params).
Proof.
  revert b args1 args2.
  induction params; simpl; intros b args1 args2 Hforall.
  { destruct b.
    exists Red; split; try constructor.
    intros r _; apply Val.lessdef_refl.     (* added _ for Regset.In *)
    intros r _; apply Val.lessdef_refl. }   (* added _ for Regset.In *)
  destruct b.
  - destruct args1; inv Hforall.
    { exists Red; split; try constructor;
      intros r _; apply Val.lessdef_refl. }
    eapply IHparams with (b := true) in H3; eauto.
    destruct H3 as (c & Hc & RS).
    exists c; split; auto.
    intros r Hlive Hr.    (* added Hlive *)
    destruct (peq r a); subst.
    + rewrite 2!Regmap.gss; assumption.
    + rewrite 2!Regmap.gso; auto.
  - destruct args1; inv Hforall.
    { intros r _; apply Val.lessdef_refl. }
    intros r Hlive.   (* added Hlive *)
    destruct (peq r a); subst.
    + rewrite 2!Regmap.gss; assumption.
    + rewrite 2!Regmap.gso; auto.
      eapply IHparams with (b := false) in H3; eauto.
Qed.
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|---|---|---|---|
| `Liveness.analyze` in match_states | `ProofLiveness.analyze` in match_states | Phase 1 created ProofLiveness; Phase 2 updated RTLcolor/RTLcolorcheck | Enables proving args in live set |
| match_rs without live parameter | match_rs with live parameter | Already done (current code) | Scopes register matching to live registers only |
| Separate live hypothesis from wc_function | LIVE derivable from WC_FUN | After Phase 2 (wc_function stores ProofLiveness.analyze) | Proof can get LIVE from WC_FUN via inv |

## Validation Architecture

### Test Framework
| Property | Value |
|----------|-------|
| Framework | Coq proof checker (coqc) |
| Config file | `_CoqProject` |
| Quick run command | `make backend/RTLtolerant.vo` |
| Full suite command | `make backend/RTLtolerant.vo && make check-admitted` |

### Phase Requirements to Test Map
| Req ID | Behavior | Test Type | Automated Command | File Exists? |
|--------|----------|-----------|-------------------|-------------|
| FSIM-01 | match_stackframes/match_states use ProofLiveness.analyze | unit (coqc) | `grep -c 'ProofLiveness.analyze' backend/RTLtolerant.v` | N/A - source check |
| FSIM-02 | Args-in-live helpers exist and are used | unit (coqc) | `make backend/RTLtolerant.vo` | N/A - part of RTLtolerant.v |
| FSIM-03 | match_rs_weaken lemma proved | unit (coqc) | `make backend/RTLtolerant.vo` | N/A - part of RTLtolerant.v |
| FSIM-04 | forall2_lessdef_match_rs_init_regs updated | unit (coqc) | `make backend/RTLtolerant.vo` | N/A - part of RTLtolerant.v |
| FSIM-05 | step_simulation all cases proved | unit (coqc) | `make backend/RTLtolerant.vo` | N/A - part of RTLtolerant.v |
| FSIM-06 | faulty_progress all cases proved | unit (coqc) | `make backend/RTLtolerant.vo` | N/A - part of RTLtolerant.v |
| FSIM-07 | faulty_backward_simulation proved | unit (coqc) | `make backend/RTLtolerant.vo` | N/A - part of RTLtolerant.v |
| FSIM-08 | Zero Admitted in RTLtolerant.vo | integration | `make backend/RTLtolerant.vo && grep -c Admitted backend/RTLtolerant.v` | N/A |

### Sampling Rate
- **Per task commit:** `make backend/RTLtolerant.vo`
- **Per wave merge:** `make backend/RTLtolerant.vo && make check-admitted`
- **Phase gate:** `make backend/RTLtolerant.vo` succeeds with zero Admitted

### Wave 0 Gaps
None -- existing Coq build infrastructure handles all compilation and proof checking. Phase 1 and Phase 2 are already complete, providing `ProofLiveness.vo` and updated `RTLcolor.vo` / `RTLcolorcheck.vo`.

## Detailed Change Analysis

### Changes Required (by location in RTLtolerant.v)

**1. Imports (line 1-18):** Add `ProofLiveness` to Require Import block. Remove `Liveness` if no longer used (but `Liveness` is likely still transitively imported via other modules, so removing may not be needed).

**2. match_stackframes (line 68):** Change `Liveness.analyze` to `ProofLiveness.analyze`.

**3. match_states (line 91):** Change `Liveness.analyze` to `ProofLiveness.analyze`.

**4. New lemmas (insert after line 48, before Section match_states):**
- `match_rs_weaken` (FSIM-03)
- Per-instruction args-in-live helpers (FSIM-02): approximately 8-10 lemmas

**5. forall2_lessdef_match_rs_init_regs (lines 1661-1687):** Add `live` parameter, adjust proof (FSIM-04).

**6. faulty_progress (lines 1333-1600):** Fix broken proof at line 1367 using new helpers. Pattern: where the proof currently tries to use `RS` and fails to show `Regset.In r (live!!pc)`, insert calls to the new args-in-live helpers.

**7. step_simulation (lines 1689-2543):** The existing proofs should mostly work after the LIVE change because:
- `econstructor; eauto` will find `WC_LIVE` from `inv WC_FUN`
- The `match_rs` usage pattern is the same, just with ProofLiveness live sets
- The Inop case (line 1707-1712) may need adjustment for the successor live set (use `match_rs_weaken` + `analyze_solution`)

**8. exec_function_internal (line 2476):** `forall2_lessdef_match_rs_init_regs` call needs `live` argument (will unify via eauto).

### Lines NOT Needing Changes
- val_compat infrastructure (290-918): Pure value-level reasoning, no liveness
- known_builtin / external_call lemmas (919-1060): Semantic lemmas, no liveness
- smove/vote lemmas (1061-1300): External call properties, no liveness
- faulty_simulation (2545-2574): Composition wrapper, delegates to step_simulation
- faulty_backward_simulation (2576-2609): Structural theorem, delegates to components

## Open Questions

1. **Inop match_rs at successor**
   - What we know: For Inop, the transfer function is `after` (identity), so `analyze_solution` gives `Subset (live!!succ) (live!!pc)`. The wc_Inop gives color preservation. The existing proof does `unfold match_rs in *; destruct b; ...` and propagates RS to the successor.
   - What's unclear: Whether `match_rs_weaken` suffices, or if the proof needs additional reasoning about color preservation at successor (the wc_Inop `For_all` hypothesis).
   - Recommendation: Try `match_rs_weaken` + `analyze_solution` first. If insufficient, the color-preservation For_all from wc_Inop provides the color equality needed.

2. **Step_simulation Iop safe-op case uses RS directly**
   - What we know: At line 1781-1790 (non-faulted Iop safe case), the proof does `intro r; ... auto` without needing `Regset.In` because when `b=false` the current match_rs is `forall r, Regset.In r live -> ...` and the proof handles this.
   - What's unclear: After the change, whether `auto` still closes goals or needs explicit liveness witnesses.
   - Recommendation: If `auto` fails, add `eapply args_in_live_iop; eauto` before the `auto`.

## Sources

### Primary (HIGH confidence)
- `backend/RTLtolerant.v` -- direct source inspection, compile test confirming failure at line 1367
- `backend/ProofLiveness.v` -- `analyze_solution`, `reg_list_live_in`, `reg_list_live_incl` confirmed by reading
- `backend/RTLcolor.v` -- `wc_function` stores `ProofLiveness.analyze f = Some live` (line 221)
- `backend/RTLfault.v` -- `fstate`, `maybe_zap`, `fstep` semantics confirmed
- `backend/Liveness.v` -- transfer function with conditional `Regset.mem res after` guard (line 78)

### Secondary (MEDIUM confidence)
- `.planning/STATE.md` -- Phase 1 and Phase 2 complete, accumulated decisions about proof patterns

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH - this is a pure Coq project, tools are coqc and make
- Architecture: HIGH - read entire 2611-line file, understand every section
- Pitfalls: HIGH - identified the exact compile failure (line 1367) and root cause
- Code examples: HIGH - based on actual `ProofLiveness` API verified by reading source

**Research date:** 2026-03-04
**Valid until:** Indefinite (Coq proof obligations don't change unless source changes)
