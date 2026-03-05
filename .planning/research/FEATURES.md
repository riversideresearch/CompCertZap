# Feature Landscape: Liveness-Bounded Fault Tolerance Proof

**Domain:** Formal verification -- backward simulation proof for fault-tolerant RTL in CompCert
**Researched:** 2026-03-04

## Table Stakes

Features the proof cannot compile without. Missing = proof fails.

### F1: ProofLiveness analysis with conservative transfer function

| Property | Detail |
|----------|--------|
| Why required | CompCert's `Liveness.transfer` (lines 68-104 of `Liveness.v`) conditionally includes `Iop`/`Iload` args: it omits them when the destination register is dead (`if Regset.mem res after then ... else after`). The simulation proof needs `Val.lessdef (rs1 # arg) (rs2 # arg)` for every argument of the current instruction, which requires those args to be in the live set. With the liveness-bounded `match_rs` (line 23-29 of `RTLtolerant.v`), if an arg is not in `live !! pc`, the `Regset.In r live` premise cannot be satisfied and the proof is stuck. |
| Complexity | Medium |
| Concrete obligation | `faulty_progress` exec_Iop protected case, line 1366: `apply RS` needs `Regset.In r (live !! pc)` for each `r` in `args`. This fails when `Liveness.transfer` did not add the args because `res` was dead. Same pattern at lines 1392 (Iload), 1409 (Istore args), 1419 (Istore src). |
| What must hold | For `Iop op args res succ` at pc: every register in `args` must be in `transfer pc (live !! succ)`, regardless of whether `res` is live after. |
| Implementation | New `backend/ProofLiveness.v` with transfer function: `Iop` always does `reg_list_live args (reg_dead res after)`; `Iload` always does `reg_list_live args (reg_dead dst after)`. Keep all other cases identical to `Liveness.transfer`. |

### F2: analyze_solution theorem for ProofLiveness

| Property | Detail |
|----------|--------|
| Why required | The `step_simulation` proof needs to transition `match_rs` from `live !! pc` to `live !! succ`. This requires knowing that `transfer f succ (live !! succ)` is a subset of `live !! pc` (the backward dataflow fixpoint property). Without this, the Inop case (line 1703-1713) cannot prove that registers live at `succ` were also live at `pc`. |
| Complexity | Low (direct instantiation of Kildall `Backward_Dataflow_Solver`) |
| Concrete obligation | `step_simulation` Inop case (line 1710): after inverting `wc_Inop`, proving `match_rs (live !! succ) (col succ) b rs1 rs2` from `match_rs (live !! pc) (col pc) b rs1 rs2` + `Regset.For_all (fun r => col pc r = col succ r) (live !! pc)` requires that `Regset.In r (live !! succ) -> Regset.In r (live !! pc)`. |
| What must hold | `ProofLiveness.analyze f = Some live -> f.(fn_code)!n = Some i -> In s (successors_instr i) -> Regset.Subset (ProofLiveness.transfer f s live!!s) live!!n` |
| Implementation | Prove `analyze_solution` analogous to `Liveness.analyze_solution` (line 118-127 of `Liveness.v`), using same Kildall solver infrastructure. |

### F3: Liveness subset lemmas for each instruction form

| Property | Detail |
|----------|--------|
| Why required | Each instruction case in `step_simulation` and `faulty_progress` must derive `Regset.In arg (live !! pc)` for instruction arguments. The proof pattern is: (1) get `analyze_solution` giving `Regset.Subset (transfer f succ (live !! succ)) (live !! pc)`, (2) show the arg is in `transfer f succ (live !! succ)` by definition of transfer, (3) conclude `Regset.In arg (live !! pc)` by subset. |
| Complexity | Medium (one lemma per instruction form, each straightforward but many cases) |
| Concrete obligations | For each instruction type, a helper lemma showing: |

**Required per-instruction membership lemmas:**

1. **Iop (safe):** `forall arg, In arg args -> Regset.In arg (transfer f pc (live !! succ))` -- follows from `reg_list_live` always including args in conservative transfer.
   - Used at: `faulty_progress` line 1362-1370, `step_simulation` line 1731-1738, 1752-1759, 1767-1775.

2. **Iop (protected):** Same as above.
   - Used at: `faulty_progress` line 1362-1370 (the TODO at line 1366).

3. **Iload:** `forall arg, In arg args -> Regset.In arg (transfer f pc (live !! succ))`.
   - Used at: `faulty_progress` line 1386-1394, `step_simulation` line 1802-1808.

4. **Istore (addr args):** `forall arg, In arg args -> Regset.In arg (transfer f pc (live !! succ))`.
   - Used at: `faulty_progress` line 1403-1411, `step_simulation` line 1850-1856.

5. **Istore (src):** `Regset.In src (transfer f pc (live !! succ))`.
   - Used at: `faulty_progress` line 1416-1421, `step_simulation` line 1861-1863.

6. **Icall/Itailcall (ros):** `forall r, ros = inl r -> Regset.In r (transfer f pc (live !! succ))`.
   - Used at: `faulty_progress` line 1430-1436, 1449-1455, `step_simulation` line 1890-1895, 1939-1944.

7. **Icall/Itailcall (args):** `forall arg, In arg args -> Regset.In arg (transfer f pc (live !! succ))`.
   - Used at: `faulty_progress` line 1430-1436 (implicit), `step_simulation` line 1897-1904, 1946-1953.

8. **Ibuiltin (bargs):** `forall r, in_builtin_arg r barg -> Regset.In r (transfer f pc (live !! succ))`.
   - Used at: `faulty_progress` line 1518-1542, `step_simulation` line 1965-2128 (multiple sub-cases).

9. **Icond (args):** `forall arg, In arg args -> Regset.In arg (transfer f pc (live !! succ))`.
   - Used at: `faulty_progress` line 1554-1561, `step_simulation` line 2395-2401.

10. **Ijumptable (arg):** `Regset.In arg (transfer f pc (live !! succ))`.
    - Used at: `faulty_progress` line 1571-1576, `step_simulation` line 2425-2428.

11. **Ireturn (optarg):** `forall r, or = Some r -> Regset.In r (transfer f pc (live !! succ))`.
    - Used at: `step_simulation` line 2456-2459.

12. **Ibuiltin vote (arg1, arg2, arg3):** `Regset.In arg1/arg2/arg3 (live !! pc)`.
    - Used at: `faulty_progress` line 1492-1513, `step_simulation` line 2078-2100.

### F4: match_rs transition lemma (pc -> succ)

| Property | Detail |
|----------|--------|
| Why required | Every instruction case in `step_simulation` must construct a new `match_rs (live !! succ) (col succ) b rs1' rs2'` from the old `match_rs (live !! pc) (col pc) b rs1 rs2`. This transition involves two things: (1) showing register values are preserved or updated correctly, and (2) showing the liveness set transition is sound. Currently this is done inline in every case; a reusable lemma would be table-stakes for maintainability. |
| Complexity | Medium |
| Concrete form | `match_rs_transition`: given `match_rs (live !! pc) (col pc) b rs1 rs2`, `Regset.Subset (live !! succ) (live !! pc)` (or the weaker `For_all` condition from wc_instruction), and appropriate conditions on modified registers, produce `match_rs (live !! succ) (col succ) b rs1' rs2'`. |

### F5: Switch wc_function to use ProofLiveness.analyze

| Property | Detail |
|----------|--------|
| Why required | `wc_function` (line 219-224 of `RTLcolor.v`) currently carries `WC_LIVE: Liveness.analyze f = Some live`. Both `match_stackframes` (line 62-72) and `match_states` (line 88-98) carry `LIVE: Liveness.analyze f = Some live`. These must use the same analysis, or the liveness set in `match_rs` won't match the one used in `wc_instruction` consistency constraints. |
| Complexity | Low (search-and-replace in type signatures) |
| Files affected | `RTLcolor.v` line 220, `RTLcolorcheck.v` line 446/498, `RTLtolerant.v` lines 68/91. |

### F6: check_col_instr_sound proof (currently Admitted)

| Property | Detail |
|----------|--------|
| Why required | `check_col_instr_sound` (line 245-443 of `RTLcolorcheck.v`) is `Admitted`. This lemma bridges the Boolean color checker to the `wc_instruction` spec that the simulation proof depends on. Without it, the `wc_program` assumption in the backward simulation theorem is unsupported. |
| Complexity | High (14 instruction cases, each requiring careful Boolean-to-Prop reflection) |
| Concrete obligation | Line 443: `Admitted.` must be replaced with `Qed.` The proof was previously completed (visible as commented-out proof text lines 249-442) but uses `PTree_Properties.for_all` which has been replaced with `Regset.for_all`. The new proof must use `Regset.for_all_2` (or equivalent) to discharge the `Regset.For_all` goals in `wc_instruction`. |
| Note | The commented-out proof is a near-complete guide. The main adaptation is `Regset.for_all` -> `Regset.For_all` reflection instead of `PTree_Properties.for_all`. |

### F7: match_rs/match_rs_upto parameterized by live set

| Property | Detail |
|----------|--------|
| Why required | Already done (lines 23-38 of `RTLtolerant.v`). `match_rs` and `match_rs_upto` take `live : Regset.t` and quantify over `Regset.In r live`. |
| Complexity | Done |
| Status | Existing on `rtl-liveness` branch. |

### F8: reg_list_live membership lemma

| Property | Detail |
|----------|--------|
| Why required | `reg_list_live` (line 39-43 of `Liveness.v`) adds registers from a list to a set. The proof needs `In r rl -> Regset.In r (reg_list_live rl lv)` to discharge membership goals. This is the fundamental building block for F3. |
| Complexity | Low |
| Implementation | Straightforward induction on `rl`. Also need the monotonicity lemma: `Regset.In r lv -> Regset.In r (reg_list_live rl lv)`. |


## Differentiators

Features that would make the proof cleaner or more maintainable, but are not strictly required for compilation.

### D1: Unified match_rs_step tactic

| Property | Detail |
|----------|--------|
| Value | The proof currently repeats the same pattern ~40 times: `apply RS; intro HC; rewrite H_color in HC; inv HC; inv Hc.` A dedicated Ltac tactic `solve_match_rs` that automates: (1) unfold match_rs, (2) in faulty case destruct the existential color, (3) apply RS with liveness membership, (4) discharge the color inequality using well-coloredness. Would cut proof length by ~30%. |
| Complexity | Medium (Ltac engineering) |
| Risk | Low -- purely proof-engineering, no soundness impact |

### D2: Regset membership decision procedure

| Property | Detail |
|----------|--------|
| Value | A tactic or lemma set that automatically resolves `Regset.In r (transfer f pc (live !! succ))` goals by unfolding transfer, matching on the instruction, and applying `reg_list_live` / `reg_live` / `reg_dead` membership lemmas. Would eliminate the most tedious part of each case. |
| Complexity | Medium |
| Risk | Low |

### D3: Liveness monotonicity across reg_dead

| Property | Detail |
|----------|--------|
| Value | `Regset.In r (reg_dead res after) -> r <> res -> Regset.In r after` and the converse direction. Needed in several cases where the transfer function kills the result register and the proof must show that other live registers remain live. |
| Complexity | Low |

### D4: Separate wc_consistency from wc_color judgement

| Property | Detail |
|----------|--------|
| Value | The `wc_instruction` inductive (lines 114-204 of `RTLcolor.v`) mixes two concerns: (1) color constraints on the current instruction (e.g., `is_basic (col succ res)`) and (2) color consistency across PC transitions (e.g., `Regset.For_all (fun r => col pc r = col succ r) (live !! pc)`). Separating these would make the proof modular. The comment at line 112 of `RTLcolor.v` acknowledges this: "they could be factored out into a separate judgement." |
| Complexity | High (ripples through checker and all proof cases) |
| Risk | Medium -- significant refactoring with unclear benefit-to-cost ratio |

### D5: Weaker match_rs for non-faulty case

| Property | Detail |
|----------|--------|
| Value | In the non-faulty case (`faulted = false`), `match_rs` quantifies `Val.lessdef` over all live registers. But the only place this is consumed is at instruction arguments (where the proof also has `rs_compat` giving full-register val_compat). The liveness bound in the non-faulty branch is technically unnecessary -- the non-faulty invariant could remain universally quantified. This would simplify the non-faulty sub-cases in `step_simulation`. |
| Complexity | Low |
| Risk | Low -- could simplify proof while maintaining soundness |


## Anti-Features

Features to deliberately NOT build.

### A1: Do NOT modify Liveness.v

| Why avoid | `Liveness.v` is used by dead code elimination (`Deadcode.v`), unused global removal (`Unusedglob.v`), register allocation (`Allocation.v`), and the `last_uses` computation for register allocation. Changing its transfer function would break these passes. The conditional inclusion of `Iop`/`Iload` args is correct for DCE -- it's only wrong for the simulation proof. |
| What to do instead | Create separate `ProofLiveness.v` with its own transfer function. |

### A2: Do NOT make liveness analysis external/axiomatized

| Why avoid | The liveness result is used in the proof's match relation (`LIVE: analyze f = Some live`). If it were axiomatized, the proof would depend on an unverified oracle. The whole point of CompCert is verified compilation. |
| What to do instead | Keep it as a Coq-verified backward dataflow analysis using Kildall. |

### A3: Do NOT try to make match_rs quantify over instruction-specific arg sets

| Why avoid | One might think: instead of a fixed live set, parameterize `match_rs` by the specific set of registers needed for the current instruction (args, src, ros, etc.). This would be maximally tight but would require the match relation to carry instruction-specific information, making the inductive `match_states` dependent on the instruction at each PC. This creates a chicken-and-egg problem: you need to know the instruction to know the match, but you need the match to step the instruction. |
| What to do instead | Use liveness analysis as the uniform over-approximation. It naturally provides a per-PC set that includes all needed registers. |

### A4: Do NOT attempt to prove check_col_instr_sound completeness

| Why avoid | Completeness (if `wc_instruction` holds then `check_col_instr = true`) would require axioms about the coloring function that we don't have. The checker only needs soundness: if it returns true, then the spec holds. The comment at line 467-479 of `RTLcolorcheck.v` confirms this was considered and abandoned. |
| What to do instead | Only prove soundness direction. |

### A5: Do NOT extend the proof to assembly level in this milestone

| Why avoid | The fault tolerance proof currently stops at RTL (`transf_c_program_to_rtl`). Extending through register allocation and code generation to assembly is a separate research problem with different challenges. Mixing it in would block progress. |
| What to do instead | Keep `transf_c_program_to_rtl_preservation_faulty` as the top-level theorem. |

### A6: Do NOT change the match_rs_upto pattern for stackframes

| Why avoid | `match_rs_upto res live col faulted rs1 rs2` (lines 31-38) excludes register `res` because upon return, the result register gets overwritten. Changing this to include `res` would break the `exec_return` case (lines 2514-2542) where the proof must construct `match_rs` from `match_rs_upto` + new result value. The current pattern is correct and well-tested. |


## Feature Dependencies

```
F1 (ProofLiveness.v) --> F2 (analyze_solution)
                     \-> F8 (reg_list_live membership)
                     \-> F5 (switch wc_function)
                     \-> F3 (per-instruction membership lemmas)
                            \-> F4 (match_rs transition)
                                   \-> Full step_simulation proof

F6 (check_col_instr_sound) is independent of F1-F5 but blocks wc_program.
F5 must be done after F1 and simultaneously with F6 (they share RTLcolorcheck.v).
F7 is already done.
```

Critical path: F1 -> F2 -> F8 -> F3 -> (F4 + F5 + F6) -> proof rebuild.

## MVP Recommendation

Prioritize in this order:

1. **F1 + F2 + F8:** Create `ProofLiveness.v` with conservative transfer, solver instantiation, `analyze_solution`, and `reg_list_live` membership lemmas. This is the foundation everything else rests on.

2. **F5:** Switch `wc_function` and `match_states`/`match_stackframes` to reference `ProofLiveness.analyze`. This is a mechanical change but must happen before the proof can be rebuilt.

3. **F3:** Prove per-instruction membership lemmas. These are needed at every proof case and are the main new proof work.

4. **F6:** Complete `check_col_instr_sound`. This can be done in parallel with F3 since it touches a different file and the commented-out proof provides a strong guide.

5. **F4:** Build match_rs transition helpers as needed during the proof rebuild.

Defer:
- **D1 (unified tactic):** Nice but not blocking. Do after the proof compiles.
- **D4 (separate wc_consistency):** Too much refactoring for uncertain benefit. Revisit only if maintenance becomes painful.
- **D5 (weaker non-faulty match_rs):** Can be done later as a simplification pass.

## Sources

All findings are from direct code inspection:
- `backend/RTLtolerant.v` -- simulation proof, match relations, all proof obligations
- `backend/RTLcolor.v` -- well-coloredness spec with liveness-bounded consistency
- `backend/RTLcolorcheck.v` -- Boolean checker and Admitted soundness lemma
- `backend/Liveness.v` -- existing liveness analysis and transfer function
- `backend/Kildall.v` -- backward dataflow solver interface
- `plans/liveness-invariant-plan.md` -- implementation plan context
- `.planning/PROJECT.md` -- project requirements
