# Domain Pitfalls

**Domain:** CompCert simulation proof refactoring -- liveness-bounded invariant update
**Researched:** 2026-03-04

## Critical Pitfalls

Mistakes that cause rewrites, stuck proofs, or broken theorem chains.

### Pitfall 1: Liveness Set Monotonicity Gap at Successor Transitions

**What goes wrong:** The `match_rs` invariant is quantified over `live !! pc` at the current program point. After a step to `succ`, the proof must re-establish `match_rs (live !! succ)`. If `live !! succ` contains registers not in `live !! pc`, the proof has no `Val.lessdef` information for those registers. The `wc_instruction` consistency constraints (`Regset.For_all ... (live !! pc)`) only cover registers in the *current* live set, not the successor's.

**Why it happens:** The standard CompCert liveness transfer function (`Liveness.transfer`) is a backward analysis: `live !! pc` is computed from `live !! succ` by adding used registers and removing defined ones. So `live !! pc` is typically a *superset* of `live !! succ` (minus defined regs, plus used regs). For most instructions, `live !! succ` is a subset of `live !! pc` union newly-computed registers. But when `Iop`/`Iload` has a dead result, `Liveness.transfer` does NOT add args to the live set, so args may be in `live !! pc` (from the after-set) but not provably so. The converse problem -- registers in `live !! succ` but not `live !! pc` -- does not occur for standard liveness because it is a backward analysis where `live !! pc >= transfer(live !! succ)`. However, if you switch to `ProofLiveness` with a different transfer function, this monotonicity relationship changes, and you must verify the new transfer function still guarantees the subset relationships your proof relies on.

**Consequences:** The `step_simulation` lemma gets stuck at every instruction case when trying to show `match_rs (live !! succ)` from `match_rs (live !! pc)`. The `auto` tactic that worked before liveness bounding (when the invariant was over all registers) now leaves unsolved `Regset.In r (live !! succ)` goals.

**Prevention:**
1. Prove a `match_succ_states` helper lemma (following the pattern in `Deadcodeproof.v`, lines 537-555) that encapsulates the transition from `live !! pc` to `live !! succ` using `analyze_solution`.
2. The `ProofLiveness.analyze_solution` lemma gives `Regset.Subset (transfer f s (live !! s)) (live !! n)` for successor `s` of instruction at `n`. Use this to show that for every `r` in `live !! succ`, either `r` is handled by the step (result register, newly computed) or `r` was already in `live !! pc` (and thus covered by the old `RS`).
3. Verify your transfer function before proving simulation cases. Write a standalone lemma: `forall pc i succ, code ! pc = Some i -> In succ (successors_instr i) -> forall r, Regset.In r (live !! succ) -> [r is handled by instruction i] \/ Regset.In r (live !! pc)`.

**Detection:** The proof breaks at `rewrite 2!Regmap.gso; auto.` lines in `step_simulation` -- the `auto` no longer closes the goal because there is an extra `Regset.In` premise.

**Phase:** Phase 3 (RTLtolerant invariant rebuild). Must be addressed as the first structural change before tackling individual instruction cases.

---

### Pitfall 2: Liveness Transfer Too Weak for Simulation Obligations

**What goes wrong:** CompCert's `Liveness.transfer` for `Iop` is: `if Regset.mem res after then reg_list_live args (reg_dead res after) else after`. When `res` is NOT live after the instruction, the args are NOT added to the before-set. But the simulation proof needs `Val.lessdef` for args to evaluate the operation at line 1361-1370 in `faulty_progress` and at lines 1729-1738 in `step_simulation`. With the liveness-bounded invariant, `match_rs (live !! pc)` does not guarantee `Val.lessdef (rs1 # arg) (rs2 # arg)` for args not in `live !! pc`.

**Why it happens:** Standard liveness is designed for dead code elimination: if `res` is dead, the instruction will be removed, so its args do not need to be live. But the simulation proof does NOT remove any instructions -- it must show that the operation can be evaluated on both sides. This is the fundamental mismatch documented in the plan's "Why this is needed" section and visible at the `TODO` comment on line 1366.

**Consequences:** Every `Iop` and `Iload` case in both `faulty_progress` and `step_simulation` fails. The pattern `apply Forall_forall; intros r Hin; apply RS; ...` requires `Regset.In r (live !! pc)` but the arg may not be in the live set.

**Prevention:** Create `ProofLiveness.v` with a conservative transfer function:
```
| Iop op args res s => reg_list_live args (reg_dead res after)  (* always add args *)
| Iload chunk addr args dst s => reg_list_live args (reg_dead dst after)  (* always add args *)
```
This over-approximates liveness but guarantees args are always in the before-set, regardless of whether the result is live. All other instruction cases can match standard `Liveness.transfer`.

**Detection:** Proof failure at the `TODO` comment (line 1366) and at analogous positions in `Iload`/`Istore` cases where `forall_lessdef_list` is applied.

**Phase:** Phase 1 (ProofLiveness.v creation). This is the root cause of the current proof breakage and must be resolved first.

---

### Pitfall 3: Commented-Out Proof in check_col_instr_sound Hides Type Mismatches

**What goes wrong:** `check_col_instr_sound` in `RTLcolorcheck.v` (line 246) is `Admitted` with the entire proof body commented out (lines 249-442). The commented proof was written against an older version of `wc_instruction` that used `PTree_Properties.for_all` over a total coloring map. The current `wc_instruction` uses `Regset.For_all` over the liveness set. Uncommenting the old proof and trying to fix it will reveal deep structural mismatches, not just superficial tactic failures.

**Why it happens:** The `wc_instruction` definition was updated to accept liveness-bounded constraints (`Regset.For_all ... (live !! pc)`) but the checker soundness proof was not updated. The old proof used `PTree_Properties.for_all_correct` to extract properties per-register from the checker's boolean `PTree_Properties.for_all` over the coloring. The new checker uses `Regset.for_all` over the liveness set instead. These are fundamentally different iteration structures.

**Consequences:** Attempting to re-prove `check_col_instr_sound` by uncommenting the old proof leads to 15+ type errors across all instruction cases. The fix requires systematic replacement of `PTree_Properties.for_all_correct` with `Regset.for_all_spec` (or equivalent), and adjusting every quantifier extraction step.

**Prevention:**
1. Do NOT try to uncomment and patch the old proof. Write the proof fresh, case by case, using the current `check_col_instr` definition as the template.
2. Prove one instruction case at a time (start with `Inop`, which is simplest).
3. Build helper lemmas for the common pattern: `Regset.for_all f s = true -> Regset.For_all f s` (this may already exist as `Regset.for_all_spec` or need a small wrapper).
4. The `destruct_andb` and `destruct_orb` tactics (lines 235-243) are still usable -- keep them.

**Detection:** Any attempt to `Require` or `make` `RTLcolorcheck.vo` will succeed (the `Admitted` compiles) but `make check-admitted` will flag it. Trying to fill in the proof reveals the mismatch immediately.

**Phase:** Phase 2 (checker soundness re-proof). Can be done in parallel with Phase 1 since it does not depend on `ProofLiveness.v` existing yet (only on the shape of `wc_instruction`).

---

### Pitfall 4: match_rs / match_rs_upto / forall2_lessdef_match_rs_init_regs Arity Mismatch

**What goes wrong:** The `match_rs` and `match_rs_upto` definitions now take a `live : Regset.t` parameter (lines 23, 31). But `forall2_lessdef_match_rs_init_regs` at line 1661 calls `match_rs col b ...` without the `live` parameter. This is a type error that prevents the file from compiling at all.

**Why it happens:** The `live` parameter was added to `match_rs` as part of the liveness-bounding change, but not all call sites were updated. The `forall2_lessdef_match_rs_init_regs` lemma was left in its old form.

**Consequences:** The entire `RTLtolerant.v` file does not compile. Every proof that depends on it (including the top-level theorem in `Complements.v`) is blocked.

**Prevention:**
1. After changing any definition's type signature, immediately grep for ALL call sites: `grep -n 'match_rs' backend/RTLtolerant.v`.
2. Update all call sites before attempting to compile. For `forall2_lessdef_match_rs_init_regs`, the fix is to add a `live` parameter and add `Regset.In r live ->` premises, or (simpler for init_regs) prove it for an arbitrary live set since `init_regs` from `Val.lessdef` args gives `Val.lessdef` for all registers unconditionally.
3. Run `coqc` on the file early and often -- do not accumulate changes across multiple definitions before checking compilation.

**Detection:** `coqc` will report a type error at line 1663. This is the first error you'll see when trying to compile.

**Phase:** Phase 3 (RTLtolerant rebuild). Must be fixed as part of the initial compilation pass, before any proof work.

---

### Pitfall 5: wc_function Carries Its Own Liveness Analysis Reference

**What goes wrong:** `wc_function` (RTLcolor.v line 219) internally stores `WC_LIVE: Liveness.analyze f = Some live`. The `match_states` relation (RTLtolerant.v line 91) independently stores `LIVE: Liveness.analyze f = Some live`. When switching to `ProofLiveness.analyze`, BOTH must be changed simultaneously, and the proof must ensure they refer to the same analysis result. If one is changed and the other is not, the proof has two different `live` maps in scope with no connection between them.

**Why it happens:** The proof structure has two independent sources of truth for the liveness analysis. This is a common pattern in CompCert (the pass definition carries the analysis, and the match relation carries it too) but it creates a coordination problem during refactoring.

**Consequences:** If `wc_function` uses `ProofLiveness.analyze` but `match_states` still uses `Liveness.analyze`, the `inv WC_FUN` tactic produces hypotheses about a different `live` map than the one in the `RS` hypothesis. Color consistency facts derived from `wc_instruction` are about one live set; the `match_rs` obligation is about another. The proof gets stuck trying to rewrite between two unrelated live maps.

**Prevention:**
1. Change both simultaneously in a single commit/edit session.
2. After changing, grep for ALL occurrences of `Liveness.analyze` in touched files to ensure none remain.
3. Add a comment documenting that `LIVE` in `match_states` and `WC_LIVE` in `wc_function` must refer to the same analysis.

**Detection:** After `inv WC_FUN`, the context will contain two different `live` variables (e.g., `live` and `live0`) with no proof of equality. The `auto` and `congruence` tactics that previously closed goals by unifying these hypotheses will fail.

**Phase:** Phase 2 (RTLcolor.v / RTLcolorcheck.v switch) and Phase 3 (RTLtolerant.v). These must use the same analysis.

---

## Moderate Pitfalls

### Pitfall 6: Regset.For_all vs forall Over Live Registers -- Proof Idiom Mismatch

**What goes wrong:** The `wc_instruction` constructors use `Regset.For_all` (a propositional predicate over the live set). The simulation proof frequently needs to extract facts about individual registers from this. The standard extraction idiom is `apply H; auto` where `H : Regset.For_all P s` and you need to show `Regset.In r s`. But with liveness bounding, the `Regset.In r (live !! pc)` fact is not always available in context -- it must be derived from the transfer function or from the instruction structure.

**Why it happens:** Before liveness bounding, `match_rs` was `forall r, ...` and extracting `Val.lessdef` for any register was trivial. Now, extracting it requires proving membership in the live set first.

**Prevention:**
1. Build a small library of `In_transfer` lemmas: for each instruction type, prove that args/results are in the appropriate live sets. E.g., `forall f live pc op args res succ, ProofLiveness.analyze f = Some live -> f.(fn_code) ! pc = Some (Iop op args res succ) -> forall r, In r args -> Regset.In r (live !! pc)`.
2. Create a tactic `solve_live` that tries `apply In_transfer_Iop; eauto` and similar for each instruction type.
3. Register these lemmas in a hint database so `auto` can find them.

**Detection:** Proof scripts that previously closed with `auto` or `apply RS` now leave `Regset.In` subgoals.

**Phase:** Phase 1 (prove In_transfer lemmas alongside ProofLiveness.v) and Phase 3 (use them in RTLtolerant.v).

---

### Pitfall 7: The Inop Case Is Deceptively Simple -- Color Consistency Does NOT Imply Liveness Subset

**What goes wrong:** The `step_simulation` Inop case (line 1703) currently just does `econstructor; eauto` and then unfolds `match_rs` to carry forward the invariant. With liveness bounding, the goal changes from `match_rs (live !! pc) ... rs1 rs2` to `match_rs (live !! succ) ... rs1 rs2`. The `wc_Inop` constructor gives `Regset.For_all (fun r => col pc r = col succ r) (live !! pc)` -- this is about COLOR preservation, not about which registers are live. You still need to show that `Regset.In r (live !! succ)` implies `Regset.In r (live !! pc)` (since the regsets are unchanged for Inop).

**Why it happens:** For Inop, `Liveness.transfer f pc (live !! succ) = live !! succ` (the transfer is identity). By `analyze_solution`, `Regset.Subset (live !! succ) (live !! pc)`. So any register live at `succ` is also live at `pc`, and `RS` gives `Val.lessdef` for it. But this reasoning requires explicitly invoking `analyze_solution` -- it is NOT automatic.

**Prevention:**
1. Prove the subset relationship as the FIRST step in each instruction case: `assert (Hsub: Regset.Subset (live !! succ) (live !! pc))` by `eapply analyze_solution_subset; eauto; simpl; auto`.
2. Use `Hsub` to convert `Regset.In r (live !! succ)` goals to `Regset.In r (live !! pc)`.
3. Consider adding a `match_rs_weaken` lemma: `Regset.Subset s1 s2 -> match_rs s2 col b rs1 rs2 -> match_rs s1 col b rs1 rs2` to make the transition a one-liner.

**Detection:** The Inop case leaves an `Regset.In r (live !! succ)` goal that `auto` cannot close.

**Phase:** Phase 3. The `match_rs_weaken` lemma should be proved early as utility infrastructure.

---

### Pitfall 8: maybe_zap_preserves_match_states Needs Liveness Awareness

**What goes wrong:** The `maybe_zap_preserves_match_states` lemma (line 202) handles the fault injection case where a register is zapped. Its proof constructs the faulted color and uses `Regmap.gss`/`Regmap.gso` to handle the zapped register. With liveness bounding, the proof must also show that the liveness set at the new PC is consistent with the zapped state.

**Why it happens:** The lemma's proof at line 220 unfolds `match_rs` and constructs `exists (col pc' r); split; auto`. It then handles individual registers with `Regmap.gso`. But now it must also handle the liveness subset: the zap happens at `pc'` (after a step), so the match must be for `live !! pc'`, and the proof must connect back to the pre-step invariant.

**Prevention:** Update `maybe_zap_preserves_match_states` FIRST, before touching the main simulation lemmas. This lemma is used by `faulty_simulation` and any breakage cascades.

**Detection:** The `eapply maybe_zap_preserves_match_states` call in `faulty_simulation` will fail to unify if the lemma's type signature has changed or if it produces subgoals it did not previously produce.

**Phase:** Phase 3. Should be one of the first lemmas updated.

---

### Pitfall 9: forall2_lessdef_match_rs_init_regs Must Handle All Registers, Not Just Live Ones

**What goes wrong:** At function entry (`exec_function_internal` case, around line 2476), `forall2_lessdef_match_rs_init_regs` is used to establish the initial match. The entry point's live set may not contain all parameter registers. But `init_regs` with `Val.lessdef` args gives `Val.lessdef` for all registers unconditionally (unused params default to `Vundef` on both sides). The lemma must be generalized to work with any live set.

**Why it happens:** `init_regs` produces identical-structure regsets from `Val.lessdef`-related args, so `Val.lessdef (init_regs args1 params) # r (init_regs args2 params) # r` holds for ALL `r`, not just live ones. The liveness-bounded version should be easy to prove: `forall r, Regset.In r live -> Val.lessdef ...` follows trivially from `forall r, Val.lessdef ...`.

**Prevention:** Update the lemma to take a `live` parameter and prove the stronger statement first: `forall r, Val.lessdef ...`, then derive the liveness-bounded version as a corollary. Alternatively, prove a general `match_rs_from_all` helper: `(forall r, Val.lessdef (rs1 # r) (rs2 # r)) -> match_rs live col false rs1 rs2`.

**Detection:** Type error at line 2476 where `forall2_lessdef_match_rs_init_regs` is applied.

**Phase:** Phase 3. Quick fix, but must be done to get past the internal function case.

---

### Pitfall 10: Regset.for_all_spec vs Regset.For_all -- Boolean vs Propositional Mismatch in Checker

**What goes wrong:** The checker (`check_col_instr`) uses `Regset.for_all` (boolean function). The spec (`wc_instruction`) uses `Regset.For_all` (propositional `forall r, Regset.In r s -> P r`). Bridging these requires a reflection lemma. If you use the wrong one or mix up the directions (soundness vs completeness), the proof structure breaks.

**Why it happens:** CompCert's `Regset` module may or may not provide a clean `for_all_spec` reflection lemma depending on the version. The MSet interface provides `for_all_spec` but it requires `Proper` instances for the predicate. If the predicate involves term-level variables captured in closures (like `col pc r =? col succ r`), the `Proper` instance may be nontrivial.

**Prevention:**
1. Check what `Regset` provides: look for `Regset.for_all_spec`, `Regset.for_all_1`, `Regset.for_all_2` in the module's interface.
2. If needed, prove a custom bridge: `forall f s, Regset.for_all f s = true -> Regset.For_all (fun r => f r = true) s`.
3. Use this bridge uniformly in all instruction cases of `check_col_instr_sound`.

**Detection:** The `Regset.for_all_correct` or `PTree_Properties.for_all_correct` lemmas from the old proof no longer apply (wrong types). The proof gets stuck after `destruct_andb`.

**Phase:** Phase 2 (checker soundness proof).

---

## Minor Pitfalls

### Pitfall 11: Tactic Brittleness Under Definition Changes

**What goes wrong:** The `inv_rs` and `inv_wc` Ltac tactics (lines 157, 281) pattern-match on the exact shape of hypotheses. Changing `match_rs` or `wc_instruction` definitions can break these tactics silently -- they may match the wrong hypothesis or fail to match at all.

**Prevention:** After changing definitions, test the tactics in isolation on a small example before running them in the full proof. Update the match patterns if the destructured form changes.

**Phase:** Phase 3. Low effort but easy to overlook.

---

### Pitfall 12: inv WC_FUN Produces Different Hypothesis Names

**What goes wrong:** The `inv WC_FUN` tactic destructs the `wc_function` record. If `wc_function` gains or loses a field (e.g., adding a `ProofLiveness` reference), the auto-generated hypothesis names change. Subsequent tactics that refer to hypotheses by name (e.g., `apply wc_fn_code in H`) break.

**Prevention:** After changing `wc_function`, test `inv WC_FUN` in one case to see the new hypothesis names. Consider using `destruct WC_FUN as [? ? WC_LIVE WC_PARAMS WC_CODE]` with explicit names instead of `inv`.

**Phase:** Phase 3. Affects every instruction case in `step_simulation` and `faulty_progress`.

---

### Pitfall 13: The faulty_progress and step_simulation Proofs Are Structurally Similar but Not Identical

**What goes wrong:** When refactoring, developers fix `faulty_progress` (the progress/determinism lemma) and assume `step_simulation` (the backward simulation step) can be fixed identically. But `faulty_progress` proves existence of a step (weaker: just needs to find SOME next state) while `step_simulation` must establish the full match relation at the successor (stronger: needs exact `Val.lessdef` relationships). The liveness obligations differ in each.

**Prevention:** Fix `step_simulation` FIRST (it is harder and more constraining). Then adapt the patterns to `faulty_progress` (which is more forgiving). Fixing `faulty_progress` first gives false confidence that the approach works.

**Phase:** Phase 3. Ordering discipline within the phase.

---

### Pitfall 14: Missing Regset.In for Istore src Register

**What goes wrong:** `Istore` has both `args` (address operands) and `src` (value to store). The simulation proof needs `Val.lessdef (rs1 # src) (rs2 # src)`. With liveness bounding, this requires `Regset.In src (live !! pc)`. The `Liveness.transfer` for `Istore` is `reg_list_live args (reg_live src after)`, which always adds `src` to the live set. But if you switch to `ProofLiveness` and accidentally omit `src` from the transfer, the proof breaks at the Istore case.

**Prevention:** When writing the `ProofLiveness.transfer` function, copy the `Istore` case exactly from `Liveness.transfer`. The `Istore` case is already correct for simulation purposes -- it always includes both args and src. Similarly for `Icall`/`Itailcall` which always include args and the function register.

**Phase:** Phase 1 (ProofLiveness.v). Easy to get right if you copy from Liveness.v carefully.

---

## Phase-Specific Warnings

| Phase Topic | Likely Pitfall | Mitigation |
|-------------|---------------|------------|
| Phase 1: ProofLiveness.v | Transfer too weak for some instruction (Pitfall 2) | Test with a manual proof sketch: for each instruction, verify args are in the before-set |
| Phase 1: ProofLiveness.v | analyze_solution statement does not match Liveness.analyze_solution shape | Mirror the exact same theorem statement, changing only the transfer function reference |
| Phase 2: RTLcolorcheck.v | Old commented proof misleads (Pitfall 3) | Write fresh; do not uncomment old proof |
| Phase 2: RTLcolor.v | wc_function liveness source mismatch (Pitfall 5) | Change Liveness -> ProofLiveness atomically across RTLcolor.v and RTLcolorcheck.v |
| Phase 3: RTLtolerant.v | Successor liveness transition (Pitfall 1, 7) | Build match_rs_weaken lemma first; build In_transfer lemmas second; then fix instruction cases |
| Phase 3: RTLtolerant.v | Arity mismatch prevents compilation (Pitfall 4) | Fix all type errors first (compilation pass), then fix proof content (proof pass) |
| Phase 3: RTLtolerant.v | faulty_progress gives false confidence (Pitfall 13) | Fix step_simulation first |
| Phase 4: Complements.v | wc_function shape change propagates | Preserve constructor shape; only swap analysis premise |
| Phase 5: Validation | Sparse inference regression | Run color checker on test programs to confirm runtime behavior unchanged |

## Sources

- Direct analysis of `/home/alex/source/compcert/backend/RTLtolerant.v` (current broken proof state)
- Direct analysis of `/home/alex/source/compcert/backend/RTLcolorcheck.v` (Admitted proof at line 443)
- Direct analysis of `/home/alex/source/compcert/backend/RTLcolor.v` (wc_instruction/wc_function definitions)
- Direct analysis of `/home/alex/source/compcert/backend/Liveness.v` (transfer function, analyze_solution)
- Direct analysis of `/home/alex/source/compcert/backend/Deadcodeproof.v` (match_succ_states pattern, lines 537-555)
- [CompCert backend correctness proofs](https://xavierleroy.org/publi/compcert-backend.pdf) -- general simulation proof structure
- [Formally Verified Loop-Invariant Code Motion](https://hal.science/hal-03628646/document) -- CompCert pass proof patterns
- [A Fast Verified Liveness Analysis in SSA Form](https://link.springer.com/chapter/10.1007/978-3-030-51054-1_19) -- liveness analysis verification approaches
