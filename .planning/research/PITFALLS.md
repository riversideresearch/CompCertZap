# Domain Pitfalls

**Domain:** Relaxing conservative builtin treatment in a verified compiler with fault-tolerance proofs
**Researched:** 2026-03-14

## Critical Pitfalls

Mistakes that cause proof breakage requiring significant rework or force reverting the approach entirely.

### Pitfall 1: val_compat vs Val.lessdef mismatch in the fault model

**What goes wrong:** The `builtin_function_sem_lessdef` lemma in `common/Builtins.v` speaks about `Val.lessdef`, but the fault model in `RTLfault.v` corrupts register values via `val_compat` -- which is strictly weaker than `Val.lessdef`. A faulted register `Vint 42` can become `Vint 99` under `val_compat`, but `Val.lessdef` only allows `Vundef -> anything`. The existing lemma may not be sufficient for the faulted-builtin case in `RTLtolerant.v`.

**Why it happens:** The `builtin_function_sem_lessdef` lemma was designed for standard CompCert compilation passes, which use `Val.lessdef` to relate source and target values. The fault model uses a different, incompatible relation. It is tempting to assume "lessdef is close enough" without validating the exact gap.

**Consequences:** If the semantic property gap is discovered late (after TMR pass and coloring changes are done), all that work is wasted. The tolerant proof case will be stuck, unable to show that a safe builtin produces `Some ...` on `val_compat`-corrupted inputs, or unable to show the output is `val_compat`-related to the non-faulted output.

**Prevention:**
1. State the exact property needed before writing any pass changes. The property is approximately: "For safe builtins, if `builtin_function_sem b vargs = Some vres` and `Forall2 val_compat vargs vargs'`, then `builtin_function_sem b vargs' = Some vres'` and `val_compat vres vres'`." This is a `val_compat` analog of `builtin_function_sem_lessdef`.
2. Prove this property first (Phase 2 in the plan) as a standalone lemma.
3. Inspect each safe builtin's semantics in `Builtins0.v` to confirm totality under type-compatible but value-different inputs. The `mkbuiltin_n1t` family (e.g., `BI_fabs`, `BI_negl`, `BI_i16_bswap`) is straightforward because the underlying function is total and the result type is determined by the input type. The `mkbuiltin_v2t` family (e.g., `BI_addl`, `BI_mull`) is also fine because `Val.addl` etc. return type-compatible outputs on type-compatible inputs (see existing `val_compat_addl`, `val_compat_mull` lemmas in `RTLfault.v`).
4. The partial builtins (`mkbuiltin_n1p`, `mkbuiltin_v2p`) must remain excluded -- they return `None` on certain inputs, and a `val_compat`-corrupted input could hit the `None` branch when the original did not.

**Detection:** Attempt the key lemma statement early. If it does not go through for a candidate builtin, that builtin is not safe to replicate. If `proj_num` dispatches on the value constructor and the type matches, the proof should be straightforward; if not, something is wrong with the classification.

**Which phase should address it:** Phase 2 (Validate the proof-critical semantic property early). This is the plan's designated risk-retirement step. Do not skip it.

### Pitfall 2: Inconsistency between the five classification consumers

**What goes wrong:** The TMR pass, faulty RTL semantics, color specification, color checker, and color oracle each make independent decisions about which builtins are safe. If any one of them disagrees with the others, the overall proof breaks. For example: if the oracle assigns basic colors to a builtin that the color spec's `wc_Ibuiltin` rule forces to White, the checker rejects the oracle's output. Or: if the TMR pass replicates a builtin but `zap_allowed` does not permit faults on it, the tolerant proof has an impossible case.

**Why it happens:** The five components live in five different files (`RTLtmr.v`, `RTLfault.v`, `RTLcolor.v`, `RTLcolorcheck.v`, `RTLinfercolor.ml`) and historically did not need to agree because all builtins were uniformly conservative. Adding a split requires coordination across all five, and it is easy to update one but forget another, especially the unverified OCaml oracle.

**Consequences:** Subtle proof failures that manifest far from their root cause. A mismatch between `zap_allowed` and the color spec might only surface when building `RTLtolerant.vo`, at which point the developer has to trace back through several layers. A mismatch involving the oracle will not cause a Coq proof failure but will cause the compiler to reject valid programs at runtime.

**Prevention:**
1. Define `builtin_can_replicate` and `builtin_can_fault` exactly once in `common/Builtins.v`, as proposed in the plan.
2. All five consumers must consume these predicates directly rather than reimplementing the classification. The TMR pass should branch on `builtin_can_replicate ef`. The `zap_allowed` definition should branch on `builtin_can_fault ef`. The color spec should have two `wc_Ibuiltin` rules gated by `builtin_can_replicate`.
3. After each phase, verify that the affected `.vo` files rebuild. The minimum rebuild set after each phase is documented in the plan.
4. For the OCaml oracle: add a runtime assertion that the oracle's output for builtins is consistent with `builtin_can_replicate`. The checker will catch errors anyway, but an assertion gives faster feedback during development.

**Detection:** Build all five `.vo` files together after each change. If one builds but another does not, look for a classification mismatch. If `RTLtolerant.vo` fails with an unresolvable case, check whether `zap_allowed` and the color spec agree.

**Which phase should address it:** Phase 1 (shared classification definition) prevents this structurally. Phases 3-5 must consume the shared definition and rebuild incrementally.

### Pitfall 3: maybe_zap_preserves_match_states requires is_basic for new cases

**What goes wrong:** The `maybe_zap_preserves_match_states` lemma in `RTLtolerant.v` (line 256) proves that after a fault (zap), the match relation is preserved. The critical step is showing `is_basic (col pc' r)` for the result register of the zapped instruction. This is done by inverting `wc_instruction` (line 279: `inv_wc; simpl in *; try congruence; inv H2; inv Hstep; try contradiction. inv H4; constructor.`). Currently, `Ibuiltin` is never zapped, so this inversion never needs to handle a builtin case. When `zap_allowed` is relaxed for safe builtins, this inversion must handle the new `wc_Ibuiltin_safe` case and extract `is_basic (col succ res)` from it.

**Why it happens:** The `inv_wc` tactic does a blanket inversion of `wc_instruction` and relies on contradictions or congruence to eliminate impossible cases. Adding a new `wc_Ibuiltin_safe` constructor creates a new case that is not impossible and must be handled explicitly. The tactic may silently leave an unresolved subgoal or, worse, resolve it incorrectly.

**Consequences:** The `maybe_zap_preserves_match_states` proof breaks, and the developer may not immediately understand why. The fix is to handle the new case in the `inv_wc` tactic or directly in the proof, but this requires understanding the tactic's behavior on the expanded inductive.

**Prevention:**
1. When adding `wc_Ibuiltin_safe` to `RTLcolor.v`, immediately check that `maybe_zap_preserves_match_states` still builds.
2. The new `wc_Ibuiltin_safe` rule must include `is_basic (col succ res)` as a premise (analogous to `wc_Iop_safe`'s `is_basic (col succ res)`). This is the premise that `maybe_zap_preserves_match_states` will extract.
3. If the `inv_wc` tactic does not automatically resolve the new case, add an explicit branch in the proof.

**Detection:** Rebuild `RTLtolerant.vo` immediately after modifying the `wc_instruction` inductive. If the proof hangs or fails at `maybe_zap_preserves_match_states`, the new constructor is the cause.

**Which phase should address it:** Phase 4 (color spec update) introduces the new constructor, but the impact manifests in Phase 5 (tolerant proof). Test the rebuild after Phase 4, not just after Phase 5.

### Pitfall 4: Builtin argument encoding differs from Iop arguments

**What goes wrong:** `Iop` instructions take a flat `list reg` as arguments. `Ibuiltin` instructions take `list (builtin_arg reg)` which can contain `BA r`, `BA_int n`, `BA_long n`, `BA_addrstack ofs`, `BA_addrglobal id ofs`, `BA_splitlong`, and other compound argument forms. The TMR proof for `Iop` uses `match_regsets` to relate source and target register states via a flat register list. Extending this to builtins requires handling `builtin_arg` trees, where registers are interleaved with constants and compound expressions.

**Why it happens:** The existing `Iop` proof pattern in `RTLtmrproof.v` (line 1776+) uses `match_regs_1_2_eval_operation` and `match_regs_1_3_eval_operation` which operate on flat register lists mapped through `rm`. For builtins, the argument remapping must use `AST.map_builtin_arg` to remap registers inside `builtin_arg` trees, and the proof must use `eval_builtin_arg_proper` (line 1195) instead of the flat list lemmas. These are structurally different proof obligations.

**Consequences:** The TMR proof case for safe builtins does not follow the `Iop` pattern as closely as expected. The developer may start by copy-pasting the `Iop` proof and then discover that the argument handling is fundamentally different, requiring new lemmas about `map_builtin_arg` and `eval_builtin_arg` composition.

**Prevention:**
1. Do not assume the `Iop` proof pattern transfers directly. Plan for the argument-handling difference from the start.
2. The TMR pass already has `eval_builtin_args_proper` (line 1207) for showing that register remapping preserves `eval_builtin_args`. Use this existing lemma rather than trying to flatten builtin args.
3. The TMR spec (`RTLtmrspec.v`) already has `match_Ibuiltin_2` which handles builtins with a result register. The new `match_Ibuiltin_safe` case must mirror the structure of `match_Iop_safe` (three copies in the code) but using `map_builtin_arg` on the argument list. Verify that `map_builtin_arg (fun r => fst (rm # r))` and `map_builtin_arg (fun r => snd (rm # r))` produce the right shadow-world argument lists.
4. Check that `eval_builtin_arg` on the remapped argument produces the same value, given `match_regsets`.

**Detection:** When writing the `match_Ibuiltin_safe` constructor in `RTLtmrspec.v`, check that the generated code shape is expressible and that `eval_builtin_arg_proper` can relate the shadow execution to the original.

**Which phase should address it:** Phase 3 (TMR pass, spec, and proof update).


## Moderate Pitfalls

### Pitfall 5: The builtin_res complication (BR vs BR_none vs BR_splitlong)

**What goes wrong:** `Iop` instructions always have exactly one result register. `Ibuiltin` instructions have a `builtin_res` which can be `BR r`, `BR_none`, or `BR_splitlong (BR rhi) (BR rlo)`. The `res_of_instruction` function (in `RTL.v`, line 780) uses `reg_of_builtin_res` which returns `None` for `BR_none` and `BR_splitlong`. When `zap_allowed` is relaxed, `maybe_zap` uses `res_of_instruction` to find the register to corrupt. For `BR_none` builtins, there is no register to corrupt, so `maybe_zap` cannot fire (which is fine). But `BR_splitlong` is problematic: it has two result registers, and `maybe_zap` can only corrupt one.

**Prevention:**
1. For the first implementation, restrict safe builtins to those with `BR r` result encoding. This excludes `BR_splitlong` cases.
2. Document this restriction in `builtin_can_replicate` so that `BR_splitlong` builtins are conservatively excluded even if their semantics are total.
3. If `BR_splitlong` support is needed later, it requires a separate `maybe_zap` extension -- not part of this patch.

**Detection:** Check that no builtin in the safe list can produce `BR_splitlong` as its result encoding. On x86-64, `BR_splitlong` is rare for the listed safe builtins, but verify this explicitly.

### Pitfall 6: Platform builtin divergence across architectures

**What goes wrong:** The safe-builtin whitelist includes platform builtins (e.g., `BI_fmin`, `BI_fmax` on x86). Other architectures (RISC-V, aarch64) have different platform builtins with different semantics. A classification that works for x86 may silently misclassify a RISC-V platform builtin, either allowing an unsafe builtin to be replicated or refusing to replicate a safe one.

**Prevention:**
1. `builtin_can_replicate_bf` should dispatch on `BI_standard` vs `BI_platform` vs `BI_replicate`. For `BI_platform`, the classification must be defined in the platform-specific `Builtins1.v` file (e.g., `x86/Builtins1.v`), not assumed from the standard list.
2. For the first implementation, classify all platform builtins as unsafe (not replicable) unless they have been individually validated. Only add x86 platform builtins (like `BI_fmin`, `BI_fmax`) if their semantics have been checked against the `val_compat` model.
3. Add a comment in `builtin_can_replicate` noting that platform builtins must be validated per-architecture.

**Detection:** Build with each configured architecture to check that the classification compiles. The Coq type system will force handling of all platform builtin constructors, so a missing case will be caught.

### Pitfall 7: The Three/Two vote_type parametrization complication

**What goes wrong:** CompCert's fault-tolerance extension parametrizes all semantics by `vote_type` (either `Two` or `Three`). The tolerant proof relates `Three`-voting execution (source) to `Two`-voting faulty execution (target). The `known_builtin_sem_Three_Two'` lemma (RTLtolerant.v, line 387) converts between the two vote types. For standard and platform builtins, this is trivial (both vote types give the same semantics). But the proof must handle the `BI_replicate` case separately because replicate builtins (vote, smove) have vote-type-dependent semantics.

When adding a new safe-builtin case to the tolerant proof, the developer must ensure the `external_call_Three_Two'` conversion still works. For standard/platform builtins classified as safe, the `known_builtin_sem` wrapper guarantees `E0` trace and unchanged memory, and the Three/Two conversion is straightforward. But if a replicate builtin accidentally enters the safe class, the proof breaks because `known_builtin_sem_Three_Two'` has a complex case split for replicate builtins (line 382-384).

**Prevention:**
1. The `builtin_can_replicate` predicate must explicitly exclude all `BI_replicate` builtins (smove, vote, check). This is already part of the plan but must be enforced structurally, not just by convention.
2. Verify that `builtin_can_replicate (EF_builtin name sg) = true` implies `lookup_builtin_function name sg` returns `Some (BI_standard _)` or `Some (BI_platform _)`, never `Some (BI_replicate _)`.
3. Add a lemma: `builtin_can_replicate ef = true -> ~ is_green_smove_builtin ef /\ ~ is_blue_smove_builtin ef /\ ~ is_vote_builtin ef`. This ensures the tolerant proof can eliminate protocol-builtin cases when handling the safe-builtin case.

**Detection:** If the tolerant proof's new safe-builtin case generates a `BI_replicate` subgoal that cannot be dismissed by contradiction, a replicate builtin has leaked into the safe class.

### Pitfall 8: Color preservation across instruction successors (Regset.For_all obligation)

**What goes wrong:** Every `wc_instruction` rule includes a `Regset.For_all` clause that specifies how colors are preserved from the instruction's PC to its successor's PC for live registers other than those explicitly modified. For the new `wc_Ibuiltin_safe` rule, this clause must correctly specify which registers are "modified" and which are "preserved." Getting this wrong means the tolerant proof cannot maintain its `match_rs` invariant across safe-builtin steps.

Specifically, for safe (replicated) builtins: the result register changes color (to a basic color), the argument registers may or may not change color, and all other live registers must preserve their color. The `Iop` rule (`wc_Iop_safe`, line 118) requires `Forall (fun arg => col pc arg = col succ res) args` -- all arguments must have the same color as the result at the successor. If the `wc_Ibuiltin_safe` rule does not impose an analogous constraint on builtin_arg registers, the tolerant proof will be unable to establish `match_rs` at the successor.

**Prevention:**
1. Model `wc_Ibuiltin_safe` as closely as possible on `wc_Iop_safe`:
   - `is_basic (col succ res)` -- result gets a basic color
   - All registers in `builtin_arg` have the same basic color as the result
   - `Regset.For_all (fun r => r <> res -> ~ Exists (in_builtin_arg r) bargs -> col pc r = col succ r) (live !! pc)` -- non-modified registers preserve color
2. Verify that this rule is accepted by the checker and can be inferred by the oracle.
3. Test the rule against the tolerant proof's `match_rs` maintenance before finalizing.

**Detection:** If the tolerant proof's safe-builtin case cannot apply `RS` (the register-set matching hypothesis) for argument registers, the color rule is too weak.

### Pitfall 9: Existing proof structure assumes all generic builtins are White

**What goes wrong:** The tolerant proof's existing `exec_Ibuiltin` case (line 904-1012) has a two-way split: vote builtins vs everything else. The "everything else" branch (line 968-1012) assumes all builtin arguments are White (via `wc_Ibuiltin`'s `Forall (builtin_arg_forall (fun r => col pc r = White)) bargs`). This means it can use `RS` unconditionally for all arguments regardless of the faulted color `c`, because `White <> c` for any basic color `c`. When a new `wc_Ibuiltin_safe` case is added where arguments have basic colors instead of White, the "everything else" branch must be split further, and the argument lessdef reasoning changes from unconditional to conditional on color mismatch.

**Prevention:**
1. The tolerant proof's `exec_Ibuiltin` case must become a three-way (or more) split: vote builtins, safe replicated builtins, other builtins. The safe-builtin case mirrors the existing `Iop` case logic rather than the existing general-builtin logic.
2. In the safe-builtin case, `RS` can only be applied to argument registers whose color differs from the faulted color `c`. This is the same pattern as `Iop` (where argument colors equal the result's basic color, and the faulted color exempts one color).
3. Audit the `inv_wc` tactic and any `simpl in *; try congruence` patterns in the proof for assumptions that only apply to White-colored arguments.

**Detection:** When building the new case, if `apply RS` fails because the color hypothesis cannot be discharged, the old White assumption has leaked into the new case.


## Minor Pitfalls

### Pitfall 10: The dedup function in argument vote generation

**What goes wrong:** The TMR pass uses `dedup (args_of_instruction instr)` to remove duplicate registers before generating majority votes. For `Ibuiltin`, `args_of_instruction` extracts registers from `builtin_arg` trees. If a safe builtin is replicated (not majority-voted), this code path is bypassed. But if the developer accidentally routes safe builtins through the majority-vote path instead of the replication path, `dedup` and `args_of_instruction` interact with `builtin_arg` in unexpected ways.

**Prevention:** When modifying `transf_instr` in `RTLtmr.v`, add the new safe-builtin case as a distinct match branch, not as a modification to the existing catch-all `_ =>` branch. The safe-builtin path should never call `maj_vote_regs`.

### Pitfall 11: Proof script brittleness from hypothesis name dependencies

**What goes wrong:** The tolerant proof uses `inv_wc`, `inv_rs`, and `apply_RS` Ltac tactics that match on hypothesis shapes. Adding new constructors to `wc_instruction` or new cases to `match_rs` changes the set of hypotheses produced by inversion, which can silently break these tactics or cause them to pick the wrong hypothesis.

**Prevention:**
1. Before modifying the `wc_instruction` inductive, identify all tactics in `RTLtolerant.v` that invert it (search for `inv_wc` and any direct `inv` on `wc_instruction` or `wc_code`).
2. After adding `wc_Ibuiltin_safe`, re-run the entire tolerant proof. Do not assume that only the `exec_Ibuiltin` case is affected -- tactics in other cases may also invert `wc_instruction` and need to handle the new constructor.
3. Consider naming key hypotheses explicitly in the proof script rather than relying on positional matching.

### Pitfall 12: External call memory effects assumption

**What goes wrong:** The tolerant proof relies on `external_call_mem_extends` to lift memory extensions through external calls. For safe builtins, `known_builtin_sem` guarantees `E0` trace and unchanged memory (`m' = m`). This means `external_call_mem_extends` is trivially satisfied. But if a builtin is misclassified as safe when it actually modifies memory (e.g., an `EF_builtin` that falls through to `external_functions_sem` because `lookup_builtin_function` returns `None`), the memory extension cannot be maintained.

**Prevention:** The `builtin_can_replicate` predicate must check `lookup_builtin_function` returns `Some _`. Add a lemma: `builtin_can_replicate ef = true -> exists bf, lookup_builtin_function name sg = Some bf` (for the `EF_builtin name sg` case). This ensures the builtin routes through `known_builtin_sem`, which guarantees no memory effects.


## Phase-Specific Warnings

| Phase Topic | Likely Pitfall | Mitigation |
|-------------|---------------|------------|
| Phase 1: Shared classification | Pitfall 2 (inconsistency), Pitfall 6 (platform divergence), Pitfall 7 (replicate exclusion) | Single definition point, explicit exclusion of BI_replicate, conservative default for platform builtins |
| Phase 2: Semantic validation | Pitfall 1 (val_compat vs lessdef), Pitfall 5 (BR_splitlong) | Prove val_compat analog of builtin_function_sem_lessdef first; restrict to BR results |
| Phase 3: TMR pass/spec/proof | Pitfall 4 (builtin_arg encoding), Pitfall 10 (dedup interaction) | Use map_builtin_arg and eval_builtin_arg_proper; separate match branch for safe builtins |
| Phase 4: Color system | Pitfall 3 (maybe_zap is_basic), Pitfall 8 (For_all obligation) | Model wc_Ibuiltin_safe on wc_Iop_safe; test maybe_zap rebuild immediately |
| Phase 5: Faulty RTL and tolerant proof | Pitfall 1 (semantic property), Pitfall 9 (White assumption), Pitfall 11 (tactic brittleness) | Use validated semantic lemma from Phase 2; three-way case split; test all existing cases rebuild |

## Sources

- `common/Builtins.v`: `builtin_function_sem_lessdef` lemma (lines 62-72)
- `common/Builtins0.v`: `mkbuiltin_n1t` / `mkbuiltin_n1p` split (lines 255-322), `standard_builtin_sem` (lines 460-502)
- `common/Events.v`: `known_builtin_sem` (lines 1424-1428), `builtin_or_external_sem` (lines 1506-1510)
- `backend/RTLfault.v`: `val_compat` (lines 21-27), `zap_allowed` (lines 52-61), `maybe_zap` (lines 63-73), existing `val_compat_*` lemmas (lines 116-757)
- `backend/RTLtolerant.v`: `match_rs` (lines 24-30), `maybe_zap_preserves_match_states` (lines 256-285), `exec_Ibuiltin` non-faulted case (lines 904-1012), `exec_Ibuiltin` faulted case (lines 1503-1818)
- `backend/RTLcolor.v`: `wc_Iop_safe` (lines 118-123), `wc_Ibuiltin` (lines 181-191)
- `backend/RTLtmr.v`: `transf_instr` (lines 179-223), safe `Iop` replication (lines 196-209)
- `backend/RTLtmrspec.v`: `match_Iop_safe` (lines 156-164), `match_Ibuiltin_2` (lines 204-210)
- `backend/RTLtmrproof.v`: `exec_Iop` proof case (lines 1776-1830), `eval_builtin_arg_proper` (lines 1195-1222)
- `plans/builtin-treatment-plan.md`: Risk assessment, implementation order, expected proof difficulty
