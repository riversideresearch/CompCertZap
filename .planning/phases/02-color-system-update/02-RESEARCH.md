# Phase 2: Color System Update - Research

**Researched:** 2026-03-04
**Domain:** Coq formal verification -- RTL color system specification and verified Boolean checker
**Confidence:** HIGH

## Summary

Phase 2 replaces `Liveness.analyze` references with `ProofLiveness.analyze` in the color system (RTLcolor.v and RTLcolorcheck.v) and completes the `check_col_instr_sound` proof which is currently `Admitted`. The scope is surgical: two import swaps, three identifier renames, and one proof completion.

The proof completion is the main challenge. The file already contains a complete commented-out proof script (lines 249-442 of RTLcolorcheck.v) that worked against an older version using `PTree_Properties.for_all_correct`. The current code uses `Regset.for_all` instead, so the proof must use `Regset.for_all_2` (from the Coq FSet interface) as the bridge between the Boolean `Regset.for_all` and the propositional `Regset.For_all`. This bridge requires a trivial `compat_bool` obligation since `E.eq = eq` (Leibniz equality on `positive`).

**Primary recommendation:** Complete `check_col_instr_sound` by adapting the commented-out proof to use `Regset.for_all_2` instead of `PTree_Properties.for_all_correct`, then swap `Liveness` to `ProofLiveness` in both files.

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|-----------------|
| COLR-01 | RTLcolor.v references ProofLiveness.analyze instead of Liveness.analyze in wc_function | Direct import swap: change `Require Import Liveness` to `Require Import ProofLiveness`, rename `Liveness.analyze` to `ProofLiveness.analyze` on line 221 |
| COLR-02 | RTLcolorcheck.v references ProofLiveness.analyze instead of Liveness.analyze | Change import, rename on lines 446 and 484; `check_col_function_sound` premise and `check_function` body |
| COLR-03 | check_col_instr_sound proof completed with no Admitted | Adapt commented-out proof (lines 249-442) from `PTree_Properties.for_all_correct` pattern to `Regset.for_all_2` pattern; covers 14 instruction cases |
| COLR-04 | RTLcolor.vo and RTLcolorcheck.vo compile with zero Admitted | Verification via `make backend/RTLcolor.vo && make backend/RTLcolorcheck.vo` and grep for Admitted |
</phase_requirements>

## Standard Stack

### Core
| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| Coq | 8.20.0 | Proof assistant | Project's verified compiler toolchain |
| FSetAVL (Regset) | stdlib | Finite set with `for_all`/`For_all` bridge | CompCert uses `Regset := FSetAVL.Make(OrderedPositive)` |
| ProofLiveness | local (Phase 1) | Conservative backward liveness analysis | Phase 1 output; provides `analyze`, `analyze_solution`, `reg_list_live_in` |

### Key Lemmas Available
| Lemma | Module | Signature | Use |
|-------|--------|-----------|-----|
| `Regset.for_all_2` | FSetInterface.S | `compat_bool E.eq f -> for_all f s = true -> For_all (fun x => f x = true) s` | Bridge boolean checker to propositional spec |
| `eqb_sound` | RTLcolor | `c1 =? c2 = true -> c1 = c2` | Convert color equality checks to propositions |
| `is_colorb_sound` | RTLcolorcheck | `is_colorb x c = true -> is_color x c` | Convert color identity checks |
| `is_basicb_spec` | RTLcolorcheck | `reflect (is_basic c) (is_basicb c)` | Reflect basic color checks |
| `not_in_inb` | RTL | `~ In x l -> inb x l = true -> False` | Discharge membership contradictions |
| `Pos.eqb_eq` | stdlib | `Pos.eqb x y = true <-> x = y` | Convert positive equality checks |
| `is_protectedb_spec` | RTL | `reflect (is_protected op) (is_protectedb op)` | Case split on protected operations |
| `is_green_smove_builtinb_spec` | RTL | `reflect ...` | Case split on smove builtins |
| `is_blue_smove_builtinb_spec` | RTL | `reflect ...` | Case split on smove builtins |
| `is_vote_builtinb_spec` | RTL | `reflect ...` | Case split on vote builtins |
| `builtin_arg_forallb_sound` | Events | `builtin_arg_forallb f barg = true -> builtin_arg_forall (fun a => f a = true) barg` | Generic builtin arg reflection |
| `builtin_res_forallb_sound` | RTL | `builtin_res_forallb f bres = true -> builtin_res_forall (fun a => f a = true) bres` | Generic builtin res reflection |
| `builtin_arg_forall_impl` | Events | Monotonicity for builtin_arg_forall | Upgrade bool predicates to prop predicates |
| `builtin_res_forall_impl` | RTL | Monotonicity for builtin_res_forall | Upgrade bool predicates to prop predicates |
| `Forall_Exists_neg` | List (stdlib) | `Forall (fun x => ~ P x) l <-> ~(Exists P l)` | Generic builtin case: convert not-Exists to Forall-not |

## Architecture Patterns

### File Change Map
```
backend/RTLcolor.v         # COLR-01: swap Liveness -> ProofLiveness
  - Line 8:   Require Import Liveness -> ProofLiveness
  - Line 221: Liveness.analyze -> ProofLiveness.analyze

backend/RTLcolorcheck.v    # COLR-02, COLR-03: swap + complete proof
  - Line 7:   Require Import Liveness -> ProofLiveness
  - Line 443: Admitted -> complete proof
  - Line 446: Liveness.analyze -> ProofLiveness.analyze
  - Line 484: Liveness.analyze -> ProofLiveness.analyze
```

### Pattern 1: Regset.for_all_2 Bridge (replaces PTree_Properties.for_all_correct)

**What:** Convert `Regset.for_all f s = true` to `forall r, Regset.In r s -> f r = true`
**When to use:** Every instruction case in `check_col_instr_sound` where the checker uses `Regset.for_all`
**Example:**
```coq
(* Step 1: Prove compat_bool for the predicate *)
assert (Hcompat: compat_bool Regset.E.eq (fun r => col pc r =? col succ r)).
{ intros x y Hxy; subst; reflexivity. }

(* Step 2: Apply for_all_2 to get For_all *)
apply Regset.for_all_2 in Hcheck; [| exact Hcompat].

(* Step 3: For_all unfolds to forall x, In x s -> f x = true *)
(* Now Hcheck : forall r, Regset.In r (live !! pc) -> (col pc r =? col succ r) = true *)

(* Step 4: Use eqb_sound to get propositional equality *)
intros r Hr; apply eqb_sound; apply Hcheck; auto.
```

**Critical note:** Every lambda passed to `Regset.for_all` in `check_col_instr` needs its own `compat_bool` proof. Since `E.eq = eq`, all are trivially `intros x y Hxy; subst; reflexivity`.

### Pattern 2: Disjunction Discharge (unchanged from commented proof)

**What:** When the checker uses `inb r args || Pos.eqb r res || (col pc r =? col succ r)`, the proof case-splits on the disjuncts
**When to use:** Iop, Iload, Istore, Icall, Ibuiltin cases where the For_all body has exclusion conditions
**Example:**
```coq
(* From Regset.for_all_2: *)
(* Hpres : forall r, In r live -> inb r args || Pos.eqb r res || (col pc r =? col succ r) = true *)

(* Goal: forall r, In r live -> ~ In r args -> r <> res -> col pc r = col succ r *)
intros r Hlive Hnotin Hneq.
specialize (Hpres r Hlive).
apply orb_prop in Hpres; destruct Hpres as [Hpres | Hpres].
- apply orb_prop in Hpres; destruct Hpres as [Hpres | Hpres].
  + exfalso; eapply not_in_inb; eauto.
  + apply Pos.eqb_eq in Hpres; congruence.
- apply eqb_sound; auto.
```

### Pattern 3: Builtin Case Splitting

**What:** The Ibuiltin case first checks `is_green_smove_builtinb`, then `is_blue_smove_builtinb`, then `is_vote_builtinb`, then falls through to generic
**When to use:** The Ibuiltin instruction case
**Note:** The Ibuiltin case in `check_col_instr` produces 4 sub-cases matching 4 `wc_instruction` constructors. Each `reflect` lemma (`is_green_smove_builtinb_spec` etc.) case-splits on whether the builtin matches. The match on `bargs`/`bres` shapes (e.g., `BA arg :: nil, BR res`) uses `destruct` and `congruence` to eliminate impossible shapes.

### Anti-Patterns to Avoid

- **Do NOT use `PTree_Properties.for_all_correct`:** The old proof used this but the current code iterates over `Regset`, not `PTree`. Using it would be a type error.
- **Do NOT try to import both `Liveness` and `ProofLiveness`:** They define conflicting module names (`RegsetLat`, `DS`). Each file should import exactly one.
- **Do NOT change the `infer_coloring` parameter type:** It takes `PMap.t Regset.t` which is the output type of both `Liveness.analyze` and `ProofLiveness.analyze`. The extraction to OCaml is unchanged.

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Boolean-to-Prop bridge for Regset.for_all | Custom reflection lemma | `Regset.for_all_2` from FSet interface | Already proven in Coq stdlib, handles compat_bool |
| Color equality reflection | Manual case analysis | `eqb_sound`, `eqb_spec`, `is_colorb_sound` from RTLcolor/RTLcolorcheck | Already defined with correct types |
| Builtin arg/res reflection | Manual induction | `builtin_arg_forallb_sound`, `builtin_res_forallb_sound` | Defined in Events.v and RTL.v respectively |

## Common Pitfalls

### Pitfall 1: compat_bool Obligation
**What goes wrong:** `Regset.for_all_2` requires `compat_bool E.eq f` as first argument. Forgetting it causes a stuck proof.
**Why it happens:** `compat_bool` is `Proper (E.eq ==> Logic.eq) f`. Since `E.eq = eq` for Regset, this is trivial but must be explicitly provided.
**How to avoid:** For every `Regset.for_all_2` call, prove `compat_bool` inline: `intros x y Hxy; subst; reflexivity`. Consider defining a reusable Ltac tactic.
**Warning signs:** Goal contains `compat_bool Regset.E.eq ?f` that can't be discharged by `auto`.

### Pitfall 2: Proof Structure Mismatch with Commented-Out Script
**What goes wrong:** Blindly uncommenting the old proof script and expecting it to work.
**Why it happens:** The old proof used `PTree_Properties.for_all_correct` (iterating over PTree code map) but the current checker uses `Regset.for_all` (iterating over live set). The hypotheses have different types.
**How to avoid:** Follow the old proof's LOGIC but replace `PTree_Properties.for_all_correct` with `Regset.for_all_2` and adjust the hypothesis manipulation accordingly.
**Warning signs:** Type errors involving `PTree.t` vs `Regset.t`.

### Pitfall 3: Liveness Import Conflict
**What goes wrong:** Importing both `Liveness` and `ProofLiveness` causes "ambiguous name" errors.
**Why it happens:** Both define `RegsetLat`, `DS`, `transfer`, `analyze`, `analyze_solution` with the same short names.
**How to avoid:** Replace the import entirely: `Liveness` -> `ProofLiveness`. Qualify with `ProofLiveness.analyze` at usage sites.
**Warning signs:** "The reference analyze was not found" or "ambiguous name" errors.

### Pitfall 4: Downstream Rebuild Cascade
**What goes wrong:** After changing RTLcolor.v, all downstream files (RTLcolorcheck.v, RTLtolerant.v, Complements.v) need recompilation.
**Why it happens:** Changing the definition of `wc_function` changes its type. Any file pattern-matching on `wc_function` will need to provide the new premise.
**How to avoid:** Phase 2 should ONLY change RTLcolor.v and RTLcolorcheck.v. Phase 3 handles RTLtolerant.v. Complements.v is Phase 4.
**Warning signs:** Build errors in files not targeted by this phase (expected; will be fixed in later phases).

### Pitfall 5: check_col_function_sound Premise
**What goes wrong:** Forgetting to update the `check_col_function_sound` lemma premise from `Liveness.analyze f = Some live` to `ProofLiveness.analyze f = Some live`.
**Why it happens:** This lemma sits in the `color_checker` section (which already has `live` as a variable), so the reference to `Liveness.analyze` is in the premise, not computed from the section variable.
**How to avoid:** Update line 446 alongside the import swap.
**Warning signs:** Type mismatch between `wc_function` (which now requires `ProofLiveness.analyze`) and the premise.

## Code Examples

### Example 1: Inop Case (simplest)

The full proof for the `Inop` case, showing the `Regset.for_all_2` pattern:

```coq
(* check_col_instr returns: Regset.for_all (fun r => col pc r =? col succ r) (live !! pc) *)
(* wc_instruction requires: Regset.For_all (fun r => col pc r = col succ r) (live !! pc) *)

- (* Inop *)
  constructor.
  apply Regset.for_all_2 in Hcheck.
  + intros r Hr. apply eqb_sound. apply Hcheck. exact Hr.
  + intros x y Hxy; subst; reflexivity.
```

### Example 2: Iop Safe Case (with disjunction discharge)

```coq
- (* Iop, not protected *)
  destruct (is_protectedb_spec o); [congruence|].
  destruct_andb Hcheck Hpres.
  destruct_andb Hr Hargs.
  rewrite forallb_forall in Hargs.
  apply Regset.for_all_2 in Hpres; [| intros x y Hxy; subst; reflexivity].
  apply wc_Iop_safe; auto.
  + apply is_basicb_spec; auto. (* or destruct (is_basicb_spec ...) *)
  + apply Forall_forall; intros x Hin.
    apply eqb_sound; auto.
  + intros r Hr Hneq.
    specialize (Hpres r Hr).
    apply orb_prop in Hpres; destruct Hpres as [Hpres | Hpres].
    * apply Pos.eqb_eq in Hpres; congruence.
    * apply eqb_sound; auto.
```

### Example 3: Import and Reference Changes in RTLcolor.v

```coq
(* Before *)
Require Import Liveness.
...
Inductive wc_function col : function -> Prop :=
  wc_function_function : forall f live
      (WC_LIVE: Liveness.analyze f = Some live)
      ...

(* After *)
Require Import ProofLiveness.
...
Inductive wc_function col : function -> Prop :=
  wc_function_function : forall f live
      (WC_LIVE: ProofLiveness.analyze f = Some live)
      ...
```

### Example 4: check_function Change in RTLcolorcheck.v

```coq
(* Before *)
Definition check_function (f : function) : bool :=
  match Liveness.analyze f with
  ...

(* After *)
Definition check_function (f : function) : bool :=
  match ProofLiveness.analyze f with
  ...
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| PTree-based color iteration (`PTree_Properties.for_all`) | Regset-based live set iteration (`Regset.for_all`) | Before this project | Proof must use `Regset.for_all_2` instead of `PTree_Properties.for_all_correct` |
| Standard `Liveness.analyze` for color system | `ProofLiveness.analyze` (conservative) | Phase 1 (this project) | Live sets are larger; all Iop/Iload args always live |
| `check_col_instr_sound` Admitted | Must be fully proved | Phase 2 (this task) | Required for COLR-03 and zero-Admitted goal |

**Deprecated/outdated:**
- The commented-out proof (lines 249-442) in RTLcolorcheck.v: logically correct but written for `PTree_Properties.for_all_correct`. Must be adapted, not simply uncommented.

## Open Questions

1. **Ltac Tactic for compat_bool**
   - What we know: Every `Regset.for_all_2` call needs `compat_bool` proof, always discharged the same way
   - What's unclear: Whether a single Ltac `solve_compat` tactic is worth defining vs. inline proof
   - Recommendation: Define inline if fewer than 5 uses; define a local Ltac if more. There are ~14 instruction cases, most using `Regset.for_all`, so a tactic is worthwhile.

2. **Existing destruct_andb/destruct_orb Ltac**
   - What we know: RTLcolorcheck.v already defines `destruct_andb` and `destruct_orb` Ltac tactics (lines 235-243)
   - What's unclear: Whether these need modification
   - Recommendation: Use as-is; they match the current code structure perfectly.

## Validation Architecture

### Test Framework
| Property | Value |
|----------|-------|
| Framework | Coq 8.20.0 proof checker |
| Config file | _CoqProject |
| Quick run command | `make backend/RTLcolor.vo && make backend/RTLcolorcheck.vo` |
| Full suite command | `make proof` |

### Phase Requirements -> Test Map
| Req ID | Behavior | Test Type | Automated Command | File Exists? |
|--------|----------|-----------|-------------------|-------------|
| COLR-01 | wc_function uses ProofLiveness.analyze | unit (build) | `make backend/RTLcolor.vo` | Yes (source exists) |
| COLR-02 | check_function uses ProofLiveness.analyze | unit (build) | `make backend/RTLcolorcheck.vo` | Yes (source exists) |
| COLR-03 | check_col_instr_sound fully proved | unit (build + grep) | `make backend/RTLcolorcheck.vo && ! grep -q '^[^(]*Admitted' backend/RTLcolorcheck.v` | Yes (source exists) |
| COLR-04 | Both files compile with zero Admitted | integration | `make backend/RTLcolor.vo && make backend/RTLcolorcheck.vo && ! grep '^[^(]*Admitted' backend/RTLcolor.v backend/RTLcolorcheck.v` | Yes |

### Sampling Rate
- **Per task commit:** `make backend/RTLcolor.vo && make backend/RTLcolorcheck.vo`
- **Per wave merge:** `make backend/RTLcolor.vo && make backend/RTLcolorcheck.vo`
- **Phase gate:** Both .vo files build + zero uncommented Admitted in both source files

### Wave 0 Gaps
None -- existing build infrastructure covers all phase requirements. Both source files exist and the Makefile already registers ProofLiveness.v.

## Sources

### Primary (HIGH confidence)
- Direct code inspection of `backend/RTLcolor.v` (248 lines) -- wc_function definition at line 219-224
- Direct code inspection of `backend/RTLcolorcheck.v` (523 lines) -- check_col_instr at 81-220, Admitted at 443, check_function at 483-491
- Direct code inspection of `backend/ProofLiveness.v` (132 lines) -- Phase 1 output, verified builds
- Coq 8.20.0 FSetInterface.v -- `for_all_2` signature at line 222-224
- Coq 8.20.0 FSetFacts.v -- `for_all_iff` at line 123-127
- Coq 8.20.0 SetoidList.v -- `compat_bool` definition at line 1100-1101
- Direct code inspection of `backend/RTL.v` -- `inb`, `not_in_inb`, `inb_spec`, `in_builtin_argb_sound`, builtin reflect lemmas

### Secondary (MEDIUM confidence)
- Commented-out proof script in RTLcolorcheck.v (lines 249-442) -- verified logically sound by inspection but needs PTree->Regset adaptation

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH -- all libraries are already in use, versions verified via `coqc --version`
- Architecture: HIGH -- changes are mechanical (import swap + identifier rename) except for proof completion
- Proof completion: HIGH -- commented-out proof provides complete logical structure; only the boolean-to-prop bridge mechanism changes (PTree_Properties -> Regset.for_all_2)
- Pitfalls: HIGH -- all pitfalls identified from direct code analysis and STATE.md blockers

**Research date:** 2026-03-04
**Valid until:** 2026-04-04 (stable Coq project, no external dependencies changing)
