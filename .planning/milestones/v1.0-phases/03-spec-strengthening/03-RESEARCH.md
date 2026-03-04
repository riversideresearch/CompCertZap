# Phase 3: Spec Strengthening - Research

**Researched:** 2026-03-03
**Domain:** Coq proof refactoring -- separating algorithm specification from invariant consequences in RTL replication specs
**Confidence:** HIGH

## Summary

Phase 3 targets the monolithic `replication_map_wf_aux` lemmas in `RTLdmrspec.v` (lines 813-915, ~102 lines) and `RTLtmrspec.v` (lines 929-1057, ~128 lines). Both prove the same combined result: given the `foldM` that allocates shadow registers, the resulting map satisfies `rm_wf` AND the allocated registers fall within a range. The TODO comments in both files explicitly call for factoring this into (1) a relational specification of the algorithm and (2) a proof that the spec implies `rm_wf`.

The key structural insight is that `replication_map_wf_aux` currently proves two distinct things in a single induction:
- **Algorithmic correctness:** each step of `foldM` extends the map with fresh registers in the expected way (the `Forall` clause about register ranges)
- **Invariant consequence:** the resulting map satisfies `rm_wf` (the NoDup distinctness property)

These are tangled because the NoDup proof for `rm_wf` requires knowing register ranges (to prove distinctness via `lia`), but the range information is an independent fact about the `foldM` computation. Separating them into a relational spec (`replication_map_rel`) that captures the range invariant, then deriving `rm_wf` as a consequence, will make both proofs cleaner and more maintainable.

**Primary recommendation:** Define a `replication_map_rel` inductive that captures per-step register allocation (each original register maps to fresh shadows in a known range), prove `foldM_satisfies_rel` that the `foldM` produces a map satisfying this relation, then prove `rel_implies_rm_wf` that the relation implies `rm_wf`. Replace `replication_map_wf_aux` with their composition.

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|-----------------|
| SPEC-01 | Relational spec defined for DMR replication-map construction in RTLdmrspec.v | Architecture Pattern 1: `replication_map_rel` inductive with DMR arity (`PMap.t reg`), single shadow register per original |
| SPEC-02 | Relational spec defined for TMR replication-map construction in RTLtmrspec.v | Architecture Pattern 1: `replication_map_rel` inductive with TMR arity (`PMap.t (reg * reg)`), two shadow registers per original |
| SPEC-03 | Monolithic `replication_map_wf_aux` proof in RTLdmrspec.v replaced with spec + impl + consequence composition | Architecture Pattern 2: `foldM_satisfies_rel` + `rel_implies_rm_wf` compose to replace `replication_map_wf_aux` |
| SPEC-04 | Monolithic `replication_map_wf_aux` proof in RTLtmrspec.v replaced with spec + impl + consequence composition | Architecture Pattern 2: same decomposition for TMR variant |
</phase_requirements>

## Standard Stack

### Core

| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| Coq | (project version) | Proof assistant | Already in use; all proofs must compile with existing Coq setup |
| CompCert RTLgen monad | N/A | `foldM`, `new_reg`, `state_incr` | The monadic infrastructure the specs are built on |
| PMap / PTree | N/A | Map data structures for register mappings | `PMap.t reg` (DMR) and `PMap.t (reg * reg)` (TMR) |

### Supporting

| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| Coqlib | N/A | `Forall`, list utilities, `Ple`, `Plt` | Used throughout for list reasoning |
| NoDup (from Coq stdlib) | N/A | Distinctness predicates | Core of `rm_wf` definition |

## Architecture Patterns

### Recommended Decomposition Structure

For each file (DMR and TMR), the refactoring introduces three new definitions/lemmas and removes one:

```
(* NEW: Relational specification *)
Inductive replication_map_rel : ... -> Prop :=

(* NEW: foldM produces a map satisfying the relation *)
Lemma foldM_satisfies_rel : ...

(* NEW: The relation implies rm_wf *)
Lemma rel_implies_rm_wf : ...

(* REPLACED: replication_map_wf_aux now trivially composes the above *)
Lemma replication_map_wf_aux : ... (* or deleted entirely *)
```

### Pattern 1: Relational Specification (replication_map_rel)

**What:** An inductive relation capturing the per-step invariant of the `foldM` that builds the replication map. It encodes what each register maps to and the range of the allocated shadow registers, WITHOUT reasoning about NoDup.

**DMR variant** (each register gets one shadow):
```coq
(* In RTLdmrspec.v *)
Inductive replication_map_rel
  : list reg -> PMap.t reg -> positive -> positive -> Prop :=
| rmr_nil :
  forall rm lo,
    replication_map_rel [] rm lo lo
| rmr_cons :
  forall r regs rm lo hi,
    replication_map_rel regs rm lo hi ->
    rm # r = hi ->
    replication_map_rel (r :: regs) rm lo (Pos.succ hi).
```

The key insight: `lo` and `hi` track the register range. For the head element `r`, `rm # r = hi` (the next available register), and the range advances by one (`Pos.succ hi`). The tail was built by the recursive `foldM` call, which already consumed `[lo, hi)`.

Wait -- the `foldM` in RTLgen processes the list with the head processed LAST (it recurses on the tail first via `do a' <- foldM f xs a; f a' x`). So the head is allocated after the tail. This means:

```coq
(* DMR: foldM processes tail first, then head *)
Inductive replication_map_rel
  : list reg -> PMap.t reg -> positive -> positive -> Prop :=
| rmr_nil :
  forall rm lo,
    replication_map_rel [] rm lo lo
| rmr_cons :
  forall r regs rm lo mid hi,
    replication_map_rel regs rm lo mid ->
    (* Head register r gets shadow at mid *)
    rm # r = mid ->
    hi = Pos.succ mid ->
    replication_map_rel (r :: regs) rm lo hi.
```

**TMR variant** (each register gets two shadows):
```coq
(* In RTLtmrspec.v *)
Inductive replication_map_rel
  : list reg -> PMap.t (reg * reg) -> positive -> positive -> Prop :=
| rmr_nil :
  forall rm lo,
    replication_map_rel [] rm lo lo
| rmr_cons :
  forall r regs rm lo mid hi r2 r3,
    replication_map_rel regs rm lo mid ->
    rm # r = (r2, r3) ->
    r2 = mid ->
    r3 = Pos.succ mid ->
    hi = Pos.succ (Pos.succ mid) ->
    replication_map_rel (r :: regs) rm lo hi.
```

**When to use:** This is the central new abstraction. It captures the essential structure of the foldM output without mixing in the NoDup reasoning.

**Important design consideration:** The relation must also capture that registers in the TAIL of the list map to values in range `[lo, mid)`. This is needed for `rel_implies_rm_wf` to derive distinctness. Two design choices:

- **Option A (bundled):** Include `Forall (fun r1 => lo <= rm # r1 < mid) regs` in the `rmr_cons` constructor. This makes the inductive heavier but self-contained.
- **Option B (derived):** Keep the inductive minimal (as above) and prove the range property as a separate lemma `replication_map_rel_range`. Then `rel_implies_rm_wf` uses both.

**Recommendation:** Option B (derived). The minimal inductive is easier to prove from `foldM`, and the range lemma is a clean induction on the relation itself. This aligns with the TODO's explicit suggestion of separation.

### Pattern 2: Composition (foldM_satisfies_rel + rel_implies_rm_wf)

**What:** Two lemmas that compose to replace `replication_map_wf_aux`.

```coq
(* Lemma 1: The foldM computation produces a map satisfying the relation *)
Lemma foldM_satisfies_rel regs acc s rm s' pf :
  Forall (fun r => r < s.(st_nextreg)) regs ->
  foldM (...) regs acc s = RTLgen.OK rm s' pf ->
  replication_map_rel regs rm s.(st_nextreg) s'.(st_nextreg).

(* Lemma 2: The relation implies rm_wf *)
Lemma rel_implies_rm_wf regs rm lo hi :
  replication_map_rel regs rm lo hi ->
  Forall (fun r => r < lo) regs ->
  rm_wf rm regs.
```

**Why this works:** `foldM_satisfies_rel` is a clean induction on the `foldM` computation that only needs to track the allocated register identities and range -- no NoDup reasoning at all. `rel_implies_rm_wf` is a pure logical derivation that reasons about NoDup from range non-overlap, without touching the monadic machinery.

**Replacing replication_map_wf_aux:** The old lemma can either be:
1. **Replaced by composition:** Keep the name but prove it as `split; [eapply rel_implies_rm_wf; eapply foldM_satisfies_rel; ... | ...]`
2. **Deleted entirely:** If `replication_map_wf` (the wrapper that calls `replication_map_wf_aux`) can be rewritten to use the new lemmas directly.

**Recommendation:** Option 2 (delete). The `replication_map_wf` lemma (which is the public-facing API used by `transf_function_match_fundef`) should be re-proved directly using `foldM_satisfies_rel` + `rel_implies_rm_wf`. The second conjunct of the old `replication_map_wf_aux` (the `Forall` about ranges) was only used internally to prove `rm_wf`; if the relational spec cleanly captures it, it need not be re-exported.

BUT: The second conjunct is also used by `foldM_rm_inv_list` (for `rm_inv`). Check: does `foldM_rm_inv_list` use the range information from `replication_map_wf_aux`? No -- `foldM_rm_inv_list` is a separate lemma that also does its own induction on `foldM`. It does NOT call `replication_map_wf_aux`. So the second conjunct can safely go.

### Pattern 3: Downstream Interface Stability

**What:** The proof files (`RTLdmrproof.v` and `RTLtmrproof.v`) only reference:
- `rm_wf` (the definition, unchanged)
- `rm_inv` (the definition, unchanged)
- `match_function`, `match_fundef`, `match_code` (unchanged)
- `transf_function_match_fundef` (the theorem, whose proof calls `replication_map_wf`)
- Various `rm_wf_neq_*` lemmas (defined in the proof files, depend only on `rm_wf` definition)

**Critical stability requirement:** As long as `rm_wf`, `rm_inv`, `match_function`, `match_fundef`, `match_code`, and `transf_function_match_fundef` keep their exact same types/signatures, the proof files compile unchanged.

### Anti-Patterns to Avoid

- **Changing `rm_wf` signature:** Do NOT change the type of `rm_wf` in either file. The proof files have hundreds of references to it.
- **Changing `transf_function_match_fundef` type:** This is the main public theorem. Its type must remain identical.
- **Making `replication_map_rel` too specific to DMR or TMR:** The two variants have different arities. Do NOT try to unify them into a single polymorphic relation in `RTLreplicateSpecCommon.v`. The DMR version uses `PMap.t reg` and the TMR version uses `PMap.t (reg * reg)`. These are structurally different enough that sharing would be forced and brittle.
- **Breaking the `foldM` processing order:** `foldM` processes tail-first (recursive call on `xs`, then `f a' x` on the head). Getting this wrong will make the inductive relation impossible to prove from the computation.

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| NoDup distinctness from ranges | Custom case analysis on every pair | Derive from `lo <= x < hi` range separation | Range-based reasoning is strictly simpler: if all values in set A are in `[lo1, hi1)` and all in set B are in `[lo2, hi2)` and ranges don't overlap, elements are distinct |
| Register range tracking | Re-derive `state_incr` facts inline | Let `replication_map_rel` encode ranges directly | The relation IS the range tracker |

**Key insight:** The monolithic proof is hard because it simultaneously reasons about (a) monad state threading, (b) PMap.gss/gso case splits, and (c) NoDup construction. Separating (a)+(b) from (c) is the entire point of this phase.

## Common Pitfalls

### Pitfall 1: foldM evaluation order

**What goes wrong:** The `foldM` in RTLgen processes the list in reverse order: it recurses on the tail first, then applies `f` to the head. This means for list `[a; b; c]`, register `c` is allocated first, then `b`, then `a`.
**Why it happens:** `foldM` is defined as `do a' <- foldM f xs a; f a' x` -- tail-recursive on the rest, then processes the current element.
**How to avoid:** The `replication_map_rel` inductive must reflect this: the tail-relation establishes a range `[lo, mid)`, and the head element's shadows are allocated at `mid` (and `mid+1` for TMR), advancing to `hi`.
**Warning signs:** If the proof of `foldM_satisfies_rel` gets stuck on the inductive step, the constructor order is likely wrong.

### Pitfall 2: PMap.gss/gso reasoning leaking into rel_implies_rm_wf

**What goes wrong:** When proving `rel_implies_rm_wf`, there's a temptation to unfold `rm_wf` and reason about `PMap.gss`/`PMap.gso`. But the relational spec should make this unnecessary.
**Why it happens:** The relation directly states what `rm # r` equals for each `r` in the list. The NoDup proof should only need range arithmetic.
**How to avoid:** Ensure `replication_map_rel` gives sufficient information about what `rm # r` is for ALL registers in the list, not just the head. This is where the derived range lemma matters.
**Warning signs:** If `PMap.gss` appears in `rel_implies_rm_wf`, the abstraction is leaking.

### Pitfall 3: The second conjunct of the old replication_map_wf_aux

**What goes wrong:** Deleting `replication_map_wf_aux` without checking whether its second conjunct (the `Forall` about register ranges) is used elsewhere.
**Why it happens:** Both files also define `foldM_rm_inv_list` which proves `rm_inv_list`. This is a SEPARATE lemma with its own induction -- it does NOT call `replication_map_wf_aux`.
**How to avoid:** Verify that `replication_map_wf_aux` is only called from `replication_map_wf` (which only uses the first conjunct). Grep confirms this: `replication_map_wf` is the only caller.
**Warning signs:** Build failures in `replication_map_rm_inv'` or `foldM_rm_inv_list` would indicate a missed dependency.

### Pitfall 4: foldM NoDup precondition for the register list

**What goes wrong:** The `replication_map_rel` relation implicitly assumes distinct input registers (otherwise two registers could be allocated the same shadow).
**Why it happens:** The input list is `fun_regs_list f = Regset.elements (all_regs params c)`, which IS guaranteed NoDup by `Regset.elements_3w`. But the current `replication_map_wf_aux` doesn't require NoDup on the input because PMap.gss/gso handles it.
**How to avoid:** If the new `rel_implies_rm_wf` needs input NoDup, it must be provided. But actually, the relational spec states `rm # r = value` for each r, which is a FACT about the final map, not about allocation order. Since PMap is a total map with last-write-wins semantics, the relation should capture the FINAL state. This means for duplicate elements, the later write wins. But `Regset.elements` guarantees NoDup, so this is not a real problem in practice. Still, the lemma statements should either assume NoDup or handle duplicates gracefully.

### Pitfall 5: Lemmas moved out of Section VOTE

**What goes wrong:** Per STATE.md: "Lemmas moved out of Section VOTE gain explicit `{VT: vote_type} {vsem: VoteSemantics VT}` parameters -- all call sites must be updated."
**Why it happens:** Both spec files don't actually use Section VOTE. But the spec common file doesn't either. This is a non-issue for this phase since `replication_map_rel`, `foldM_satisfies_rel`, and `rel_implies_rm_wf` are all about register maps, not vote semantics.
**How to avoid:** Keep all new definitions/lemmas at the same scope level as the existing `replication_map_wf_aux`.

## Code Examples

### DMR: replication_map_rel Inductive

```coq
(* Source: New code for RTLdmrspec.v *)
(** Relational specification of the DMR replication map construction.
    [replication_map_rel regs rm lo hi] holds when [rm] maps each
    register in [regs] to a distinct shadow in the range [lo, hi). *)
Inductive replication_map_rel
  : list reg -> PMap.t reg -> positive -> positive -> Prop :=
| rmr_nil :
  forall rm lo,
    replication_map_rel [] rm lo lo
| rmr_cons :
  forall r regs rm lo mid,
    replication_map_rel regs rm lo mid ->
    rm # r = mid ->
    replication_map_rel (r :: regs) rm lo (Pos.succ mid).
```

### DMR: foldM_satisfies_rel

```coq
(* Source: New code for RTLdmrspec.v *)
Lemma foldM_satisfies_rel regs acc s rm s' pf :
  Forall (fun r => r < s.(st_nextreg)) regs ->
  foldM
    (fun rm r1 => do r2 <- new_reg; ret rm # r1 <- r2)
    regs acc s = RTLgen.OK rm s' pf ->
  replication_map_rel regs rm s.(st_nextreg) s'.(st_nextreg).
Proof.
  revert acc s rm s' pf.
  induction regs; simpl; intros acc s rm s' pf Hall Hfold.
  { inv Hfold. constructor. }
  inv Hall.
  unfold RTLgen.bind in Hfold.
  (* foldM recurses on tail first *)
  match goal with
  | [ _: match ?X with | RTLgen.Error _ => _ | RTLgen.OK _ _ _ => _ end = _ |- _ ] =>
      destruct X eqn:HX
  end.
  { inv Hfold. }
  inv Hfold.
  econstructor.
  - eapply IHregs; eauto.
  - rewrite PMap.gss. reflexivity.
Qed.
```

Note: The actual proof may need more care around state threading. The above is a sketch.

### DMR: rel_implies_rm_wf

```coq
(* Source: New code for RTLdmrspec.v -- sketch *)
Lemma replication_map_rel_range regs rm lo hi :
  replication_map_rel regs rm lo hi ->
  Forall (fun r => lo <= rm # r < hi) regs.
Proof.
  induction 1.
  - constructor.
  - constructor.
    + subst. lia.
    + eapply Forall_impl; [| exact IHreplication_map_rel].
      simpl; intros; lia.
Qed.

Lemma rel_implies_rm_wf regs rm lo hi :
  replication_map_rel regs rm lo hi ->
  Forall (fun r => r < lo) regs ->
  rm_wf rm regs.
Proof.
  (* All original registers are < lo.
     All shadow registers are in [lo, hi).
     Therefore originals and shadows are disjoint.
     Different shadows are at different positions (from the relation).
     This gives all the NoDup clauses of rm_wf. *)
  ...
Qed.
```

### TMR: replication_map_rel Inductive

```coq
(* Source: New code for RTLtmrspec.v *)
Inductive replication_map_rel
  : list reg -> PMap.t (reg * reg) -> positive -> positive -> Prop :=
| rmr_nil :
  forall rm lo,
    replication_map_rel [] rm lo lo
| rmr_cons :
  forall r regs rm lo mid r2 r3,
    replication_map_rel regs rm lo mid ->
    rm # r = (r2, r3) ->
    r2 = mid ->
    r3 = Pos.succ mid ->
    replication_map_rel (r :: regs) rm lo (Pos.succ (Pos.succ mid)).
```

### Replacement of replication_map_wf

```coq
(* In both files, replication_map_wf becomes: *)
Lemma replication_map_wf f rm s pf :
  replication_map f (init_state f) = RTLgen.OK rm s pf ->
  rm_wf rm (fun_regs_list f).
Proof.
  intro H.
  eapply rel_implies_rm_wf.
  - eapply foldM_satisfies_rel; eauto.
    apply Forall_forall; intros r Hin.
    apply in_lt_max_reg; auto.
  - apply Forall_forall; intros r Hin.
    apply in_lt_max_reg; auto.
Qed.
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| Monolithic `replication_map_wf_aux` proving rm_wf + ranges in one induction | (This phase) Relational spec separating algorithmic correctness from invariant consequences | Phase 3 | Cleaner proofs, easier maintenance, better separation of concerns |

## Open Questions

1. **Should `replication_map_wf_aux` be kept as a compatibility wrapper or deleted?**
   - What we know: It is only called from `replication_map_wf`. The proof files never reference it directly.
   - What's unclear: Whether keeping it as a thin wrapper is cleaner than rewriting `replication_map_wf` to call the new lemmas directly.
   - Recommendation: Delete `replication_map_wf_aux` entirely and rewrite `replication_map_wf` to use the new decomposition. Cleaner and avoids dead code.

2. **Should `replication_map_rel` encode the concrete shadow register values or just ranges?**
   - What we know: The relation needs `rm # r = value` to connect to the map. For DMR `value` is a single reg, for TMR it's a pair.
   - What's unclear: Whether the constructors should use equality (`rm # r = mid`) or just range bounds (`lo <= rm # r < hi`).
   - Recommendation: Use equality (`rm # r = mid` / `rm # r = (mid, Pos.succ mid)`). This is strictly more informative and makes `rel_implies_rm_wf` trivial to derive because we know exact values.

3. **NoDup on the input register list**
   - What we know: `fun_regs_list f = Regset.elements (all_regs ...)` which is NoDup by `Regset.elements_3w`.
   - What's unclear: Whether `rel_implies_rm_wf` needs NoDup as a precondition.
   - Recommendation: It likely does, because `rm_wf` requires cross-register distinctness (for `r <> r'`, their shadows must be distinct). Without NoDup on the input, two equal registers would have the same shadow, which is fine. But `rm_wf` quantifies over `r <> r'`, so if the list has duplicates, `r` and `r'` could be the same element at different positions. Since `rm_wf` says "for all r in l, for all r' in l, r <> r' implies NoDup [r; shadow(r); r'; shadow(r')]", duplicates in the list are not a problem -- we just need that DISTINCT elements have DISTINCT shadows. The relation with exact equalities gives this: if `rm # r = mid_r` and `rm # r' = mid_r'` with `r <> r'`, then `mid_r <> mid_r'` because later writes in PMap overwrite earlier ones. Actually, with PMap last-write-wins, if `r` appears multiple times, `rm # r` reflects the LAST write. The relation must be carefully designed to match. Since `Regset.elements` is NoDup, adding a NoDup precondition is safe and simplifies the proof.

## Validation Architecture

### Test Framework

| Property | Value |
|----------|-------|
| Framework | Coq (make) |
| Config file | Makefile + _CoqProject |
| Quick run command | `make backend/RTLdmrspec.vo backend/RTLtmrspec.vo -j4` |
| Full suite command | `make backend/RTLdmrspec.vo backend/RTLtmrspec.vo backend/RTLdmrproof.vo backend/RTLtmrproof.vo -j4` |

### Phase Requirements to Test Map

| Req ID | Behavior | Test Type | Automated Command | File Exists? |
|--------|----------|-----------|-------------------|-------------|
| SPEC-01 | `replication_map_rel` defined in RTLdmrspec.v | compilation | `make backend/RTLdmrspec.vo` | N/A (source modification) |
| SPEC-02 | `replication_map_rel` defined in RTLtmrspec.v | compilation | `make backend/RTLtmrspec.vo` | N/A (source modification) |
| SPEC-03 | `replication_map_wf_aux` replaced in RTLdmrspec.v, proof file still compiles | compilation | `make backend/RTLdmrspec.vo backend/RTLdmrproof.vo -j4` | N/A |
| SPEC-04 | `replication_map_wf_aux` replaced in RTLtmrspec.v, proof file still compiles | compilation | `make backend/RTLtmrspec.vo backend/RTLtmrproof.vo -j4` | N/A |

### Sampling Rate

- **Per task commit:** `make backend/RTLdmrspec.vo backend/RTLtmrspec.vo -j4` (spec files compile)
- **Per wave merge:** `make backend/RTLdmrspec.vo backend/RTLtmrspec.vo backend/RTLdmrproof.vo backend/RTLtmrproof.vo -j4` (proof files still type-check)
- **Phase gate:** Full suite green before `/gsd:verify-work`

### Wave 0 Gaps

None -- existing Coq build infrastructure covers all phase requirements. No new test files needed.

## Sources

### Primary (HIGH confidence)

- Direct source code analysis of `backend/RTLdmrspec.v` (lines 808-955) -- DMR monolithic proof
- Direct source code analysis of `backend/RTLtmrspec.v` (lines 925-1097) -- TMR monolithic proof
- Direct source code analysis of `backend/RTLgen.v` (lines 159-165) -- `foldM` definition confirming tail-first evaluation order
- Direct source code analysis of `backend/RTLdmr.v` (line 180) -- DMR `replication_map` definition
- Direct source code analysis of `backend/RTLtmr.v` (line 289) -- TMR `replication_map` definition
- Grep analysis confirming `replication_map_wf_aux` is only called from `replication_map_wf` in both files
- Grep analysis confirming proof files do NOT reference `replication_map_wf_aux`, `foldM_rm_inv_list`, or `rm_inv_list`
- Build verification: all four target .vo files compile on current branch

### Secondary (MEDIUM confidence)

- TODO comments in source code (lines 808-812 of RTLdmrspec.v, lines 925-928 of RTLtmrspec.v) -- author's own refactoring suggestion aligns with our approach

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH - direct code analysis, no external dependencies
- Architecture: HIGH - the refactoring pattern (relational spec + consequence) is a well-known Coq proof engineering technique, and the TODO comments confirm the author intended this exact decomposition
- Pitfalls: HIGH - all identified from direct analysis of the `foldM` definition and its usage patterns

**Research date:** 2026-03-03
**Valid until:** No expiration (internal codebase refactoring, no external dependency drift)
