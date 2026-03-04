# Phase 4: Proof De-duplication - Research

**Researched:** 2026-03-03
**Domain:** Coq proof refactoring -- collapsing repeated proof patterns within single files
**Confidence:** HIGH

## Summary

Phase 4 addresses five concrete de-duplication targets across four Coq proof files. Each target is a within-file refactoring that replaces repeated proof scripts with parametric helpers or per-case lemma decompositions, without changing any externally visible theorem signatures. The work is strictly build-gated: each file must independently compile after its changes (`make backend/<file>.vo`), and the full proof suite must pass at phase end.

The five targets decompose into four independent file-scoped refactoring tasks plus one migration task (removing the deprecated `external_call_Three_Two` after migrating its 3 call sites to `external_call_Three_Two'`). None of the five DEDUP requirements modify theorem signatures visible outside their containing file, and none require the `no_votes` policy decision (XPASS-01/XPASS-02, deferred to v2). The STATE.md blocker about `no_votes` Option A/B is stale -- it was written when Phase 4 included `no_votes` policy alignment, which has since been scoped out.

**Primary recommendation:** Execute each file's de-duplication independently, verifying with `make backend/<file>.vo` after each change. The four files have no cross-dependencies for these changes, so task ordering is flexible. The `external_call_Three_Two` removal (DEDUP-04) and `external_call_vote_lessdef` collapse (DEDUP-03) both touch RTLtolerant.v, so they should be done sequentially within that file.

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|-----------------|
| DEDUP-01 | `no_votes_external_call` in Novotesproof.v refactored from 8 repeats to helper lemma + driver | Extract `lookup_builtin_not_vote` helper; the 8 repeated blocks differ only in which `do N` count and which hypothesis (`Hef` vs `Hef'`) produces the contradiction |
| DEDUP-02 | `maj_voteR_step` in RTLtmrproof.v refactored from four-case duplication to parametric lemma | Extract `maj_voteR_step_of_type` parametric over `ty`; needs a vote-sem selector function mapping `typ` to the correct `vote_sem_*_ok` lemma |
| DEDUP-03 | `external_call_vote_lessdef` in RTLtolerant.v refactored from four identical cases to type-parametric lemma | Extract `vote_lessdef_of_type` parametric over `ty`; all four cases are structurally identical modulo the type constructor (`Tint`/`Tlong`/`Tsingle`/`Tfloat`) |
| DEDUP-04 | Deprecated `external_call_Three_Two` removed from RTLtolerant.v after migrating all 3 call sites to `external_call_Three_Two'` | Three call sites at lines ~1704, ~1764, ~1854; migration requires adding `Val.lessdef` handling at each site since `external_call_Three_Two'` provides `Val.lessdef v v'` while the deprecated version only provides existence |
| DEDUP-05 | `check_col_instr_sound` in RTLcolorcheck.v split into per-instruction lemmas | The proof currently has 11 instruction cases (Inop, Iop safe, Iop protected, Iload, Istore, Icall, Itailcall, Ibuiltin green smove, Ibuiltin blue smove, Ibuiltin vote, Ibuiltin other, Icond, Ijumptable, Ireturn) in one ~200-line block |
</phase_requirements>

## Standard Stack

### Core
| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| Coq/Rocq | 8.20.0 | Proof assistant | Already in use, unchanged |
| OCaml | 4.14.2 | Extraction target | Already in use, unchanged |
| make | GNU Make | Build system | Standard CompCert build |

### Supporting
No additional libraries needed. All changes are within-file Coq proof refactoring using existing tactics and definitions.

## Architecture Patterns

### Pattern 1: Type-Parametric Vote Semantics Helper

**What:** Extract a helper that maps `typ -> vote_sem_ok` proof, eliminating the four-case `destruct ty` pattern.

**When to use:** When a proof destructs on `ty : typ` (filtering out `Tany32`/`Tany64`) and applies one of `vote_sem_int_ok`, `vote_sem_float_ok`, `vote_sem_long_ok`, `vote_sem_single_ok` in each branch with otherwise identical proof scripts.

**Strategy for DEDUP-02 (maj_voteR_step):**

The current proof destructs `ty`, then in each branch:
1. Inverts `H0` (the `maj_voteR` hypothesis)
2. Constructs the step using `exec_Ibuiltin` with `vote_sem_*_ok`
3. Proves register preservation via `PMap.gss`/`PMap.gso`

The key difficulty: the register-value case analysis differs per type because each value constructor has a different equality decider (`Int.eq_dec`, `Float.eq_dec`, `Int64.eq_dec`, `Float32.eq_dec`), and `Tint`/`Tlong` additionally need `Archi.ptr64` handling for pointer values.

**Recommended approach:** Instead of a fully parametric lemma that abstracts over the equality decider, use a single Ltac tactic or a lemma that takes the `vote_sem_ok` proof as an argument. The vote semantics step construction is identical; only the "result equals input" proof at the end differs. A parametric helper can handle steps 1-2 and leave the register equality as a side goal, or use `destruct (rs # r1)` uniformly with `try solve` chains.

```coq
(* Sketch: parametric helper approach *)
Lemma maj_voteR_step_of_type
  ty r1 r2 r3 pc succ tstk sig params stacksize c entrypoint sp rs m :
  is_actual_type ty ->
  (vote_sem_ok (match ty with
    | Tint => (vote_type_sem VT).(vote_sem_int)
    | Tlong => (vote_type_sem VT).(vote_sem_long)
    | Tsingle => (vote_type_sem VT).(vote_sem_single)
    | Tfloat => (vote_type_sem VT).(vote_sem_float)
    | _ => (* unreachable *) (vote_type_sem VT).(vote_sem_int)
    end)) ->
  Val.has_type (rs # r1) ty ->
  rs # r1 = rs # r2 ->
  rs # r2 = rs # r3 ->
  maj_voteR c ty r1 r2 r3 pc succ ->
  exists rs', plus step tge (...) [] (...) /\ (forall r, rs # r = rs' # r).
```

Then `maj_voteR_step` becomes:
```coq
destruct ty; simpl in *; try contradiction; clear H;
  eapply maj_voteR_step_of_type; eauto.
```

**Confidence:** HIGH -- the four branches share identical step construction; only the PMap equality tail differs.

### Pattern 2: Vote Lessdef Type Parametrization

**What:** Extract a helper for `external_call_vote_lessdef` that handles one `is_vote_builtin` case.

**When to use:** When four cases of `inv Hbuiltin` produce identical proof scripts modulo the type (`Tint`/`Tlong`/`Tsingle`/`Tfloat`) and the `lessdef_vote3_vote*` lemma application pattern.

**Strategy for DEDUP-03:**

Each of the four cases in `external_call_vote_lessdef` follows this structure:
1. Unfold `builtin_or_external_sem`, `Builtins.lookup_builtin_function`
2. `destruct (signature_eq _ _)`
3. `inv Hext; simpl in *`
4. Case-split on `list_lessdef_mod_1` (`Heq`) -- 3 sub-cases
5. Each sub-case applies `lessdef_vote3_vote`, `lessdef_vote3_vote'`, or `lessdef_vote3_vote''` with the appropriate type constructor

The lemmas `lessdef_vote3_vote`, `lessdef_vote3_vote'`, `lessdef_vote3_vote''` are already parametric over `ty` -- they take `ty` as an argument. The only per-case difference is the type constructor used for `vote ty y y0 y1`.

**Recommended approach:** Extract a helper `vote_lessdef_of_type` that takes `ty` as a parameter, the `vote_sem_ok` proof for that type, and shows the result. The `list_lessdef_mod_1` case analysis is type-independent.

```coq
Lemma vote_lessdef_of_type ty vs1 vs2 m1 m2 t v m' :
  @builtin_or_external_sem Three VoteSemantics_Three
    ("__builtin_vote_" ++ type_name ty)
    (replicate_builtin_sig (vote_builtin_of_type ty))
    (Genv.globalenv prog) vs1 m1 t v m' ->
  list_lessdef_mod_1 vs1 vs2 ->
  Memory.Mem.extends m1 m2 ->
  exists v', @builtin_or_external_sem Two VoteSemantics_Two ... /\ Val.lessdef v v'.
```

**Alternative simpler approach:** Use Ltac to factor the repeated tactic script into a single tactic `solve_vote_lessdef_case ty`, then apply it in each `inv Hbuiltin` branch. This is less clean but mechanically simpler and avoids needing to construct a type-level mapping function.

**Confidence:** HIGH -- all four cases are literally identical modulo the type.

### Pattern 3: Builtin Lookup Helper for Novotesproof

**What:** Extract a `lookup_builtin_not_vote` helper that handles the repeated `Builtins.lookup_builtin_function` unfolding in `no_votes_external_call`.

**When to use:** The 8 repeated blocks in `no_votes_external_call` handle two `external_function` constructors (`EF_builtin` and `EF_runtime`, lines 64-107 and 143-221) and within each, 4 sub-cases for the 4 vote types.

**Strategy for DEDUP-01:**

The proof structure is:
1. `destruct ef; simpl; auto` -- generates 2 non-trivial cases (`EF_builtin`, `EF_runtime`)
2. Each case: unfold `builtin_or_external_sem`, `destruct (Builtins.lookup_builtin_function ...)`
3. When `Some b`: `inv Hsem; constructor; destruct b; auto`
4. Then `destruct b; simpl in *; repeat (destruct vargs; try congruence)`
5. Each `b` branch (4 vote types): unfold `Builtins.lookup_builtin_function` and do N `destruct (string_dec ...)` steps, then find the matching vote builtin and derive contradiction from `Hef` or `Hef'`

The key observation: the 8 blocks (4 per EF case) differ ONLY in:
- The `do N` count (8, 9, 10, or 11 string_dec destructs before hitting the vote builtin)
- Which hypothesis produces the contradiction (`Hef` for votes, `Hef'` for runtimes)

**Recommended approach:** The `do N` variation is the hardest part. A helper lemma could abstract over the builtin lookup result:

```coq
Lemma lookup_builtin_not_vote name sg :
  ~ is_vote_builtin (EF_builtin name sg) ->
  ~ is_vote_runtime (EF_builtin name sg) ->
  forall b, Builtins.lookup_builtin_function name sg = Some b ->
  (* The builtin semantics for Three and Two agree *)
  forall vargs m t v m',
    bs_sem _ b vargs = Some v ->
    exists b', Builtins.lookup_builtin_function name sg = Some b' /\
      bs_sem _ b' vargs = Some v.
```

**Alternative (simpler, likely more practical):** Since the `do N` pattern comes from the position of vote builtins in the `replicate_builtin_table`, a tactic-based approach may be more robust:

```coq
Ltac solve_not_vote_case Hef :=
  unfold Builtins.lookup_builtin_function in *;
  destruct (Builtins0.lookup_builtin _ _ _ _); [inv Hlookup|];
  destruct (Builtins0.lookup_builtin _ _ _ _); [inv Hlookup|];
  simpl in *;
  repeat (destruct (string_dec _ _ && signature_eq _ _);
          simpl in *; try solve [inv Hlookup]);
  (* Handle the vote builtin match *)
  match goal with
  | [H: (_ && _)%bool = true |- _] =>
    apply andb_prop in H; destruct H;
    exfalso; apply Hef;
    repeat match goal with
    | [H: (if ?x then _ else _) = true |- _] => destruct x
    end; try discriminate; constructor
  end.
```

However, the cleanest approach might be to prove a single abstract lemma that the Three-semantics builtin lookup for any non-vote, non-runtime builtin produces the same result as the Two-semantics lookup. This would require understanding the `Builtins.lookup_builtin_function` structure more deeply.

**Most practical approach:** Use `repeat` and `try solve` more aggressively to collapse the `do N` variation. The existing proof already uses `repeat` in some places. A single tactic block can handle all 8 cases:

```coq
Lemma no_votes_external_call ... :
  ...
Proof.
  intros Hef Hef'.
  destruct ef; simpl; auto.
  - (* EF_builtin *)
    unfold builtin_or_external_sem; intro Hsem.
    destruct (Builtins.lookup_builtin_function name sg) eqn:Hlookup; auto.
    inv Hsem. constructor. destruct b; auto.
    destruct b; simpl in *;
      repeat (destruct vargs; try congruence);
      solve_builtin_case Hef Hef' Hlookup.
  - (* EF_runtime -- same structure *)
    ...
Qed.
```

**Confidence:** MEDIUM -- the exact tactic automation depends on how `repeat` interacts with the `do N` pattern; may need experimentation.

### Pattern 4: Per-Instruction Lemma Decomposition

**What:** Split `check_col_instr_sound` into separate lemmas, one per instruction type.

**When to use:** A proof that destructs on an ADT with many constructors, where each branch is self-contained and can be proved independently.

**Strategy for DEDUP-05:**

The `check_col_instr_sound` proof handles 11 instruction types in one monolithic block. Each case is already self-contained -- it only depends on `check_col_instr pc instr = true` specialized to the particular instruction constructor.

The recommended decomposition creates one lemma per case:
```coq
Lemma check_col_instr_sound_Inop pc succ :
  check_col_instr pc (Inop succ) = true ->
  wc_instruction (fun n r => (col n) ! r) pc (Inop succ).

Lemma check_col_instr_sound_Iop_safe pc op args res succ :
  ~ is_protected op ->
  check_col_instr pc (Iop op args res succ) = true ->
  wc_instruction (fun n r => (col n) ! r) pc (Iop op args res succ).

Lemma check_col_instr_sound_Iop_protected pc op args res succ :
  is_protected op ->
  check_col_instr pc (Iop op args res succ) = true ->
  wc_instruction (fun n r => (col n) ! r) pc (Iop op args res succ).

(* etc. for Iload, Istore, Icall, Itailcall,
   Ibuiltin_smove_green, Ibuiltin_smove_blue, Ibuiltin_vote, Ibuiltin_other,
   Icond, Ijumptable, Ireturn *)
```

Then the main lemma becomes:
```coq
Lemma check_col_instr_sound pc instr :
  check_col_instr pc instr = true ->
  wc_instruction (fun n r => (col n) ! r) pc instr.
Proof.
  destruct instr; simpl; intro Hcheck; try congruence.
  - apply check_col_instr_sound_Inop; auto.
  - destruct (is_protectedb_spec o).
    + apply check_col_instr_sound_Iop_protected; auto.
    + apply check_col_instr_sound_Iop_safe; auto.
  (* etc. *)
Qed.
```

The instruction types in `check_col_instr` to decompose:
1. `Inop` (lines 271-275)
2. `Iop` safe (lines 291-304)
3. `Iop` protected (lines 276-290)
4. `Iload` (lines 305-318)
5. `Istore` (lines 319-334)
6. `Icall` (lines 335-354)
7. `Itailcall` (lines 355-361)
8. `Ibuiltin` green smove (lines 362-378)
9. `Ibuiltin` blue smove (lines 379-395)
10. `Ibuiltin` vote (lines 396-411)
11. `Ibuiltin` other (lines 412-439)
12. `Icond` (lines 440-450)
13. `Ijumptable` (lines 451-459)
14. `Ireturn` (lines 460-462)

Note: The `Iop` case splits into safe vs. protected inside the proof. The `Ibuiltin` case splits into four sub-cases (green smove, blue smove, vote, other).

**Confidence:** HIGH -- each case is self-contained; this is mechanical extraction.

### Pattern 5: Deprecated Lemma Removal via Call-Site Migration

**What:** Remove `external_call_Three_Two` after migrating its 3 call sites to `external_call_Three_Two'`.

**Strategy for DEDUP-04:**

The deprecated lemma:
```coq
Lemma external_call_Three_Two ef vargs m t v m' :
  @external_call Three VoteSemantics_Three ef ... ->
  exists v', @external_call Two VoteSemantics_Two ef ... .
```

The replacement:
```coq
Lemma external_call_Three_Two' ef vargs m t v m' :
  @external_call Three VoteSemantics_Three ef ... ->
  exists v', @external_call Two VoteSemantics_Two ef ... /\ Val.lessdef v v'.
```

The difference: `external_call_Three_Two'` additionally provides `Val.lessdef v v'`.

**Call site analysis:**

1. **Line ~1704** (vote builtin, non-faulty case): Uses `external_call_Three_Two` to get `v'` for constructing a 2-voting step. Does NOT use `Val.lessdef`. Migration: replace `apply external_call_Three_Two in Hext` with `apply external_call_Three_Two' in Hext`, then `destruct Hext as [v' [Hext _]]` (discard the lessdef).

2. **Line ~1764** (other builtin, non-faulty case): Same pattern -- gets `v'` for step construction, does not use lessdef. Migration: same as site 1.

3. **Line ~1854** (custom `external_call_mem_extends` lemma): Uses `external_call_Three_Two` to convert a Three-call to a Two-call, then uses `Events.external_call_mem_extends` to get memory extension. Migration: replace with `external_call_Three_Two'`, destruct, use the Two-call result. The `Val.lessdef` is again discarded.

All three sites only use the existence of `v'` and the Two-voting external call. The additional `Val.lessdef` from `external_call_Three_Two'` is simply discarded at each site. This makes the migration mechanical.

**Confidence:** HIGH -- all 3 call sites inspected; migration is destructing an extra conjunction.

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Type-to-vote-sem mapping | Manual 4-way destruct in every proof | Define `vote_sem_of_type : typ -> builtin_sem` helper in Builtins2.v or locally | Eliminates repeated `destruct ty` dispatch |
| Builtin lookup contradiction | Manual `do N (destruct ...)` counting | `repeat` + `try solve` tactic chains | The exact `do N` count depends on table position and is fragile |
| Per-instruction proof cases | One giant proof block | Per-instruction lemma extraction | Each case is independently verifiable |

**Key insight:** These are all within-file refactorings. No new shared modules are needed. The existing `RTLreplicateSpecCommon.v` and `RTLreplicateProofCommon.v` from Phase 2 are not affected.

## Common Pitfalls

### Pitfall 1: Breaking the Section Context
**What goes wrong:** Extracting a helper lemma from inside `Section PRESERVATION` or `Section match_states` without properly handling section variables.
**Why it happens:** The helper references `prog`, `tprog`, `ge`, `tge`, `TRANSF` as section variables. If moved outside the section, these become explicit arguments.
**How to avoid:** Keep all extracted helpers inside the same section as the original proof. For DEDUP-02/03/04, the helpers stay inside `Section PRESERVATION`.
**Warning signs:** "Unbound variable" errors after extraction.

### Pitfall 2: Vote Semantics Typeclass Dispatch
**What goes wrong:** The parametric helper for `maj_voteR_step_of_type` must correctly dispatch the `VoteSemantics` typeclass. If the helper is stated with a `match ty` that returns a `vote_sem_ok` proof, Coq's dependent pattern matching may not reduce correctly.
**Why it happens:** `vote_sem_int_ok` etc. are typeclass projections, not match arms. The `VoteSemantics` record fields are `vote_sem_int_ok`, `vote_sem_long_ok`, etc., and they are accessed via the `vsem` instance, not via a `match ty` expression.
**How to avoid:** Either (a) define a dispatch function `vote_sem_ok_of_type (ty : typ) : vote_sem_ok (vote_type_sem_of_type ty)` that uses `match ty`, or (b) keep the `destruct ty` in the main lemma and have the helper handle the post-dispatch case, or (c) use an Ltac tactic to automate the dispatch without a lemma-level abstraction.
**Warning signs:** "Cannot unify" errors when `simpl` does not reduce the match.

### Pitfall 3: Ibuiltin Case Decomposition Boundary
**What goes wrong:** The `Ibuiltin` case in `check_col_instr_sound` has a 4-way nested if-then-else (green smove / blue smove / vote / other). Extracting per-instruction lemmas requires deciding where the split happens: one lemma for all of `Ibuiltin`, or four separate lemmas.
**Why it happens:** The outer match is on `instr`, but the inner match is on `ef` (the external function). The four sub-cases are actually different `wc_instruction` constructors.
**How to avoid:** Extract four separate lemmas: `check_col_Ibuiltin_smove_green_sound`, `check_col_Ibuiltin_smove_blue_sound`, `check_col_Ibuiltin_vote_sound`, `check_col_Ibuiltin_other_sound`. Each takes the appropriate `is_*_spec` hypothesis.
**Warning signs:** Overly complex helper lemma that still has internal case splits.

### Pitfall 4: external_call_Three_Two Migration Incompleteness
**What goes wrong:** Removing `external_call_Three_Two` while one call site still references it.
**Why it happens:** The custom `external_call_mem_extends` lemma at line ~1845 also uses it, which is easy to miss since it's a different lemma from `Events.external_call_mem_extends`.
**How to avoid:** Run `rg 'external_call_Three_Two[^'\'']' backend/RTLtolerant.v` before deletion to find ALL references. There are exactly 3: lines ~1704, ~1764, ~1854. Migrate all three in the same commit as the deletion.
**Warning signs:** Build failure mentioning "The reference external_call_Three_Two was not found".

### Pitfall 5: Stale STATE.md Blocker
**What goes wrong:** The `no_votes` policy blocker in STATE.md causes unnecessary delay. It was written when Phase 4 included `no_votes` policy alignment (XPASS-01/XPASS-02), which has since been scoped to v2.
**Why it happens:** The original research/roadmap described Phase 4 as including `no_votes` alignment. The current REQUIREMENTS.md and ROADMAP.md correctly scope Phase 4 to DEDUP-01 through DEDUP-05 only.
**How to avoid:** Dismiss the blocker explicitly in the plan. None of the five DEDUP requirements modify any theorem signature or touch `no_votes` policy. The `Novotesproof.v` changes (DEDUP-01) are purely structural -- same lemma statement, shorter proof script.

## Code Examples

### Example 1: external_call_Three_Two Migration Pattern

At each of the 3 call sites, the current pattern is:
```coq
apply external_call_Three_Two in Hext.
destruct Hext as [v' Hext].
```

The migrated pattern is:
```coq
apply external_call_Three_Two' in Hext.
destruct Hext as [v' [Hext _]].
```

The `_` discards the `Val.lessdef v v'` since it is not needed at any of the three sites.

### Example 2: Per-Instruction Lemma Extraction

Before (monolithic, lines 266-463):
```coq
Lemma check_col_instr_sound (pc : node) (instr : instruction) :
  check_col_instr pc instr = true ->
  wc_instruction (fun n r => (col n) ! r) pc instr.
Proof.
  destruct instr; simpl; intro Hcheck; try congruence.
  - (* Inop: 5 lines *)
  - (* Iop: 35 lines *)
  - (* Iload: 14 lines *)
  (* ... 200 total lines ... *)
Qed.
```

After (decomposed):
```coq
Lemma check_col_Inop_sound pc succ :
  check_col_instr pc (Inop succ) = true ->
  wc_instruction (fun n r => (col n) ! r) pc (Inop succ).
Proof. (* 5 lines *) Qed.

(* ... one lemma per instruction type ... *)

Lemma check_col_instr_sound (pc : node) (instr : instruction) :
  check_col_instr pc instr = true ->
  wc_instruction (fun n r => (col n) ! r) pc instr.
Proof.
  destruct instr; simpl; intro Hcheck; try congruence.
  - apply check_col_Inop_sound; auto.
  - destruct (is_protectedb_spec o);
    [apply check_col_Iop_protected_sound | apply check_col_Iop_safe_sound]; auto.
  (* ... dispatch to per-instruction lemma ... *)
Qed.
```

### Example 3: vote_lessdef_of_type Sketch

```coq
(* Helper: given a type, prove vote lessdef for that type's builtin *)
Lemma vote_lessdef_of_type ty vs1 vs2 m1 m2 t v m' :
  is_vote_builtin (EF_builtin (vote_builtin_name ty) (vote_builtin_sig ty)) ->
  @builtin_or_external_sem Three VoteSemantics_Three
    (vote_builtin_name ty) (vote_builtin_sig ty)
    (Genv.globalenv prog) vs1 m1 t v m' ->
  list_lessdef_mod_1 vs1 vs2 ->
  Memory.Mem.extends m1 m2 ->
  exists v', @builtin_or_external_sem Two VoteSemantics_Two
    (vote_builtin_name ty) (vote_builtin_sig ty)
    (Genv.globalenv prog) vs2 m2 t v' m2 /\
    Val.lessdef v v'.
```

Alternatively, since `is_vote_builtin` already has exactly 4 constructors, the Ltac approach is simpler:

```coq
Ltac solve_vote_lessdef_case :=
  unfold builtin_or_external_sem in *;
  unfold Builtins.lookup_builtin_function in *; simpl in *;
  destruct (signature_eq _ _); simpl in *; try congruence;
  clear e; inv Hext; simpl in *;
  inv Heq; try congruence;
  repeat match goal with
  | [H: list_lessdef_mod_1 (_ :: _) (_ :: _) |- _] => inv H; try congruence
  | [H: Forall2 _ (_ :: _) (_ :: _) |- _] => inv H; try congruence
  | [H: (bs_sem _ _ _) = Some _ |- _] => inv H
  end;
  eexists; split; [constructor; auto | ];
  first [apply lessdef_vote3_vote | apply lessdef_vote3_vote' | apply lessdef_vote3_vote'']; auto.
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| `external_call_Three_Two` (no lessdef) | `external_call_Three_Two'` (with lessdef) | Already exists in codebase | Stronger result; enables removal of deprecated version |
| Monolithic instr soundness proof | Per-instruction lemma decomposition | Standard Coq proof engineering pattern | Each case independently verifiable |
| Manual 4-way type destruct | Parametric type helper | This phase | Eliminates copy-paste proof scripts |

## Open Questions

1. **Ltac vs. Lemma for DEDUP-01 (Novotesproof)**
   - What we know: The 8 repeated blocks differ in `do N` count and contradiction hypothesis
   - What's unclear: Whether a lemma-level abstraction or a tactic-level abstraction is cleaner
   - Recommendation: Try tactic approach first (`repeat` + `try solve`); fall back to lemma if the tactic doesn't cleanly handle the `do N` variation. Budget extra time for experimentation.

2. **Scope of vote_sem dispatch helper for DEDUP-02**
   - What we know: The dispatch from `ty` to `vote_sem_*_ok` is the core parametric step
   - What's unclear: Whether to define a `vote_sem_ok_of_type` function in `Builtins2.v` (permanent utility) or locally in `RTLtmrproof.v` (scoped to this use)
   - Recommendation: Define locally in `RTLtmrproof.v` inside the same section. If it proves useful elsewhere, it can be promoted later.

3. **Granularity of check_col_instr_sound decomposition**
   - What we know: 14 instruction cases can each be a separate lemma
   - What's unclear: Whether the `Ibuiltin` sub-cases (green smove, blue smove, vote, other) should be 4 lemmas or 1 lemma with internal case split
   - Recommendation: 4 separate lemmas for the `Ibuiltin` sub-cases, since they correspond to different `wc_instruction` constructors and have meaningfully different proof structures.

## Validation Architecture

### Test Framework
| Property | Value |
|----------|-------|
| Framework | Coq 8.20.0 proof checker (`coqc`) |
| Config file | `_CoqProject` (auto-generated by Makefile) |
| Quick run command | `make backend/<file>.vo` |
| Full suite command | `make proof -j$(nproc) && make check-admitted` |

### Phase Requirements -> Test Map
| Req ID | Behavior | Test Type | Automated Command | File Exists? |
|--------|----------|-----------|-------------------|-------------|
| DEDUP-01 | Novotesproof.v compiles with de-duplicated `no_votes_external_call` | proof compilation | `make backend/Novotesproof.vo` | N/A (Coq proof check) |
| DEDUP-02 | RTLtmrproof.v compiles with parametric `maj_voteR_step` | proof compilation | `make backend/RTLtmrproof.vo` | N/A |
| DEDUP-03 | RTLtolerant.v compiles with collapsed `external_call_vote_lessdef` | proof compilation | `make backend/RTLtolerant.vo` | N/A |
| DEDUP-04 | RTLtolerant.v compiles without `external_call_Three_Two` | proof compilation | `make backend/RTLtolerant.vo` | N/A |
| DEDUP-05 | RTLcolorcheck.v compiles with per-instruction lemmas | proof compilation | `make backend/RTLcolorcheck.vo` | N/A |
| ALL | Full proof suite passes | full build | `make proof -j$(nproc) && make check-admitted` | N/A |

### Sampling Rate
- **Per task commit:** `make backend/<file>.vo` (seconds)
- **Per wave merge:** Not applicable (single-wave phase)
- **Phase gate:** `make proof -j$(nproc) && make check-admitted` before verification

### Wave 0 Gaps
None -- existing Coq build infrastructure covers all phase requirements. No new test files or framework configuration needed.

## Sources

### Primary (HIGH confidence)
- Direct inspection of `/home/alex/source/compcert/backend/Novotesproof.v` (379 lines) -- all 8 repeated blocks analyzed
- Direct inspection of `/home/alex/source/compcert/backend/RTLtmrproof.v` (lines 727-832) -- four-case `maj_voteR_step` analyzed
- Direct inspection of `/home/alex/source/compcert/backend/RTLtolerant.v` (lines 1163-1509) -- `external_call_Three_Two`, `external_call_Three_Two'`, `external_call_vote_lessdef` analyzed; all 3 deprecated call sites identified
- Direct inspection of `/home/alex/source/compcert/backend/RTLcolorcheck.v` (lines 120-463) -- `check_col_instr` and `check_col_instr_sound` structure analyzed
- Direct inspection of `/home/alex/source/compcert/backend/Builtins2.v` -- `vote_type`, `VoteSemantics`, `vote_sem_ok`, `vote`/`vote3` definitions
- Direct inspection of `/home/alex/source/compcert/backend/RTLtmrspec.v` (lines 46-53) -- `maj_voteR` inductive
- Direct inspection of `/home/alex/source/compcert/backend/RTL.v` (lines 1199-1265) -- `is_vote_builtin` inductive and boolean reflection
- `/home/alex/source/compcert/.planning/REQUIREMENTS.md` -- DEDUP-01 through DEDUP-05 definitions
- `/home/alex/source/compcert/.planning/STATE.md` -- blockers and decisions
- `/home/alex/source/compcert/.planning/ROADMAP.md` -- phase dependencies and success criteria
- `/home/alex/source/compcert/.planning/research/ARCHITECTURE.md` -- module dependency graph
- `/home/alex/source/compcert/.planning/research/SUMMARY.md` -- prior research findings

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH -- no new tools or libraries needed
- Architecture (per-requirement patterns): HIGH -- all code directly inspected, patterns identified from actual proof scripts
- Pitfalls: HIGH -- all grounded in actual source inspection with specific line numbers
- Vote-sem dispatch approach: MEDIUM -- the exact Coq tactic for type-parametric dispatch needs experimentation during implementation

**Research date:** 2026-03-03
**Valid until:** indefinite (stable codebase, all findings based on direct source inspection)

**Note on stale blocker:** The STATE.md records "The `no_votes` Option A vs. Option B policy decision must be made before Phase 4 implementation begins." This blocker is stale. The current Phase 4 scope (DEDUP-01 through DEDUP-05) does not include `no_votes` policy alignment, which was moved to v2 (XPASS-01, XPASS-02). The planner should dismiss this blocker and note it in the plan.
