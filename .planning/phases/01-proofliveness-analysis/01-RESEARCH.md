# Phase 1: ProofLiveness Analysis - Research

**Researched:** 2026-03-04
**Domain:** Coq backward dataflow analysis (Kildall framework), FSetAVL membership proofs
**Confidence:** HIGH

## Summary

This phase creates a new standalone file `backend/ProofLiveness.v` that is a conservative variant of the existing `backend/Liveness.v`. The key difference: the standard `Liveness.transfer` omits `Iop`/`Iload` argument registers from the live set when the destination register is dead (an optimization for dead code elimination). `ProofLiveness.transfer` must **always** include these argument registers, because the faulty backward simulation proof in `RTLtolerant.v` needs to discharge `Val.lessdef` obligations on argument registers even when the result is not live.

The file is structurally almost identical to `Liveness.v` -- same imports, same Kildall solver instantiation, same `analyze_solution` proof strategy. The differences are confined to exactly two `match` arms in the `transfer` function (removing the `Regset.mem` guard on `Iop` and `Iload`), plus an additional membership lemma `reg_list_live_in` that does not exist in `Liveness.v`.

**Primary recommendation:** Clone `Liveness.v`, remove the `Regset.mem` conditional guards in the `Iop` and `Iload` cases of `transfer`, drop the `last_uses` definitions (unused), add a `reg_list_live_in` induction lemma, register the file in `Makefile` BACKEND list, and verify with `make backend/ProofLiveness.vo`.

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|-----------------|
| PLIV-01 | ProofLiveness.v defines conservative transfer function that always includes Iop/Iload args regardless of result liveness | Transfer function modification: remove `if Regset.mem res after` guard in Iop case and `if Regset.mem dst after` guard in Iload case |
| PLIV-02 | ProofLiveness.v instantiates Kildall backward solver and exposes `analyze : function -> option (PMap.t Regset.t)` | Identical instantiation to Liveness.v: `Module RegsetLat := LFSet(Regset). Module DS := Backward_Dataflow_Solver(RegsetLat)(NodeSetBackward).` |
| PLIV-03 | ProofLiveness.v proves `analyze_solution` theorem (fixpoint property at every CFG edge) | Same proof strategy as Liveness.v: apply `DS.fixpoint_solution`, discharge side condition `transf n bot = bot` when `code!n = None` |
| PLIV-04 | ProofLiveness.v provides `reg_list_live_in` membership lemma | New inductive lemma on `reg_list_live` using `Regset.add_1` and `Regset.add_2` |
| PLIV-05 | ProofLiveness.v builds standalone (`make backend/ProofLiveness.vo`) | Add `ProofLiveness.v` to BACKEND list in Makefile, run `make depend` then `make backend/ProofLiveness.vo` |
</phase_requirements>

## Standard Stack

### Core
| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| Coq | 8.20.0 | Proof assistant | Project version (from `coqtop` output) |
| CompCert Kildall.v | N/A (in-tree) | Backward dataflow solver framework | Standard CompCert infrastructure for all dataflow analyses |
| CompCert Lattice.v | N/A (in-tree) | `LFSet` functor: lifts `FSetAVL` to `SEMILATTICE` | Standard lattice for register sets |
| FSetAVL | Coq stdlib | Finite set implementation providing `Regset` | `Module Regset := FSetAVL.Make(OrderedPositive)` in `Registers.v` |

### Supporting
| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| Registers.v | N/A (in-tree) | Defines `Regset`, `reg`, `Regmap` | All register set operations |
| RTL.v | N/A (in-tree) | RTL language definition, `instruction`, `successors_instr` | Transfer function pattern matching |
| Coqlib.v | N/A (in-tree) | Standard CompCert utility lemmas | `In` list membership |
| Maps.v | N/A (in-tree) | `PMap`, `PTree` | Accessing `fn_code`, dataflow result maps |
| Op.v | N/A (in-tree) | Operation definitions | Required by RTL.v |
| AST.v | N/A (in-tree) | AST types (`ident`, `signature`, etc.) | Required by RTL.v |

### Alternatives Considered
| Instead of | Could Use | Tradeoff |
|------------|-----------|----------|
| Creating ProofLiveness.v | Modifying Liveness.v | Cannot modify Liveness.v -- it is used by dead code elimination (`Deadcode.v`) and register allocation (`Allocation.v`); changing its transfer function would break those passes |
| `DS.fixpoint` | `DS.fixpoint_allnodes` | `fixpoint_allnodes` requires no side condition on transfer at unreachable nodes, but is less efficient; standard `fixpoint` works fine here since the side condition is trivially discharged |

## Architecture Patterns

### Recommended File Structure
```
backend/
  ProofLiveness.v    # NEW: conservative liveness analysis
  Liveness.v         # EXISTING: standard liveness (unchanged)
  Kildall.v          # EXISTING: solver framework (unchanged)
```

### Pattern 1: Backward Dataflow Analysis Instantiation
**What:** Instantiate CompCert's generic backward dataflow solver for register set liveness
**When to use:** Creating any backward dataflow analysis over register sets
**Example:**
```coq
(* Source: backend/Liveness.v lines 110-114 *)
Module RegsetLat := LFSet(Regset).
Module DS := Backward_Dataflow_Solver(RegsetLat)(NodeSetBackward).

Definition analyze (f: function): option (PMap.t Regset.t) :=
  DS.fixpoint f.(fn_code) successors_instr (transfer f).
```

### Pattern 2: analyze_solution Proof Strategy
**What:** Prove the fixpoint property of the backward solver
**When to use:** After defining `analyze` using `DS.fixpoint`
**Example:**
```coq
(* Source: backend/Liveness.v lines 118-127 *)
Lemma analyze_solution:
  forall f live n i s,
  analyze f = Some live ->
  f.(fn_code)!n = Some i ->
  In s (successors_instr i) ->
  Regset.Subset (transfer f s live!!s) live!!n.
Proof.
  unfold analyze; intros. eapply DS.fixpoint_solution; eauto.
  intros. unfold transfer; rewrite H2. apply DS.L.eq_refl.
Qed.
```

Key insight: The side condition `forall n a, code!n = None -> L.eq (transf n a) L.bot` is discharged by showing that when `fn_code!n = None`, the transfer function returns `Regset.empty` (which is `L.bot`). This works identically for both standard and conservative transfer functions since both return `Regset.empty` in the `None` case.

The solver gives `L.ge res!!n (transf s res!!s)`, and since `LFSet.ge x y` is defined as `Regset.Subset y x`, this directly yields `Regset.Subset (transfer f s live!!s) live!!n`.

### Pattern 3: Conservative Transfer Function
**What:** Modified transfer that always includes operation arguments
**When to use:** When the proof needs argument liveness unconditionally
**Example:**
```coq
(* ProofLiveness.transfer -- conservative variant *)
Definition transfer
  (f: function) (pc: node) (after: Regset.t) : Regset.t :=
  match f.(fn_code)!pc with
  | None => Regset.empty
  | Some i =>
    match i with
    | Inop s => after
    | Iop op args res s =>
        reg_list_live args (reg_dead res after)    (* ALWAYS include args *)
    | Iload chunk addr args dst s =>
        reg_list_live args (reg_dead dst after)    (* ALWAYS include args *)
    | Istore chunk addr args src s =>
        reg_list_live args (reg_live src after)
    | Icall sig ros args res s =>
        reg_list_live args (reg_sum_live ros (reg_dead res after))
    | Itailcall sig ros args =>
        reg_list_live args (reg_sum_live ros Regset.empty)
    | Ibuiltin ef args res s =>
        reg_list_live (params_of_builtin_args args)
          (reg_list_dead (params_of_builtin_res res) after)
    | Icond cond args ifso ifnot =>
        reg_list_live args after
    | Ijumptable arg tbl =>
        reg_live arg after
    | Ireturn optarg =>
        reg_option_live optarg Regset.empty
    end
  end.
```

### Pattern 4: reg_list_live_in Membership Lemma
**What:** Prove that `In r args` implies `Regset.In r (reg_list_live args s)`
**When to use:** Downstream proofs need to extract membership from argument lists
**Example:**
```coq
Lemma reg_list_live_in:
  forall r args s,
  In r args ->
  Regset.In r (reg_list_live args s).
Proof.
  induction args; simpl; intros.
  - contradiction.
  - destruct H.
    + subst. apply reg_list_live_incl. apply Regset.add_1. reflexivity.
    + apply IHargs. auto.
Qed.
```

This requires an auxiliary monotonicity lemma showing that `Regset.In r s` implies `Regset.In r (reg_list_live args s)` -- i.e., `reg_list_live` only adds elements, never removes them.

### Anti-Patterns to Avoid
- **Modifying Liveness.v:** This breaks dead code elimination and register allocation. Always create a separate file.
- **Using `fixpoint_allnodes`:** While it avoids the side condition, it is less efficient and not necessary here. The standard `fixpoint` with its trivial side condition is preferred.
- **Importing ProofLiveness from Liveness:** ProofLiveness should be fully standalone, importing only from CompCert's base libraries (Coqlib, Maps, Lattice, AST, Op, Registers, RTL, Kildall). It should NOT import Liveness.v.
- **Proving reg_list_live_in directly without monotonicity:** The direct induction gets stuck because `reg_list_live (a :: args) s = reg_list_live args (Regset.add a s)`, and the IH gives membership in `reg_list_live args s` but you need it in `reg_list_live args (Regset.add a s)`. The monotonicity/inclusion helper resolves this.

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Dataflow fixpoint computation | Custom worklist algorithm | `Kildall.Backward_Dataflow_Solver` | CompCert's Kildall module provides a verified solver with guaranteed convergence and machine-checked fixpoint properties |
| Register set operations | Custom set library | `Regset` (FSetAVL) | `Regset` provides all needed operations (`add`, `remove`, `mem`, `Subset`, `In`, `union`, `empty`) with correct membership lemmas |
| Lattice structure | Custom lattice | `LFSet(Regset)` | Automatically lifts `Regset` to a semi-lattice where `ge = Subset` (reversed), `bot = empty`, `lub = union` |

**Key insight:** The entire analysis infrastructure is already built. ProofLiveness.v is a thin layer on top of existing CompCert machinery -- the only novel content is the two-line change to the transfer function and one new membership lemma.

## Common Pitfalls

### Pitfall 1: Forgetting to handle the `None` case in `transfer`
**What goes wrong:** If `transfer` does not return `Regset.empty` when `fn_code!pc = None`, the `analyze_solution` proof fails because the side condition `forall n a, code!n = None -> L.eq (transf n a) L.bot` cannot be discharged.
**Why it happens:** Copy-paste error or forgetting that `DS.fixpoint_solution` requires this condition for the efficient solver.
**How to avoid:** Keep the `| None => Regset.empty` case identical to `Liveness.v`.
**Warning signs:** `eapply DS.fixpoint_solution` leaves an unsolvable subgoal about `L.eq`.

### Pitfall 2: Wrong direction of `Regset.Subset` in `analyze_solution`
**What goes wrong:** Stating the conclusion as `Regset.Subset live!!n (transfer f s live!!s)` (backwards).
**Why it happens:** Confusion about `LFSet.ge` direction. `LFSet.ge x y` is `Regset.Subset y x` (y is a subset of x), so `L.ge res!!n (transf s res!!s)` means the transfer result is a SUBSET of the fixpoint value.
**How to avoid:** The conclusion should be `Regset.Subset (transfer f s live!!s) live!!n` -- the transfer function result flows INTO the fixpoint value at node n.
**Warning signs:** Proof seems to require the wrong direction of subset inclusion.

### Pitfall 3: reg_list_live_in induction without monotonicity helper
**What goes wrong:** Direct induction on `args` in `reg_list_live_in` gets stuck at the `a :: args` case.
**Why it happens:** `reg_list_live (a :: args) s` unfolds to `reg_list_live args (Regset.add a s)`. When `r = a`, you need `Regset.In a (reg_list_live args (Regset.add a s))`. You know `Regset.In a (Regset.add a s)` from `Regset.add_1`, but the IH only says `In r args -> Regset.In r (reg_list_live args s)` -- it says nothing about elements already in `s`.
**How to avoid:** First prove a monotonicity lemma: `Regset.In r s -> Regset.In r (reg_list_live args s)`. Then use it to lift `Regset.add_1` through the recursive `reg_list_live` calls.
**Warning signs:** The `subst; apply Regset.add_1; reflexivity` tactic fails because the goal has `reg_list_live args (...)` wrapped around the add.

### Pitfall 4: Forgetting to add ProofLiveness.v to the Makefile
**What goes wrong:** `make backend/ProofLiveness.vo` fails with "No rule to make target".
**Why it happens:** The Makefile compiles `.v` files listed in the `BACKEND` variable. VPATH handles directory resolution, but the file must appear in the file list.
**How to avoid:** Add `ProofLiveness.v` to the `BACKEND` variable in the Makefile (line ~176 area, near `Liveness.v`), then run `make depend` to regenerate `.depend`.
**Warning signs:** `make depend` does not list ProofLiveness.v in its output.

### Pitfall 5: Module name collision with Liveness.v
**What goes wrong:** If ProofLiveness.v uses the same module names (`RegsetLat`, `DS`) as Liveness.v, files that import both may have ambiguous references.
**Why it happens:** Coq module names are global within a compilation unit.
**How to avoid:** Use distinct module names: `Module PLRegsetLat := LFSet(Regset).` and `Module PLDS := Backward_Dataflow_Solver(PLRegsetLat)(NodeSetBackward).` Alternatively, since ProofLiveness.v and Liveness.v are never imported in the same file (downstream files use one or the other), the standard names can be reused -- but distinct names are safer.
**Warning signs:** "Ambiguous reference" errors when compiling downstream files.

## Code Examples

### Complete ProofLiveness.v Transfer Function
```coq
(* Source: derived from backend/Liveness.v lines 68-104, with modifications *)

(* Reuse Liveness.v helper definitions -- these are identical *)
Notation reg_live := Regset.add.
Notation reg_dead := Regset.remove.

Definition reg_option_live (or: option reg) (lv: Regset.t) :=
  match or with None => lv | Some r => reg_live r lv end.

Definition reg_sum_live (ros: reg + ident) (lv: Regset.t) :=
  match ros with inl r => reg_live r lv | inr s => lv end.

Fixpoint reg_list_live
  (rl: list reg) (lv: Regset.t) {struct rl} : Regset.t :=
  match rl with
  | nil => lv
  | r1 :: rs => reg_list_live rs (reg_live r1 lv)
  end.

Fixpoint reg_list_dead
  (rl: list reg) (lv: Regset.t) {struct rl} : Regset.t :=
  match rl with
  | nil => lv
  | r1 :: rs => reg_list_dead rs (reg_dead r1 lv)
  end.

(* Conservative transfer: always include Iop/Iload args *)
Definition transfer
  (f: function) (pc: node) (after: Regset.t) : Regset.t :=
  match f.(fn_code)!pc with
  | None => Regset.empty
  | Some i =>
    match i with
    | Inop s => after
    | Iop op args res s =>
        reg_list_live args (reg_dead res after)
    | Iload chunk addr args dst s =>
        reg_list_live args (reg_dead dst after)
    | Istore chunk addr args src s =>
        reg_list_live args (reg_live src after)
    | Icall sig ros args res s =>
        reg_list_live args (reg_sum_live ros (reg_dead res after))
    | Itailcall sig ros args =>
        reg_list_live args (reg_sum_live ros Regset.empty)
    | Ibuiltin ef args res s =>
        reg_list_live (params_of_builtin_args args)
          (reg_list_dead (params_of_builtin_res res) after)
    | Icond cond args ifso ifnot =>
        reg_list_live args after
    | Ijumptable arg tbl =>
        reg_live arg after
    | Ireturn optarg =>
        reg_option_live optarg Regset.empty
    end
  end.
```

### Monotonicity Helper for reg_list_live
```coq
(* Helper: reg_list_live preserves existing membership *)
Lemma reg_list_live_incl:
  forall args s r,
  Regset.In r s -> Regset.In r (reg_list_live args s).
Proof.
  induction args; simpl; intros.
  - assumption.
  - apply IHargs. apply Regset.add_2. assumption.
Qed.

(* Main membership lemma *)
Lemma reg_list_live_in:
  forall r args s,
  In r args -> Regset.In r (reg_list_live args s).
Proof.
  induction args; simpl; intros.
  - contradiction.
  - destruct H as [H | H].
    + subst. apply reg_list_live_incl. apply Regset.add_1. reflexivity.
    + apply IHargs. assumption.
Qed.
```

### FSetAVL Lemma Signatures (for reference)
```coq
(* Key Regset lemmas from FSetAVL.Make(OrderedPositive):
   - Regset.add_1 : forall s x y, x = y -> Regset.In y (Regset.add x s)
       Note: uses OrderedPositive.eq which is Coq's eq on positive
   - Regset.add_2 : forall s x y, Regset.In y s -> Regset.In y (Regset.add x s)
   - Regset.add_3 : forall s x y, x <> y -> Regset.In y (Regset.add x s) -> Regset.In y s
   - Regset.empty_1 : forall x, ~ Regset.In x Regset.empty
   - Regset.mem_1 : forall s x, Regset.In x s -> Regset.mem x s = true
   - Regset.mem_2 : forall s x, Regset.mem x s = true -> Regset.In x s
   - Regset.Subset : defined as forall a, Regset.In a s1 -> Regset.In a s2
*)
```

### Makefile Modification
```makefile
# In Makefile, around line 176, add ProofLiveness.v to BACKEND:
  Kildall.v Liveness.v ProofLiveness.v \
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| `match_rs` quantifies over ALL registers | `match_rs` restricted to LIVE registers | This branch (rtl-liveness) | Requires liveness info in proof, but matches inference oracle's sparse approach |
| Uses `Liveness.analyze` everywhere | Will split: `Liveness.analyze` for DCE/regalloc, `ProofLiveness.analyze` for fault tolerance proof | This phase | Clean separation of concerns |

**Deprecated/outdated:**
- The current `RTLtolerant.v` still references `Liveness.analyze` -- this must be changed to `ProofLiveness.analyze` in Phase 3

## Open Questions

1. **Module name collision risk**
   - What we know: Both `Liveness.v` and `ProofLiveness.v` will define `Module RegsetLat` and `Module DS` at the top level. Files that import both would see a conflict.
   - What's unclear: Whether any file will ever need to import both simultaneously.
   - Recommendation: Use the same names (for simplicity/readability), since downstream files (RTLcolor.v, RTLcolorcheck.v, RTLtolerant.v) will be switched from Liveness to ProofLiveness, not importing both. If a collision arises later, prefix with `PL` (e.g., `PLRegsetLat`).

2. **Regset.add_1 signature with OrderedPositive.eq**
   - What we know: `Regset.add_1` in Coq 8.20 FSetAVL expects `OrderedPositive.eq x y` which should be definitionally equal to `x = y` since OrderedPositive uses `Pos.eq` = `@eq positive`.
   - What's unclear: Whether `reflexivity` alone suffices or `apply Pos.eq_refl` is needed.
   - Recommendation: Try `reflexivity` first; if it fails, use `apply OrderedPositive.eq_refl` or unfold the equality.

## Validation Architecture

### Test Framework
| Property | Value |
|----------|-------|
| Framework | Coq 8.20.0 proof checker |
| Config file | `_CoqProject` (R flags for all directories) |
| Quick run command | `make backend/ProofLiveness.vo` |
| Full suite command | `make proof` (all .v files) |

### Phase Requirements to Test Map
| Req ID | Behavior | Test Type | Automated Command | File Exists? |
|--------|----------|-----------|-------------------|-------------|
| PLIV-01 | Conservative transfer function includes Iop/Iload args unconditionally | unit (Coq type-check) | `make backend/ProofLiveness.vo` | No -- Wave 0 |
| PLIV-02 | Kildall solver instantiation and `analyze` exposed | unit (Coq type-check) | `make backend/ProofLiveness.vo` | No -- Wave 0 |
| PLIV-03 | `analyze_solution` theorem proved | unit (Coq proof-check) | `make backend/ProofLiveness.vo` | No -- Wave 0 |
| PLIV-04 | `reg_list_live_in` membership lemma proved | unit (Coq proof-check) | `make backend/ProofLiveness.vo` | No -- Wave 0 |
| PLIV-05 | Standalone build succeeds | integration | `make backend/ProofLiveness.vo && grep -w 'Admitted' backend/ProofLiveness.v; test $? -ne 0` | No -- Wave 0 |

### Sampling Rate
- **Per task commit:** `make backend/ProofLiveness.vo`
- **Per wave merge:** `make backend/ProofLiveness.vo && grep -cw 'Admitted' backend/ProofLiveness.v | grep -q '^0$'`
- **Phase gate:** `make backend/ProofLiveness.vo` succeeds with zero Admitted

### Wave 0 Gaps
- [ ] `backend/ProofLiveness.v` -- the entire file (PLIV-01 through PLIV-05)
- [ ] `Makefile` BACKEND list update -- add ProofLiveness.v
- [ ] `.depend` regeneration -- `make depend`

## Sources

### Primary (HIGH confidence)
- `backend/Liveness.v` (lines 1-148) -- complete reference implementation being adapted
- `backend/Kildall.v` (lines 888-1076) -- `BACKWARD_DATAFLOW_SOLVER` interface and `Backward_Dataflow_Solver` implementation
- `lib/Lattice.v` (lines 600-639) -- `LFSet` functor defining `ge = Subset`, `bot = empty`, `lub = union`
- `backend/Registers.v` (line 99) -- `Module Regset := FSetAVL.Make(OrderedPositive)`
- `backend/RTL.v` (lines 422-434) -- `successors_instr` definition
- `backend/RTLtolerant.v` (lines 23-29, 62-95) -- `match_rs` and `match_states` definitions showing how liveness is consumed
- `backend/RTLcolor.v` (lines 101-224) -- `wc_instruction` and `wc_function` showing how liveness is consumed

### Secondary (MEDIUM confidence)
- `backend/RTLtmrspec.v` (lines 1189-1201) -- existing proof pattern for `Regset.add_1`/`Regset.add_2` usage in membership lemmas

### Tertiary (LOW confidence)
- None

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH -- all libraries are in-tree CompCert modules, directly inspected
- Architecture: HIGH -- ProofLiveness.v is a straightforward clone of Liveness.v with two lines changed
- Pitfalls: HIGH -- all pitfalls derive from direct code inspection and understanding of the Kildall framework's side conditions
- Membership lemma: HIGH -- proof strategy verified by examining existing `in_pset_of_list` / `in_regset_of_list` patterns in RTLtmrspec.v/RTLdmrspec.v which use the same `Regset.add_1`/`Regset.add_2` approach

**Research date:** 2026-03-04
**Valid until:** Indefinite (all sources are in-tree, stable CompCert infrastructure)
