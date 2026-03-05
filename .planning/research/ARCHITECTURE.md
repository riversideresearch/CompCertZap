# Architecture Patterns

**Domain:** Coq proof component dependency graph for liveness-bounded fault tolerance proof
**Researched:** 2026-03-04

## Recommended Architecture

The liveness-bounded proof update involves five Coq files plus one OCaml file, connected by a strict dependency chain. The new `ProofLiveness.v` slots in at the bottom of the chain, and three existing files (`RTLcolor.v`, `RTLcolorcheck.v`, `RTLtolerant.v`) must swap their `Liveness.analyze` references to `ProofLiveness.analyze`. `Complements.v` at the top of the chain requires no direct changes -- it consumes only the types and theorems exported by `RTLcolorcheck` and `RTLtolerant`, which preserve their API shape.

```
                      driver/Complements.v
                     /                    \
                    /                      \
    RTLcolorcheck.check_program_sound   RTLtolerant.faulty_backward_simulation
            |                                    |
     RTLcolorcheck.v                      RTLtolerant.v
       |        |                          |        |
  RTLcolor.v    |                     RTLcolor.v    |
       |        |                          |        |
       +--------+--------------------------+--------+
                          |
               ProofLiveness.v (NEW)
                          |
                    Kildall.v (backward dataflow solver)
```

### Component Boundaries

| Component | Responsibility | Imports (Key) | Exports (Key) |
|-----------|---------------|---------------|---------------|
| `ProofLiveness.v` (NEW) | Conservative backward liveness analysis; always includes Iop/Iload args | `Kildall`, `RTL`, `Registers`, `Op` | `analyze : function -> option (PMap.t Regset.t)`, `analyze_solution` lemma |
| `RTLcolor.v` | Declarative well-coloredness spec parameterized by live sets | `Liveness` (switch to `ProofLiveness`), `RTL`, `Registers` | `wc_instruction`, `wc_function`, `wc_program`, `wc_fundef` |
| `RTLcolorcheck.v` | Boolean checker + soundness proof; calls `infer_coloring` oracle | `RTLcolor`, `Liveness` (switch to `ProofLiveness`), `RTL` | `check_program_sound : check_program p = true -> wc_program p` |
| `RTLtolerant.v` | Faulty backward simulation proof (3-voting non-faulty >= 2-voting faulty) | `RTLcolor`, `RTLfault`, `RTLtmr`, `Liveness` (switch to `ProofLiveness`) | `faulty_backward_simulation : wc_program prog -> backward_simulation ...` |
| `Complements.v` | Top-level theorem composition: C >= faulty RTL | `RTLcolorcheck`, `RTLtolerant`, `Compiler`, `RTLagreement`, `Novotes` | `transf_c_program_to_rtl_preservation_faulty` |
| `RTLinfercolor.ml` | OCaml oracle: union-find color inference using live sets | Extracted Coq types | `infer_coloring : function -> PMap.t Regset.t -> option (node -> reg -> color)` |

### Data Flow: How Liveness Information Flows Through Proofs

**Current flow (using `Liveness.analyze`):**

```
1. RTLcolorcheck.check_function calls Liveness.analyze f -> Some live
2. Passes live to infer_coloring f live (OCaml oracle)
3. Passes live to check_col_function live col f (Boolean checker)
4. check_col_function_sound proves:
     Liveness.analyze f = Some live ->
     check_col_function live col f = true ->
     wc_function col f
5. wc_function carries the live proof internally:
     wc_function_function : forall f live,
       Liveness.analyze f = Some live -> ... -> wc_function col f
6. RTLtolerant.match_states / match_stackframes carry:
     LIVE: Liveness.analyze f = Some live
   and use live !! pc to bound register match invariants
7. RTLtolerant uses Liveness.analyze_solution to step live sets forward
```

**Target flow (using `ProofLiveness.analyze`):**

Same structure, but every occurrence of `Liveness.analyze` is replaced with `ProofLiveness.analyze` in steps 1-7. The critical difference is that `ProofLiveness.transfer` is conservative: for `Iop op args res succ`, it always does `reg_list_live args (reg_dead res after)` regardless of whether `res` is live after. This guarantees that instruction arguments are always in the live set, which `RTLtolerant` needs to discharge `Val.lessdef` obligations for `eval_operation` and `eval_addressing`.

**Key insight:** The live set at `pc` computed by `ProofLiveness` is a superset of the live set computed by `Liveness`. This means:
- The `Regset.For_all` constraints in `wc_instruction` are *weaker* (easier to satisfy) with ProofLiveness because the quantification domain is larger but the color consistency must still hold
- Wait -- actually this is reversed. A *larger* live set at pc means the `Regset.For_all` constraints in `wc_instruction` are *stronger* (harder to satisfy for the color checker), because more registers must satisfy color consistency
- However, the checker already operates on the actual live set, and the inference oracle already produces colorings consistent with whatever live set is passed in
- For the simulation proof in `RTLtolerant`, a larger live set means more registers satisfy `match_rs`, which means more `Val.lessdef` facts are available, which is exactly what we need

**The tradeoff is:** Harder for the checker to pass (more registers must be consistently colored) but easier for the simulation proof (more registers are known to match). Since the inference oracle already produces colorings that satisfy the larger set (it already uses liveness-bounded sparse inference), the checker should still pass.

### Precise Import Graph (What Imports What)

```
ProofLiveness.v
  Imports: Coqlib, Maps, Lattice, AST, Op, Registers, RTL, Kildall
  (Same as Liveness.v but with modified transfer function)

RTLcolor.v
  Imports: AST, Errors, Coqlib, Events, Integers, List, Maps, Registers, RTL, Values
  Imports: Liveness  <-- CHANGE TO ProofLiveness
  Uses: Liveness.analyze in wc_function constructor (line 221)

RTLcolorcheck.v
  Imports: AST, Errors, Coqlib, Events, Integers, List, Maps, Registers, RTL, RTLcolor, Values
  Imports: Liveness  <-- CHANGE TO ProofLiveness
  Uses: Liveness.analyze in check_function (line 484)
  Uses: Liveness.analyze in check_col_function_sound premise (line 446)

RTLtolerant.v
  Imports: AST, Behaviors, Builtins2, Coqlib, Events, Globalenvs, Linking, Maps, Registers
  Imports: RTLtmr, RTLtmrspec, RTL, RTLcolor, RTLfault, Smallstep, Values
  Does NOT directly import Liveness -- gets it transitively through RTLcolor
  Uses: Liveness.analyze in match_stackframes (line 68) and match_states (line 91)
  CHANGE: Must add ProofLiveness import and switch LIVE hypotheses

Complements.v
  Imports: Coqlib, Errors, AST, Linking, Events, Smallstep, Behaviors
  Imports: Csyntax, Csem, Cstrategy, Asm, Compiler, Compopts
  Imports: RTLagreement, RTLcolorcheck, RTLfault, RTLtolerant
  Imports: Novotes, Novotesproof, Asmagreement, Builtins2
  Does NOT directly import Liveness or RTLcolor
  Uses: RTLcolorcheck.check_program_sound (line 559)
  Uses: RTLtolerant.faulty_backward_simulation (line 558)
  NO CHANGES needed if check_program_sound and faulty_backward_simulation preserve their type signatures
```

### Why Complements.v Requires No Changes

The top-level theorem `transf_c_program_to_rtl_preservation_faulty` (line 546-570) only touches:

1. `RTLcolorcheck.check_program_sound : check_program tp = true -> wc_program tp`
2. `RTLtolerant.faulty_backward_simulation : wc_program prog -> backward_simulation ...`

Both `wc_program` and `check_program_sound` keep the same type signatures regardless of whether they internally use `Liveness.analyze` or `ProofLiveness.analyze`. The `wc_function` inductive hides the analysis choice behind an existential (`exists col, wc_function col f`), and `faulty_backward_simulation` takes `wc_program prog` as a hypothesis. So the change is entirely encapsulated.

**However:** `Complements.v` must be *rebuilt* because it transitively depends on `RTLcolorcheck.vo` and `RTLtolerant.vo`. The `.vo` files embed proof terms that reference the analysis, so changing the analysis requires recompilation of all downstream `.vo` files.

## Patterns to Follow

### Pattern 1: Kildall Backward Dataflow Instantiation
**What:** Use CompCert's generic backward dataflow solver to compute fixpoints
**When:** Creating a new backward analysis (like ProofLiveness)
**Why:** This is the standard CompCert pattern. Liveness.v, Deadcode.v, and others all follow it.

```coq
(* In ProofLiveness.v *)
Module RegsetLat := LFSet(Regset).
Module DS := Backward_Dataflow_Solver(RegsetLat)(NodeSetBackward).

Definition transfer (f: function) (pc: node) (after: Regset.t) : Regset.t :=
  match f.(fn_code)!pc with
  | None => Regset.empty
  | Some i =>
    match i with
    | Iop op args res s =>
        (* CONSERVATIVE: always include args, unlike Liveness.transfer *)
        reg_list_live args (reg_dead res after)
    | Iload chunk addr args dst s =>
        (* CONSERVATIVE: always include args *)
        reg_list_live args (reg_dead dst after)
    (* ... other cases same as Liveness.transfer ... *)
    end
  end.

Definition analyze (f: function): option (PMap.t Regset.t) :=
  DS.fixpoint f.(fn_code) successors_instr (transfer f).
```

### Pattern 2: Analysis Soundness Lemma
**What:** Prove that the fixpoint satisfies the transfer function at every edge
**When:** Every backward dataflow analysis needs this for downstream proofs

```coq
Lemma analyze_solution:
  forall f live n i s,
  analyze f = Some live ->
  f.(fn_code)!n = Some i ->
  In s (successors_instr i) ->
  Regset.Subset (transfer f s live!!s) live!!n.
```

This is proved by a single call to `DS.fixpoint_solution` plus a corner case for `None` nodes. Identical structure to `Liveness.analyze_solution`.

### Pattern 3: Liveness Membership Helpers
**What:** Derive `Regset.In r (live !! pc)` for instruction arguments from `analyze_solution`
**When:** In RTLtolerant, to discharge `Val.lessdef` obligations by applying `match_rs`

```coq
(* Helper: arguments of an Iop at pc are in live !! pc *)
Lemma args_live_at_iop f live pc op args res succ :
  analyze f = Some live ->
  f.(fn_code) ! pc = Some (Iop op args res succ) ->
  forall r, In r args -> Regset.In r (live !! pc).
Proof.
  intros Hlive Hpc r Hin.
  eapply Regset.Subset_trans.
  2: { eapply analyze_solution; eauto. simpl; auto. }
  (* From transfer definition: args are added to live set *)
  unfold transfer; rewrite Hpc.
  apply reg_list_live_in; auto.
Qed.
```

These helpers are the new proof infrastructure that bridges ProofLiveness and RTLtolerant. They replace the current proof gap where RTLtolerant cannot show argument liveness.

## Anti-Patterns to Avoid

### Anti-Pattern 1: Modifying Liveness.v Directly
**What:** Changing the transfer function in the existing `Liveness.v`
**Why bad:** `Liveness.v` is consumed by `Deadcode.v` (dead code elimination) and `Allocation.v` (register allocation). Making the transfer function conservative (always including Iop/Iload args) would over-approximate liveness for DCE, preventing it from eliminating dead instructions. It would also affect register allocation quality.
**Instead:** Create a separate `ProofLiveness.v` that is used only by the fault tolerance proof components.

### Anti-Pattern 2: Changing wc_function Constructor Shape
**What:** Altering the fields or type signature of `wc_function`
**Why bad:** `wc_function` is consumed by RTLtolerant's `match_stackframes` and `match_states`. Changing its shape (e.g., adding fields, removing the `live` parameter) would cascade into every inversion of `wc_function` in the 2600-line RTLtolerant proof.
**Instead:** Only swap `Liveness.analyze` to `ProofLiveness.analyze` in the `WC_LIVE` field. The constructor shape `wc_function_function : forall f live, analyze f = Some live -> ... -> wc_function col f` stays identical.

### Anti-Pattern 3: Leaving check_col_instr_sound Admitted
**What:** Keeping the `Admitted` in `RTLcolorcheck.v` line 443
**Why bad:** The entire chain depends on this lemma. `check_function_sound` calls it (line 464), `check_program_sound` calls `check_function_sound` (line 521), and `Complements.v` calls `check_program_sound` (line 559). An `Admitted` here means the top-level theorem has no actual proof backing.
**Instead:** Complete the proof case-by-case. The commented-out proof (lines 249-442) shows the old structure before the switch from `PTree_Properties.for_all` to `Regset.for_all`. The new proof follows the same pattern but uses `Regset.for_all_correct` instead of `PTree_Properties.for_all_correct`.

## Suggested Build Order (Dependencies Between Components)

### Phase 1: ProofLiveness.v (standalone, no existing file changes)

**Dependencies:** Only `Kildall`, `RTL`, standard CompCert libs
**What to build:** `make backend/ProofLiveness.vo`
**Parallel work possible:** None yet, but this is a clean new file

Key deliverables:
- `transfer` function with conservative Iop/Iload handling
- `analyze` via Kildall solver
- `analyze_solution` soundness lemma
- Helper lemmas for argument membership (`reg_list_live_in`, etc.)

### Phase 2: RTLcolor.v (swap analysis reference)

**Dependencies:** ProofLiveness.vo
**What to build:** `make backend/RTLcolor.vo`
**Changes:** Single line swap: `Liveness` import -> `ProofLiveness`, and `Liveness.analyze` -> `ProofLiveness.analyze` in `wc_function` constructor (line 221)
**Risk:** Very low -- the `wc_function` inductive only stores the analysis result, not the analysis internals

### Phase 3: RTLcolorcheck.v (swap analysis + complete Admitted proof)

**Dependencies:** RTLcolor.vo, ProofLiveness.vo
**What to build:** `make backend/RTLcolorcheck.vo`
**Changes:**
1. Swap `Liveness` import to `ProofLiveness`
2. Swap `Liveness.analyze` to `ProofLiveness.analyze` in `check_function` (line 484) and `check_col_function_sound` (line 446)
3. Complete `check_col_instr_sound` proof (currently Admitted at line 443)

**Risk:** MEDIUM -- the `check_col_instr_sound` proof is the main work item. The old proof (commented out, lines 249-442) needs updating from `PTree_Properties.for_all_correct` to `Regset.for_all_correct`, but the logical structure is the same.

**Note:** The `infer_coloring` parameter type is `function -> PMap.t Regset.t -> option (node -> reg -> color)`. The `PMap.t Regset.t` argument's provenance (Liveness vs ProofLiveness) is irrelevant to the parameter's type -- it is just `PMap.t Regset.t` either way. So the extraction wiring in `extraction.v` and the OCaml `RTLinfercolor.ml` require NO changes.

### Phase 4: RTLtolerant.v (swap analysis + rebuild simulation proof)

**Dependencies:** RTLcolor.vo, ProofLiveness.vo (does NOT depend on RTLcolorcheck.vo)
**What to build:** `make backend/RTLtolerant.vo`
**Changes:**
1. Add `ProofLiveness` import (currently imports Liveness transitively through RTLcolor)
2. Swap `Liveness.analyze` to `ProofLiveness.analyze` in `match_stackframes` (line 68) and `match_states` (line 91)
3. Add ProofLiveness membership lemmas and update proof scripts that need `Regset.In` facts for instruction arguments

**Risk:** HIGH -- this is a 2600-line proof file. The plan identifies the `exec_Iop` case near line 1367 as the known breakpoint. Additional cases (`Iload`, `Istore`, `Icall`, `Itailcall`, builtins) also need `Val.lessdef` for arguments, which requires `Regset.In` facts from ProofLiveness.

**Critical insight for build order:** Phase 3 (RTLcolorcheck) and Phase 4 (RTLtolerant) are INDEPENDENT of each other and can be developed in parallel. They both depend on Phase 2 (RTLcolor) but not on each other.

```
                     Phase 1: ProofLiveness.v
                            |
                     Phase 2: RTLcolor.v
                    /                    \
          Phase 3: RTLcolorcheck.v    Phase 4: RTLtolerant.v
                    \                    /
                     Phase 5: Complements.v (rebuild only)
```

### Phase 5: Complements.v (rebuild, no source changes expected)

**Dependencies:** RTLcolorcheck.vo, RTLtolerant.vo
**What to build:** `make driver/Complements.vo`
**Changes:** None expected. Rebuild verifies that the type signatures compose correctly.
**Risk:** LOW -- if RTLcolorcheck and RTLtolerant preserve their export signatures (which they should), this is just a recompilation.

### Build Commands for Incremental Development

```bash
# Phase 1: standalone new file
make backend/ProofLiveness.vo

# Phase 2: depends on Phase 1
make backend/RTLcolor.vo

# Phase 3 and 4: can run in parallel after Phase 2
make backend/RTLcolorcheck.vo &
make backend/RTLtolerant.vo &
wait

# Phase 5: final rebuild
make driver/Complements.vo

# Validation
make check-admitted
make ccomp
```

## Files NOT Affected by This Change

These files use `Liveness.analyze` but are NOT part of the fault tolerance proof chain and must NOT be changed:

| File | Why It Uses Liveness | Why It Is Unaffected |
|------|---------------------|---------------------|
| `backend/Deadcode.v` | Dead code elimination pass | Uses Liveness for its own optimization; not in fault tolerance path |
| `backend/RTLtmr.v` | TMR pass uses `live_regs` to compute entry-point live registers | Uses `Liveness.analyze` for the *transformation*, not the *proof*. The TMR pass itself is upstream of the color checker. |
| `backend/RTLdmr.v` | DMR pass uses `live_regs` similarly | Same as RTLtmr.v |
| `backend/RTLtmrspec.v` | TMR correctness proof mentions `Liveness.analyze` | Only in a `destruct (Liveness.analyze _)` pattern match (line 1408), not using the result for color/tolerance |
| `backend/RTLdmrspec.v` | DMR correctness proof mentions `Liveness.analyze` | Same pattern as RTLtmrspec.v |

The TMR/DMR passes use `Liveness` to decide which registers to replicate at function entry. This is a code generation concern (the transformation), not a proof concern (the simulation). Changing what the TMR pass *does* is out of scope. The fault tolerance proof only needs ProofLiveness for the *verification* that the result is well-colored and fault-tolerant.

## Scalability Considerations

| Concern | Current State | After ProofLiveness |
|---------|--------------|---------------------|
| Proof compile time | RTLtolerant.v is already the longest-compiling file (~minutes) | ProofLiveness adds trivial overhead; RTLtolerant proof scripts may be slightly longer but same complexity |
| Color inference memory | Sparse inference already uses liveness-bounded tables | ProofLiveness produces slightly larger live sets (Iop/Iload args always included), so sparse tables are marginally larger, but still O(live regs) not O(all regs) |
| Checker runtime | `check_program` iterates all instructions | No change -- same checker algorithm, just slightly larger Regset.for_all domains |

## Sources

- `backend/Liveness.v` -- existing analysis, lines 68-114 (transfer function and solver instantiation)
- `backend/RTLcolor.v` -- well-coloredness spec, lines 101-247
- `backend/RTLcolorcheck.v` -- checker implementation and soundness, lines 1-523
- `backend/RTLtolerant.v` -- faulty backward simulation, lines 1-2612
- `driver/Complements.v` -- top-level theorem, lines 546-570
- `plans/liveness-invariant-plan.md` -- existing plan document
- `.planning/PROJECT.md` -- project context
