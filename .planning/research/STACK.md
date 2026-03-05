# Technology Stack: ProofLiveness Kildall Analysis for CompCertZAP

**Project:** CompCertZAP Liveness-Bounded Fault Tolerance Proof
**Researched:** 2026-03-04
**Overall confidence:** HIGH (all recommendations based on direct codebase inspection of existing CompCert patterns)

## Executive Summary

Defining a custom backward dataflow analysis in CompCert's Kildall framework is a mechanical, well-trodden process. The codebase contains four existing instantiations of `Backward_Dataflow_Solver` (Liveness, Deadcode, Allocation, Regalloc) that all follow an identical three-step recipe: (1) define a lattice module, (2) instantiate the solver functor, (3) wrap `DS.fixpoint` as `analyze` and prove `analyze_solution`. The `ProofLiveness` analysis needs no novel Coq engineering -- it reuses the same lattice (`RegsetLat`), same node set (`NodeSetBackward`), and same solver functor, differing only in its transfer function.

The critical design decision is how the transfer function differs from `Liveness.transfer`. The existing transfer conditionally omits `Iop`/`Iload` argument registers when the destination is dead (an optimization for dead code elimination). The proof-liveness transfer must unconditionally include those arguments because the simulation proof in `RTLtolerant.v` needs `Val.lessdef` for all instruction arguments at every reachable PC, regardless of whether the destination register is "live" in the DCE sense.

## Recommended Stack

### Kildall Framework Instantiation

| Component | Module/Definition | Source File | Purpose | Why This One |
|-----------|------------------|-------------|---------|--------------|
| Lattice | `RegsetLat` (= `LFSet(Regset)`) | `lib/Lattice.v` | Semi-lattice over register sets, ordered by subset inclusion | Already defined and used by `Liveness.v`; `ge` = `Subset`, `lub` = `union`, `bot` = `empty`. Reuse directly. |
| Solver functor | `Backward_Dataflow_Solver(RegsetLat)(NodeSetBackward)` | `backend/Kildall.v` | Worklist-based backward fixpoint solver | Same instantiation as `Liveness.v`. The solver is parameterized only by the lattice and node-set ordering; the transfer function is passed at call site. |
| Node set | `NodeSetBackward` | `backend/Kildall.v` (line 1601) | Reverse-postorder worklist for backward analysis convergence | The only `NODE_SET` implementation designed for backward analyses. All four existing backward analyses use it. |
| Transfer function | `proof_transfer` (new) | `backend/ProofLiveness.v` (new) | Compute "proof-live" registers before each instruction | Must differ from `Liveness.transfer` at `Iop` and `Iload` cases. See design below. |
| Entry point | `DS.fixpoint` | via `Backward_Dataflow_Solver` | The backward fixpoint call | Use the efficient `fixpoint` (not `fixpoint_allnodes`), same as `Liveness.analyze`. Requires the transfer-maps-bot-to-bot side condition, which `proof_transfer` satisfies. |

### Transfer Function Design

| Instruction | `Liveness.transfer` behavior | `proof_transfer` behavior | Rationale |
|------------|------------------------------|--------------------------|-----------|
| `Inop s` | Pass through `after` | Pass through `after` | No difference needed |
| `Iop op args res s` | If `res` in `after`: add `args`, kill `res`. Else: `after` unchanged. | **Always** add `args`, kill `res` | Simulation proof needs `Val.lessdef` for args even when `res` is dead in DCE sense. The `exec_Iop` case in `RTLtolerant.v` (line ~1366) requires `Regset.In arg (live !! pc)` for each arg. |
| `Iload chunk addr args dst s` | If `dst` in `after`: add `args`, kill `dst`. Else: `after` unchanged. | **Always** add `args`, kill `dst` | Same reasoning as `Iop`. The `exec_Iload` case needs `Val.lessdef` for addressing args. |
| `Istore chunk addr args src s` | Add `args`, add `src` | Add `args`, add `src` | No difference needed. Both sides always need these live. |
| `Icall sig ros args res s` | Add `args`, add `ros`, kill `res` | Add `args`, add `ros`, kill `res` | No difference needed. Calls are never dead-code-eliminated. |
| `Itailcall sig ros args` | Add `args`, add `ros`, empty base | Add `args`, add `ros`, empty base | No difference needed. |
| `Ibuiltin ef args res s` | Add builtin arg params, kill builtin res params | Add builtin arg params, kill builtin res params | No difference needed. |
| `Icond cond args ifso ifnot` | Add `args` | Add `args` | No difference needed. |
| `Ijumptable arg tbl` | Add `arg` | Add `arg` | No difference needed. |
| `Ireturn optarg` | Add `optarg`, empty base | Add `optarg`, empty base | No difference needed. |

### Supporting Lemmas (New)

| Lemma | Statement Shape | Purpose | Confidence |
|-------|----------------|---------|------------|
| `analyze_solution` | `analyze f = Some live -> f.(fn_code)!n = Some i -> In s (successors_instr i) -> Regset.Subset (proof_transfer f s live!!s) live!!n` | Core fixpoint property. Analogous to `Liveness.analyze_solution`. One-line proof via `DS.fixpoint_solution`. | HIGH |
| `proof_transfer_args_live` | For `Iop op args res s`: `Regset.Subset (proof_transfer f pc after) live!!pc -> In arg args -> Regset.In arg (live!!pc)` | Helper to discharge `Regset.In` goals for instruction args in simulation. Follows directly from transfer definition. | HIGH |
| `proof_transfer_iload_args_live` | Analogous for `Iload` | Same pattern for load addressing args | HIGH |
| `proof_transfer_incl` | `forall f pc after, Regset.Subset (Liveness.transfer f pc after) (proof_transfer f pc after)` | Shows proof-liveness is a conservative over-approximation of DCE liveness. Useful if any existing proof relies on standard liveness being a lower bound. | MEDIUM (may not be needed) |

## Concrete Coq Definitions

### ProofLiveness.v Structure

```coq
(* Exact module instantiation -- copy from Liveness.v *)
Require Import Coqlib Maps Lattice AST Op Registers RTL Kildall.

Notation reg_live := Regset.add.
Notation reg_dead := Regset.remove.
(* Reuse reg_option_live, reg_sum_live, reg_list_live, reg_list_dead
   from Liveness.v or redefine locally *)

Definition transfer (f: function) (pc: node) (after: Regset.t) : Regset.t :=
  match f.(fn_code)!pc with
  | None => Regset.empty
  | Some i =>
      match i with
      | Inop s => after
      | Iop op args res s =>
          (* CRITICAL DIFFERENCE: always include args *)
          reg_list_live args (reg_dead res after)
      | Iload chunk addr args dst s =>
          (* CRITICAL DIFFERENCE: always include args *)
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

Module RegsetLat := LFSet(Regset).
Module DS := Backward_Dataflow_Solver(RegsetLat)(NodeSetBackward).

Definition analyze (f: function) : option (PMap.t Regset.t) :=
  DS.fixpoint f.(fn_code) successors_instr (transfer f).

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

### Key Observation: The Side Condition

The efficient backward solver (`DS.fixpoint`, not `DS.fixpoint_allnodes`) requires a side condition:

```coq
forall n a, code!n = None -> L.eq (transf n a) L.bot
```

This says: "transfer at non-existent nodes returns bottom." The `proof_transfer` function satisfies this because the outer match on `f.(fn_code)!pc` returns `Regset.empty` (= `L.bot`) when `None`. This is identical to `Liveness.transfer`. The proof is the same one-liner: `unfold transfer; rewrite H2. apply DS.L.eq_refl.`

## What NOT to Do

### Do NOT modify `Liveness.v`

**Why:** `Liveness.v` is consumed by dead code elimination (`Deadcode.v`), register allocation (`Allocation.v`, `Regalloc.ml`), and linearization (`Linearize.v`). Changing its transfer function would break these passes. The conditional omission of `Iop`/`Iload` args is correct and desirable for DCE: if the result is dead, the whole instruction will be eliminated, so its args need not be live. `ProofLiveness` serves a different purpose (simulation proof soundness, not code transformation).

### Do NOT use `fixpoint_allnodes`

**Why:** `fixpoint_allnodes` is less efficient (starts with all nodes on the worklist instead of just exit points). It exists for cases where the side condition `transf bot = bot` cannot be established. Since `proof_transfer` trivially satisfies this condition, use the efficient `fixpoint` variant. All production CompCert analyses use the efficient variant.

### Do NOT add a new lattice module

**Why:** `RegsetLat` (= `LFSet(Regset)`) is the exact right lattice. The proof-liveness domain is register sets ordered by inclusion, identical to standard liveness. There is no need for a product lattice (like `Deadcode`'s `NA` = needs x memory-needs) or a flat lattice. Adding unnecessary lattice complexity would create proof obligations with no benefit.

### Do NOT parameterize transfer by vote_type

**Why:** The transfer function computes a static property of the CFG structure (which registers are "proof-live"). It does not depend on vote semantics. The `Section VOTE` pattern used in RTL semantics files is unnecessary here. `Liveness.v` is similarly unparameterized.

### Do NOT try to compute proof-liveness at extraction time

**Why:** The analysis result is consumed by Coq proof terms (the `LIVE` hypothesis in `match_states` and `match_stackframes`). It must exist as a Coq-level computation, not an OCaml oracle. The color inference oracle (`RTLinfercolor.ml`) can continue using standard `Liveness.analyze` for its own sparse-table optimization -- these are independent concerns.

### Do NOT define helper notation like `succs_of_instruction` separately

**Why:** CompCert already has `successors_instr` in `RTL.v` (line 422). The backward solver is parameterized by this. Use it directly as `Liveness.v` does.

## Integration Points

### Files That Must Change

| File | Change | Complexity |
|------|--------|------------|
| `backend/ProofLiveness.v` | **New file.** ~100 lines. Transfer + solver instantiation + `analyze_solution`. | Low |
| `backend/RTLcolor.v` | Replace `Liveness.analyze` with `ProofLiveness.analyze` in `wc_function` constructor (line 221). | Trivial (1 line) |
| `backend/RTLcolorcheck.v` | Replace `Liveness.analyze` import/usage. Update `check_col_function` to use `ProofLiveness.analyze`. | Low (import + a few references) |
| `backend/RTLtolerant.v` | Replace `LIVE: Liveness.analyze f = Some live` with `LIVE: ProofLiveness.analyze f = Some live` in `match_stackframes` and `match_states`. Add helper lemma applications to discharge `Regset.In` goals. | Medium (many proof script touchups, but each is small) |
| Build system | Add `ProofLiveness.v` to `_CoqProject` and `Makefile` (BACKEND list). | Trivial |

### Files That Must NOT Change

| File | Why |
|------|-----|
| `backend/Liveness.v` | Used by DCE, regalloc, linearization. Unrelated concern. |
| `backend/Kildall.v` | Generic framework. No modification needed. |
| `lib/Lattice.v` | `RegsetLat` already exists. |
| `backend/RTLfault.v` | Faulty semantics. Independent of analysis. |
| `backend/RTLtmr.v` / `RTLtmrproof.v` | TMR pass. Independent of liveness. |
| `backend/RTLinfercolor.ml` | OCaml oracle. Already uses its own liveness internally. |

## How Analysis Results Flow into Simulation Proofs

The pattern, used identically in `Liveness.v`, `Deadcode.v`, and the target `RTLtolerant.v`:

1. **Match state carries analysis result.** The `match_states` inductive has a hypothesis `LIVE: ProofLiveness.analyze f = Some live`. This threads the fixpoint result through the simulation.

2. **At each step, extract the fixpoint property.** When the simulation advances from `pc` to successor `pc'`, invoke `ProofLiveness.analyze_solution` to obtain:
   ```
   Regset.Subset (transfer f pc' live!!pc') live!!pc
   ```
   This says the transfer-image at the successor is contained in the live set at the current PC.

3. **Use subset to derive membership.** Since `transfer f pc' live!!pc'` contains instruction arguments (by definition of the conservative transfer), and the live set at `pc` is a superset, the args are in `live!!pc`.

4. **Feed membership into `match_rs`.** The `match_rs (live!!pc) (col pc) b rs1 rs2` relation gives `Val.lessdef (rs1#r) (rs2#r)` for any `r` with `Regset.In r (live!!pc)`.

**Concrete proof script pattern:**
```coq
(* In the Iop case of step_simulation: *)
assert (Regset.In arg (live !! pc)).
{ eapply ProofLiveness.analyze_solution in LIVE; eauto.
  (* LIVE gives Subset (transfer f pc' live!!pc') (live!!pc) *)
  apply LIVE.
  (* transfer definition shows arg is in transfer result *)
  unfold ProofLiveness.transfer. rewrite H. (* H: code!pc = Some (Iop ...) *)
  apply reg_list_live_in; auto. (* arg in args -> arg in reg_list_live args ... *) }
apply RS; auto.
```

The key helper lemma needed is `reg_list_live_in`:
```coq
Lemma reg_list_live_in: forall r rl s,
  In r rl -> Regset.In r (reg_list_live rl s).
```

This follows from `Regset.add_spec` by induction on `rl`. It may already exist in CompCert's libraries or need to be proven once in `ProofLiveness.v`.

## Confidence Assessment

| Area | Confidence | Reason |
|------|------------|--------|
| Kildall instantiation pattern | HIGH | Four existing instantiations in codebase follow identical pattern |
| Transfer function design | HIGH | Direct inspection of proof obligations in `RTLtolerant.v` (lines 1362-1370) shows exactly which `Regset.In` facts are needed |
| `analyze_solution` proof | HIGH | One-line proof identical to `Liveness.analyze_solution` (line 124-127) |
| Integration with `RTLcolor.v` | HIGH | `wc_function` constructor explicitly carries `Liveness.analyze f = Some live` -- swap is mechanical |
| Proof script updates in `RTLtolerant.v` | MEDIUM | Each individual case is straightforward, but there are many cases (~10 instruction types x 2 simulation lemmas) |
| Build system integration | HIGH | Standard Makefile/CoqProject addition |

## Sources

All findings are from direct inspection of the following files in the repository:

- `backend/Kildall.v` -- Backward solver functor, `BACKWARD_DATAFLOW_SOLVER` interface, `fixpoint_solution` theorem
- `backend/Liveness.v` -- Reference instantiation pattern, `analyze_solution` proof
- `lib/Lattice.v` -- `LFSet` functor providing `SEMILATTICE` over `FSetInterface.WS`
- `backend/Registers.v` -- `Regset` = `FSetAVL.Make(OrderedPositive)`
- `backend/RTLtolerant.v` -- Proof obligations that drive transfer function design (lines 1358-1400, 1714-1790)
- `backend/RTLcolor.v` -- `wc_function` and `wc_instruction` definitions consuming liveness
- `backend/RTLcolorcheck.v` -- Boolean checker using `live !! pc` for `Regset.for_all`
- `backend/Deadcode.v` -- Second reference instantiation (different lattice, same solver pattern)
- `backend/RTL.v` -- `successors_instr` definition
