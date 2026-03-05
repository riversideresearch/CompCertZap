# CompCert RTL Liveness Analysis

This document summarizes CompCert's RTL liveness analysis, with emphasis on the dead-code-elimination (DCE) optimization encoded directly in its transfer function.

## Scope and location

The analysis described here is the RTL-level analysis in:

- `backend/Liveness.v`

It computes, for each program point `pc`, a set of pseudo-registers that must be live **before** executing the instruction at `pc`.

## What "live" means here

At a high level, register `r` is live at `pc` if there exists a path from `pc` to some future use of `r` such that `r` is not redefined before that use.

CompCert computes this with a standard backward dataflow analysis over register sets (`Regset.t`).

## Domain, direction, and solver

1. Domain: finite sets of registers (`Regset.t`).
2. Order: set inclusion (via `LFSet` lattice).
3. Direction: backward.
4. Engine: `Backward_Dataflow_Solver` from `backend/Kildall.v`.

In `backend/Liveness.v`:

- `Module RegsetLat := LFSet(Regset).`
- `Module DS := Backward_Dataflow_Solver(RegsetLat)(NodeSetBackward).`
- `analyze f := DS.fixpoint f.(fn_code) successors_instr (transfer f).`

The key solver guarantee is exposed as:

- `analyze_solution`:
  for every edge `n -> s`, `transfer f s (live!!s) ⊆ live!!n`.

This is the standard inequational solution property for backward analyses.

## Transfer function

`transfer` takes:

1. current function `f`
2. current node `pc`
3. `after` set (live-out at `pc`)

and returns live-before at `pc`.

Most cases follow the usual shape:

- values read by the instruction are added;
- values overwritten by the instruction are removed;
- control-flow joins are handled by solver iteration over CFG edges.

Examples from `backend/Liveness.v`:

- `Inop s`: unchanged (`after`)
- `Istore ... args src s`: add `args` and `src`
- `Icall ... ros args res s`: add call target register (if indirect), add args, kill `res`
- `Ireturn (Some r)`: only `r` live before return

## DCE-oriented optimization in transfer

The most important nontrivial behavior is for side-effect-free instructions:

- `Iop op args res s`
- `Iload chunk addr args dst s`

In both cases, `transfer` checks whether the destination is live in `after`:

1. If destination is live, keep standard behavior:
   add operands and kill destination.
2. If destination is dead, return `after` unchanged:
   do **not** add operands.

In code (`backend/Liveness.v`):

- `Iop`: branch on `Regset.mem res after`
- `Iload`: branch on `Regset.mem dst after`

### Why this optimization exists

This is intentional and documented in comments in `Liveness.v`: if a side-effect-free instruction computes a dead result, DCE may remove that instruction later, so its operands need not be forced live before it.

Effectively, the analysis is tuned for optimization profitability:

1. smaller live sets
2. more dead instruction elimination opportunities
3. less conservative register pressure

This is a standard "anticipate removable computation" trick in production compilers.

## Relationship to dead code elimination

CompCert's dead-code pass (`backend/Deadcode.v` / `backend/Deadcodeproof.v`) consumes liveness-like information to identify useless computations.

The transfer behavior above aligns with that goal:

1. dead-result pure ops/loads do not keep operands alive;
2. this helps classify such instructions as removable;
3. removing them is semantics-preserving because those instruction classes are treated as side-effect-free in that context.

## Precision and tradeoff

This analysis is precise for DCE, but it is not the same as "all registers read by the current step must be related."

That distinction matters for proofs that require current-step operand relations (for example, simulations that must evaluate the current instruction in lockstep even when its result is dead). In those settings, a stronger "proof liveness" transfer may be needed.

## Additional output: `last_uses`

`Liveness.v` also defines:

- `last_uses_at`
- `last_uses`

These compute registers that are used for the last time at each instruction (based on computed liveness), useful for later analyses/optimizations.

## Summary

CompCert RTL liveness is:

1. a standard backward dataflow analysis over register sets,
2. solved with Kildall's generic framework,
3. intentionally specialized for DCE by suppressing operand liveness for dead-result `Iop`/`Iload`.

That optimization is deliberate, effective, and correct for optimization pipelines, but can be too weak for proof obligations that need stronger per-step operand guarantees.
