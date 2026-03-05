# Color System, Faulty Simulation, and Fault Tolerance Composition

## 1. Purpose of this report

This report explains three things and their relationship:

1. The RTL color system (`backend/RTLcolor.v`, checker in `backend/RTLcolorcheck.v`)
2. The faulty simulation theorem (`backend/RTLtolerant.v`)
3. How both are used in the end-to-end fault tolerance theorem (`driver/Complements.v`)

The key conceptual split is:

- Agreement: handled via 2-vote vs 3-vote semantic bridging (`backend/RTLagreement.v`)
- Separation: handled by well-coloredness and consumed by `RTLtolerant.v`

Together they yield the final faulty-preservation result.

## 2. Fault model (what the theorem protects against)

The faulty semantics is defined in `backend/RTLfault.v`.

- Faulty state is `fstate = { fs_state : RTL.state; fault : bool }`.
- `fault = false` means no fault injected yet; `true` means fault already injected.
- A faulty step wraps an ordinary RTL step and then applies `maybe_zap`.
- `maybe_zap` can either do nothing or overwrite one result register with a `val_compat` value.
- This overwrite is only allowed once, because `maybe_zap_reg` requires input fault bit `false`.
- Fault injection is restricted by `zap_allowed` (for example, no zaps on loads/stores/calls/builtins in the current model).

So this is a single-fault register-zap model, not arbitrary multi-fault corruption.

## 3. How the color system encodes separation

### 3.1 Colors and lane intuition

`RTLcolor.v` defines:

- Basic colors: `Red`, `Green`, `Blue` (independent replicated lanes)
- Non-basic colors: `White`, `Pink` (unprotected/transitional states)

Intuition:

- R/G/B represent separated replicas.
- `White` marks values that are not currently protected by TMR (for example, vote/call results).
- `Pink` is a transient state used during staged rebuilding of replicas via smove builtins.

### 3.2 Instruction-level well-coloredness rules

The core judgment is `wc_instruction` (parameterized by liveness map and coloring function).

Important cases:

- `wc_Iop_safe`: for unprotected operations, arguments must be in one basic lane, and result stays in that lane.
- `wc_Iop_protected`: for protected ops, arguments are `White` and result is `White`.
- `wc_Iload`, `wc_Istore`, `wc_Icall`, `wc_Itailcall`, generic `wc_Ibuiltin`: arguments/results constrained through `White`.
- `wc_Ibuiltin_vote`: vote arguments must be exactly `(Red, Green, Blue)`, result becomes `White`.
- `wc_Ibuiltin_smove_green` and `wc_Ibuiltin_smove_blue`: enforce `White -> Pink -> Red` on the main copy while creating `Green`/`Blue` shadows.

Crucially, almost every rule also has a `Regset.For_all` side condition that preserves colors of unaffected live registers across successor edges.

That preservation condition is essential for simulation invariants; it is not cosmetic.

### 3.3 Function and program well-coloredness

- `wc_function col f` requires successful liveness analysis and `wc_instruction` for all instructions.
- `wc_program p` requires each internal function to have some coloring satisfying `wc_function`.

The executable checker in `RTLcolorcheck.v` computes:

- `check_function`: run liveness, infer a coloring (`infer_coloring`), then verify constraints.
- `check_program`: all internal functions pass.
- `check_program_sound`: `check_program p = true -> wc_program p`.

`infer_coloring` is unverified, but that is acceptable: only checker soundness is relied on, so bad inferred colorings are rejected.

## 4. Faulty simulation theorem in RTLtolerant

### 4.1 Statement

Inside section `TOLERANCE` with hypothesis `WC_prog : wc_program prog`:

`faulty_backward_simulation :
  backward_simulation (RTL3.semantics prog) (faulty_semantics prog)`.

Source semantics:

- Non-faulty RTL with 3-voting (`RTL3`)

Target semantics:

- Faulty RTL with 2-voting (`faulty_semantics`)

Interpretation:

- For every faulty behavior `behF`, there exists a non-faulty 3-vote behavior `beh3`
  such that `behavior_improves beh3 behF`.
- Equivalently: the faulty semantics refines the non-faulty 3-vote semantics
  (target refines source for `backward_simulation source target`).

### 4.2 Match relation design

The proof uses `match_states` with a boolean index tracking fault status.

### Register relation (`match_rs`)

- If not faulted: all registers satisfy `Val.lessdef` pointwise.
- If faulted: there exists one basic color `c` such that all live registers whose color is not `c` satisfy `Val.lessdef`.

This exactly formalizes "after one fault, at most one lane may be compromised."

### Stackframes and memory

- Stackframes carry analogous `match_rs_upto` constraints.
- `rs_compat` (via `val_compat`) is also tracked to reason about non-protected computations under zaps.
- Memory relation is `Mem.extends`.

### 4.3 Why `Val.lessdef` is used

The relation cannot be equality in general because 3-vote is stricter than 2-vote:

- 2-vote can return a defined value in cases where 3-vote returns `Vundef`.
- Therefore source (RTL3) may be less defined than target (faulty RTL2) and `lessdef` is the right abstraction.

### 4.4 Proof skeleton

Main components:

1. `step_simulation`: simulate one non-faulty RTL2 step by one RTL3 step while preserving match relation.
2. `maybe_zap_preserves_match_states`: if a zap occurs, transition to the "one bad color" post-fault invariant.
3. `faulty_simulation`: combine target faulty step with source step simulation.
4. `faulty_progress`: required progress condition for CompCert backward simulation framework.
5. `fault_order` on booleans (`true < false`) and well-foundedness proof.

Then `Backward_simulation` is instantiated with these obligations.

## 5. Why color-based separation is exactly what the faulty simulation needs

The nontrivial part of the simulation is preserving the post-fault invariant across all instructions.

The color system provides exactly the needed facts:

- Lane discipline: replicas remain separated in R/G/B except at designated merge/rebuild points.
- Controlled crossings: vote and smove rules are explicit and typed.
- Successor consistency: unaffected live registers keep their colors, enabling transport of invariants across CFG edges.

Operationally in the proof:

- Many instruction cases invert `wc_instruction` hypotheses to recover these constraints.
- Liveness lemmas show required registers are in transfer/live sets.
- The proof repeatedly uses these facts to show either:
  - a register remains less-defined, or
  - it belongs to the single potentially-corrupted color lane.

Without those color constraints, the "only one lane can diverge" invariant would not be stable.

## 6. Composition into the overall fault tolerance theorem

`driver/Complements.v` proves:

`transf_c_program_to_rtl_preservation_faulty`

which composes three backward-simulation/refinement links:

1. `faulty(tp) -> RTL3(tp)` via `faulty_backward_simulation` (requires well-coloredness from checker soundness).
2. `RTL3(tp) -> RTL(tp)` via `rtl_rtl3_backward_simulation` from `RTLagreement.v`.
3. `RTL(tp) -> C(p)` via standard CompCert correctness for the truncated pipeline.

Then `behavior_improves_trans` composes the three improvements.

This corresponds to the story in `doc/fault_tolerance.md`:

- Agreement bridge handles 2-vote vs 3-vote semantics.
- Separation bridge (well-coloredness + tolerant simulation) handles faults.

## 7. Practical summary

- The color checker is the mechanized certificate of separation.
- `RTLtolerant.v` is the theorem that consumes that certificate to prove fault robustness under the single-fault RTL model.
- `Complements.v` combines this with existing CompCert simulation machinery to get an end-to-end C-to-RTL fault-tolerance preservation result.
