# Plan: Fault Tolerance at RISC-V Asm Level

## Goal
Prove an asm-level analogue of `transf_c_program_to_rtl_preservation_faulty`:

- input: CompCert C program `p`
- output: RISC-V asm `tp` from full `transf_c_program`
- assumptions: asm color checker accepts `tp`
- guarantee: behaviors of faulty asm semantics of `tp` are refined by behaviors of source C semantics

Concretely, add a theorem in `driver/Complements.v` of the form:

```coq
forall p tp beh,
  transf_c_program p = OK tp ->
  RiscvAsmColorcheck.check_program tp = true ->
  program_behaves (RiscvAsmfault.faulty_semantics tp) beh ->
  exists beh', program_behaves (Csem.semantics p) beh' /\ behavior_improves beh' beh.
```

## Key decisions
1. **Fault model**: start with the RTL-style single-fault model (one zap globally) for fastest proof reuse; keep a clean extension point for per-activation budgets (as sketched in `doc/paper.pdf`).
2. **Color domain**: color both machine registers and stack locations (not registers only), otherwise spills/coalescing can break separation undetected.
3. **Checker granularity**: per-function checker over asm code before `Asmexpand` (matches Coq `Asm.semantics` used in proofs).
4. **Semantics strategy**: keep existing backend semantics unparameterized (core/2-vote), introduce strict-3 only where needed (`RTL3`, `Asm3`) plus explicit `3 -> 2` bridge lemmas.
5. **Liveness optimization**: implement liveness-bounded sparse inference from the start. Registers are finite, but stack locations are not a small fixed set; dense `pc x location` tables can still become quadratic.

## Phase 0: Preflight on RISC-V backend
### Why
Current tree is configured for `ARCH=x86`; RISC-V proof files are not currently in the active Coq include path.

### Actions
1. Build in a RISC-V configuration branch (`./configure ... riscv64-linux`) and identify missing fault-tolerance modules.
2. Add `riscV/Asm3.v` (strict-3 asm semantics over existing asm syntax, analogous to `backend/RTL3.v`) using `external_call3`.
3. Prove baseline bridge lemmas for `Asm3`:
   - receptiveness/determinacy counterparts needed by simulation combinators
   - `Asm3_to_Asm2` behavior-improves lemma (`program_behaves Asm3 -> exists beh2, program_behaves Asm2 beh2 /\ behavior_improves beh2 beh3`)
4. Keep `riscV/Asmagreement.v` optional; it is not on the critical path for the new composition shape.

### Exit criteria
- `make` succeeds in RISC-V config before new asm-fault modules are introduced.

## Phase 1: Asm location model + CFG/liveness infrastructure
### New files (RISC-V)
- `riscV/AsmLoc.v` (or equivalent): abstract colorable locations
- `riscV/AsmLiveness.v` (proof-oriented liveness over locations)

### Actions
1. Define colorable location type:
   - machine regs (`preg` subset used by generated code)
   - abstract stack cells (frame-relative offsets/chunks)
2. Define per-instruction `uses/defs` and successor relation for asm code positions.
3. Build backward dataflow liveness (Kildall) over locations.
4. Prove solution lemmas analogous to `ProofLiveness.analyze_solution` used by tolerant proofs.

### Notes
- Keep the analysis conservative (proof-friendly) rather than DCE-friendly.
- Treat calls/returns explicitly so live-through-call stack cells are modeled soundly.

## Phase 2: Declarative RISC-V asm color system + checker soundness
### New files
- `riscV/Asmcolor.v`
- `riscV/Asmcolorcheck.v`

### Actions
1. Port RTL color ideas to asm instruction families:
   - arithmetic/logical ops
   - loads/stores to stack/global
   - branches/jumps/calls/returns
   - vote/smove builtins
2. State `wc_instruction`, `wc_function`, `wc_program` over asm + location liveness.
3. Implement boolean checker and prove soundness:
   - `check_program_sound : check_program p = true -> wc_program p`

### Design constraints
- Enforce color-preservation on live locations across successors.
- Enforce separation discipline for stack moves and spill/reload patterns.

## Phase 3: Unverified inference oracle (translation validation path)
### New files
- `riscV/Asminfercolor.ml`

### Actions
1. Implement union-find constraint solving like `backend/RTLinfercolor.ml`.
2. Use sparse per-program-point maps keyed by only live locations.
3. Expose oracle to Coq checker as an axiom parameter (same trust model as RTL checker).

### Integration
- Add extraction wiring in `extraction/extraction.v`:
  - `Extract Constant RiscvAsmColorcheck.infer_coloring => "Asminfercolor.infer_coloring"`.

## Phase 4: Faulty RISC-V asm semantics
### New file
- `riscV/Asmfault.v`

### Actions
1. Define faulty state wrapper and `maybe_zap` relation for asm states.
2. Define `zap_allowed`/destination extraction per instruction family.
3. Define `faulty_semantics` and prove basic lemmas (initial/final, determinacy-related helpers as needed).

### Recommended scope for first theorem
- Faults affect destination register values only.
- Exclude control-flow critical writes (`PC`, `RA`, `SP`) and vote/smove builtins.

## Phase 5: Faulty backward simulation at asm level
### New file
- `riscV/Asmtolerant.v`

### Actions
1. Define match relation between strict-3 non-faulty asm and core/2-voting faulty asm:
   - lessdef-style relation over live colored locations
   - memory relation (`Mem.extends`) plus stack-cell coherence lemmas
2. Prove step simulation with stuttering as needed.
3. Prove main theorem:

```coq
Theorem faulty_backward_simulation :
  wc_program prog ->
  backward_simulation
    (Asm3.semantics prog)
    (faulty_semantics prog).
```

### Practical advice
- Follow structure of `backend/RTLtolerant.v` closely.
- Build a dense helper-lemma layer first (uses/defs/liveness membership), then main simulation.

## Phase 6: Compose end-to-end theorem in `driver/Complements.v`
### Actions
1. Reuse existing compiler-correctness chain to asm core semantics (`C2 >= Asm2`) from `transf_c_program`.
2. Use `Asm3_to_Asm2` bridge (`Asm3 -> Asm2`) proved in Phase 0.
3. Use asm tolerant theorem (`faulty2 -> Asm3`) from Phase 5.
4. Compose refinements in theorem-direction form:
   - `faulty_asm2 behF -> exists beh3, program_behaves Asm3 beh3 /\ behavior_improves beh3 behF`
   - `program_behaves Asm3 beh3 -> exists beh2, program_behaves Asm2 beh2 /\ behavior_improves beh2 beh3`
   - `program_behaves Asm2 beh2 -> exists behC, program_behaves Csem behC /\ behavior_improves behC beh2`
5. Conclude by transitivity of `behavior_improves`:
   - `exists behC, program_behaves Csem behC /\ behavior_improves behC behF`.
6. Add final theorem `transf_c_program_preservation_faulty_asm`.

## Why `novotes` is not needed in this composition
The previous RTL proof shape used a `2 -> 3` bridge (weak agreement), which requires `no_votes`.

This asm plan avoids `2 -> 3` entirely. We only need `3 -> 2` bridges:

1. `faulty_asm2 -> Asm3` (from tolerant backward simulation).
2. `Asm3 -> Asm2` (strict vote to core vote).
3. `Asm2 -> C2` (existing compiler correctness, read backward as behavior-improves).

`Asm3 -> Asm2` does not require `novotes`:
- non-vote externals are identical in `external_call3` and `external_call`
- vote builtins satisfy `vote3 <= vote` (lessdef)
- therefore each strict-3 step is matched by a core step with related results
- behavior-level refinement follows by standard simulation lifting.

## Phase 7: Driver and extraction integration
### Files
- `driver/Driver.ml`
- `extraction/extraction.v`

### Actions
1. Run asm checker in driver on pre-`Asmexpand` asm program.
2. Keep RTL checker temporarily behind a flag during migration; default to asm checker for RISC-V target.
3. Extract asm checker/oracle modules.

## Liveness optimization decision
Use liveness-bounded sparse inference from the first asm version.

Reasoning:
1. Register count is small, but stack locations can be large per function after spilling.
2. A dense `pc x location` table can still be near-quadratic in large functions.
3. You already paid the proof engineering cost once (`ProofLiveness` path); repeating dense-first then sparse-later at asm level will likely cost more total effort.

## Risks and mitigations
1. **Instruction-set proof volume is large**
   - Mitigation: prove per-family helper lemmas and keep checker/spec aligned structurally.
2. **Stack slot abstraction mismatch with actual addressing**
   - Mitigation: restrict first checker to stack accesses it can classify soundly; reject unsupported patterns conservatively.
3. **Drift between `Asm` and `Asm3` semantics definitions**
   - Mitigation: keep `Asm3` as a minimal fork of `Asm` with only `external_call` swapped to `external_call3`, and add parity lemmas early.
4. **Proof brittleness in `Complements.v` composition**
   - Mitigation: express composition with explicit theorem directions (`faulty2 -> Asm3 -> Asm2 -> C2`) and avoid mixed arrow shorthand.

## Validation checklist
1. `make check-admitted` passes.
2. New modules build in RISC-V config:
   - `riscV/Asmcolor.vo`
   - `riscV/Asmcolorcheck.vo`
   - `riscV/Asmfault.vo`
   - `riscV/Asmtolerant.vo`
   - `driver/Complements.vo`
3. Compiler path check:
   - compile sample with `-tmr`
   - asm checker runs and accepts expected outputs.
