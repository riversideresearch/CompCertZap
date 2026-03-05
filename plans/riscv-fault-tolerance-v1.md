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
4. **Liveness optimization**: implement liveness-bounded sparse inference from the start. Registers are finite, but stack locations are not a small fixed set; dense `pc x location` tables can still become quadratic.

## Phase 0: Preflight on RISC-V backend
### Why
Current tree is configured for `ARCH=x86`; RISC-V proof files are not currently in the active Coq include path.

### Actions
1. Build in a RISC-V configuration branch (`./configure ... riscv64-linux`) and identify missing fault-tolerance modules.
2. Ensure RISC-V backend is vote-semantic compatible (`Two`/`Three`) where needed for asm theorems.
3. Add `riscV/Asmagreement.v` (copy/adapt from `x86/Asmagreement.v`) so weak-agreement preservation is available on RISC-V builds too.

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
1. Define match relation between 3-voting non-faulty asm and 2-voting faulty asm:
   - lessdef-style relation over live colored locations
   - memory relation (`Mem.extends`) plus stack-cell coherence lemmas
2. Prove step simulation with stuttering as needed.
3. Prove main theorem:

```coq
Theorem faulty_backward_simulation :
  wc_program prog ->
  backward_simulation
    (@Asm.semantics Three VoteSemantics_Three prog)
    (faulty_semantics prog).
```

### Practical advice
- Follow structure of `backend/RTLtolerant.v` closely.
- Build a dense helper-lemma layer first (uses/defs/liveness membership), then main simulation.

## Phase 6: Compose end-to-end theorem in `driver/Complements.v`
### Actions
1. Add pipeline lemmas from C to asm under 3-voting (reuse existing pass proofs parameterized by vote semantics).
2. Reuse the current no-votes bridge (`2-voting -> 3-voting`) at RTL pre-TMR stage.
3. Compose refinements:
   - C (2-voting) >= RTL no-votes (2)
   - RTL no-votes (2) >= RTL no-votes (3)
   - RTL no-votes (3) >= final asm (3)
   - final asm (3) >= faulty asm (2) via `Asmtolerant`
4. Add final theorem `transf_c_program_preservation_faulty_asm`.

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
3. **Vote-semantics parameterization gaps in RISC-V files**
   - Mitigation: do parameterization cleanup in Phase 0 before tolerance proofs.
4. **Proof brittleness in `Complements.v` composition**
   - Mitigation: keep the same refinement decomposition style already used for RTL theorem.

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
