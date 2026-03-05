# Architecture

**Analysis Date:** 2026-03-04

## Pattern Overview

**Overall:** CompCert is a formally verified C compiler with **layered multi-pass architecture** extended with fault tolerance via **Triple Modular Redundancy (TMR)** and **Dual Modular Redundancy (DMR)** at the RTL intermediate level. Each compilation pass is proven to preserve semantics via forward or backward simulation, composing into a single end-to-end correctness theorem.

**Key Characteristics:**
- Multi-language intermediate representation: 10+ intermediate languages from C syntax down to assembly
- Control Flow Graph (CFG) representation at RTL and below (programs are finite maps from nodes to instructions)
- Monadic composition of partial and total transformations using Result monad (`res` type)
- Proof-per-pass strategy: each transformation pass `Foo.v` has corresponding proof `Fooproof.v`
- Fault tolerance achieved through color-based register separation at RTL level with majority voting

## Layers

**Frontend (C Language Analysis):**
- Purpose: Parse, elaborate, and type-check C source code
- Location: `cfrontend/`, `cparser/`
- Contains: C syntax trees (`Csyntax.v`), semantics (`Csem.v`), simplified Clight language
- Depends on: Common library utilities, AST definitions
- Used by: Middle-end transformations

**Middle-end (IR Optimization):**
- Purpose: Language-independent optimizations (inlining, constant propagation, dead code elimination, CSE)
- Location: `backend/` (passes like `Tailcall.v`, `Inlining.v`, `Constprop.v`, `CSE.v`, `Deadcode.v`)
- Contains: RTL-level optimizations, liveness analysis (`Liveness.v`), value analysis (`ValueDomain.v`)
- Depends on: RTL language definition, optimality algorithms (Kildall fixed point)
- Used by: Register allocation and code generation phases

**Fault Tolerance (TMR/DMR Insertion):**
- Purpose: Insert redundancy at RTL level with color-based register separation
- Location: `backend/RTLtmr.v`, `backend/RTLdmr.v`, `backend/RTLcolor.v`, `backend/RTLcolorcheck.v`, `backend/RTLinfercolor.ml`
- Contains: Replication instruction generation, color inference oracle, verification checker
- Depends on: RTL language, liveness information, builtin definitions (`Builtins2.v`)
- Used by: Post-optimization phase before register allocation

**Backend (Code Generation):**
- Purpose: Lower RTL to target machine code (allocation, linearization, stack layout, final assembly)
- Location: `backend/` (passes: `Allocation.v`, `Linearize.v`, `Stacking.v`), `x86/` (or `arm/`, `aarch64/`, etc.)
- Contains: Register allocator, instruction linearizer, stack frame builder, target-specific code generation
- Depends on: RTL, LTL, Linear, Mach, Asm languages; machine-specific definitions
- Used by: Final assembly output

**Verification Framework (Common):**
- Purpose: Provide semantic frameworks, simulation relations, and proof utilities
- Location: `common/`, `lib/`
- Contains: AST node types, value semantics, memory model, linking, small-step semantics, behaviors
- Depends on: Coq standard library, Coqlib utilities
- Used by: All language definitions and proof modules

## Data Flow

**Full C to Assembly Pipeline:**

1. **Parsing & Elaboration** (`cparser/` → `Csyntax.program`)
   - OCaml Menhir parser produces Cabs (C abstract syntax)
   - Elaboration (`Elab.ml`) produces `Csyntax.program` with full type annotations

2. **Simplification** (`SimplExpr.transl_program` → `Clight.program`)
   - Flatten complex expressions into pure expressions
   - Result: `Clight` (simplified C with only statements)

3. **C Frontend** (`SimplLocals.v`, `Cshmgen.v`, `Cminorgen.v` → `Cminor.program`)
   - Eliminate stack-allocated variables via expansion
   - Lower to Csharpminor (C# minor - closer to machine)
   - Lower to Cminor (even simpler IR)

4. **Instruction Selection** (`Selection.sel_program` → `CminorSel.program`)
   - Map Cminor operations to target-specific instruction operations
   - Architecture-dependent (`x86/SelectOp.v`, etc.)

5. **RTL Generation** (`RTLgen.transl_program` → `RTL.program`)
   - Flatten expression trees into register transfer code
   - Introduce virtual registers and explicit control flow
   - Build explicit control flow graphs

6. **RTL Optimizations** (`transf_rtl_program` pipeline):
   - Tail call identification → Tailcall pass
   - Function inlining analysis → Inlining pass
   - Renumber node IDs → Renumber pass
   - Constant propagation → Constprop pass
   - Global value numbering → CSE pass
   - Dead code elimination → Deadcode pass
   - Remove unused global symbols → Unusedglob pass
   - Verify no vote builtins present → Novotes pass

7. **Fault Tolerance Insertion** (DMR/TMR optional):
   - **DMR**: Duplicate each register, emit comparison checks before non-idempotent ops
   - **TMR**: Triplicate each register, use majority voting before non-idempotent ops
   - Color inference oracle assigns Red (primary), Green/Blue (shadows), White/Pink (temporary)
   - Verified checker (`RTLcolorcheck.check_program`) verifies register separation

8. **Register Allocation** (`Allocation.transf_program` → `LTL.program`)
   - Assign virtual registers to physical machine registers
   - Build register interference graph
   - Perform coloring (different from TMR colors - this is hardware register coloring)

9. **CFG Linearization** (`Linearize.transf_program` → `Linear.program`)
   - Convert CFG representation to linear instruction sequence
   - Maintain control flow via jumps and branches

10. **Stacking** (`Stacking.transf_program` → `Mach.program`)
    - Build stack frame layout (parameters, local variables, spill slots)
    - Insert prologue/epilogue code

11. **Assembly Generation** (`Asmgen.transf_program` → `Asm.program`)
    - Generate target-specific assembly instructions
    - Machine-specific (x86-64, ARM, RISC-V, etc.)

**State Management:**

- **Immutable Program State**: Programs flow through passes as values, each pass produces new program value
- **Local Compilation State**: Within passes (e.g., `RTLgen`), state monad (`res` result type) tracks:
  - Generated code (map of nodes to instructions)
  - Fresh node counter (for generating unique node IDs)
  - Error messages if transformation fails
- **Control Flow Graph**: RTL and below use explicit CFG: `fn_code : PTree.t instruction` (map from node → instruction)

## Key Abstractions

**Instruction (RTL level):**
- Purpose: Represent register transfer operations
- Examples: `Iop` (arithmetic), `Iload` (memory read), `Istore` (memory write), `Icall` (function call), `Ibuiltin` (intrinsics/votes), `Icond` (conditional branch)
- Pattern: Each instruction explicitly lists successor nodes, enabling static CFG construction

**Function Definition:**
- Purpose: Container for code and metadata
- Pattern: Functions are opaque at top level but contain detailed RTL/Asm code; separate compilation handled via linking (`common/Linking.v`)

**Simulation Relation:**
- Purpose: Formalize "program A is at least as good as program B"
- Pattern: Forward simulation (A executes, B can match) vs backward simulation (B executes, A could match); composed into end-to-end theorem
- Examples: `RTLgenproof.v` proves `RTL semantics >= CminorSel semantics`, `RTLtolerantproof.v` proves TMR program survives single-bit faults

**Vote Builtin:**
- Purpose: Represent majority voting, agreement checking, and result movement in TMR/DMR
- Pattern: Verified builtins (`__builtin_vote_int`, `__builtin_smove_int_green`, `__builtin_check_int`, etc.) called as `Ibuiltin` instructions
- Semantics: Defined in `Builtins2.VoteSemantics` typeclass (parameterized by vote_type: Two/Three for DMR/TMR)

**Color (Fault Tolerance):**
- Purpose: Assign registers to redundancy domains for TMR/DMR
- Pattern: Per-program-point coloring `node -> reg -> color` where color ∈ {Red, Green, Blue, White, Pink}
  - Red: primary computation
  - Green, Blue: replicated shadows
  - White, Pink: temporary colors for intermediate results
- Examples: `RTLcolor.v` defines color type and properties, `RTLcolorcheck.v` verifies well-coloredness

**Liveness Analysis:**
- Purpose: Determine which registers are live at each CFG node
- Pattern: Forward dataflow analysis via Kildall algorithm; result is `PMap.t Regset.t` (map from node to set of live registers)
- Used by: Register allocation, TMR coloring, dead code elimination

## Entry Points

**Coq Verification Layer:**
- Location: `driver/Compiler.v`
- Triggers: Loaded by proof files to compose semantic preservation proofs
- Responsibilities:
  - Define `transf_c_program`: C source → Asm via full pipeline
  - Define `transf_c_program_to_rtl`: C source → RTL (for fault tolerance analysis)
  - Define `transf_rtl_program'`: RTL → Asm after optional DMR/TMR
  - Compose individual pass proofs into end-to-end theorems

**OCaml Execution Layer:**
- Location: `driver/Driver.ml`
- Triggers: Invoked by `ccomp` binary when user runs `./ccomp test.c -o test`
- Responsibilities:
  - Parse C source via `cparser/Parser.mly` and `Elab.ml`
  - Run `Compiler.transf_c_program_to_rtl` to get RTL
  - Verify RTL is well-colored via `RTLcolorcheck.check_program` (calls oracle `RTLinfercolor.infer_coloring`)
  - If `-dmr` or `-tmr` flags: apply DMR/TMR replication
  - Generate final assembly via `Compiler.transf_rtl_program''`
  - Output assembly file

**Color Inference Oracle:**
- Location: `backend/RTLinfercolor.ml`
- Triggers: Called from `Driver.ml` post-RTL-generation to infer coloring
- Responsibilities:
  - Use union-find data structure to partition registers into equivalence classes
  - Assign colors respecting liveness constraints (live-out register separation)
  - Return `option (node -> reg -> color)` (None if coloring impossible)

## Error Handling

**Strategy:** Result monad throughout (`res A = Error string | OK A`)

**Patterns:**
- **Composition**: `@@@` operator chains partial computations; any Error propagates
- **Fallback**: Some passes are conditional (`partial_if` flag checks), skip if flag false
- **Reporting**: Failed transformation includes error message (e.g., "register allocation failed")
- **Checking**: Color verification (`RTLcolorcheck.check_program`) returns boolean; failures reported to user

**Example (Driver.ml):**
```ocaml
let rtl = match Compiler.transf_c_program_to_rtl csyntax with
  | Errors.OK rtl -> rtl
  | Errors.Error msg -> fatal_error loc "%a" print_error msg
```

## Cross-Cutting Concerns

**Logging:**
- Approach: `time` operator in `Compiler.v` wraps passes (no-op in extracted code, tracked by OCaml `Timing` module)
- Optional IR dumps: `print_RTL`, `print_LTL`, `print_Mach` procedures called conditionally based on flags

**Validation:**
- Color checking: `RTLcolorcheck.check_program` verifies well-coloredness before proceeding to code generation
- Vote-free checking: `Novotes.transf_program` ensures source RTL contains no vote builtins (error if present)
- Type checking: Present in frontend (`cfrontend/Ctyping.v`), not runtime

**Authentication (Linking):**
- Approach: `TransfLink` typeclass ensures passes preserve separate compilation property
- Semantics preserved under arbitrary linking with external code via `Linking.v`

**Fault Model:**
- Single-bit fault assumption: `RTLfault.v` defines faulty semantics where one register can be "zapped" (corrupted) at most once per instruction
- Protection: Only non-protected operations (`RTLfault.zap_allowed`) can trigger faults; memory ops and calls are protected
- Recovery: Well-colored TMR program provides backward simulation showing 3-voting >= 2-voting under fault

---

*Architecture analysis: 2026-03-04*
