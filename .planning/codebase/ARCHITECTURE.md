# Architecture

**Analysis Date:** 2026-03-03

## Pattern Overview

**Overall:** Multi-stage compiler with formal verification in Coq, extraction to OCaml, and fault tolerance via Triple Modular Redundancy (TMR).

**Key Characteristics:**
- Multi-pass compilation from C to x86-64 assembly through 13+ intermediate languages
- Each compiler pass has a corresponding proof file establishing semantic preservation via forward/backward simulation
- Fault tolerance modeled at the RTL (Register Transfer Language) level using color-based register separation
- Vote-parameterized semantics: each intermediate language supports both Two-voting and Three-voting modes for DMR/TMR
- Proven under single-fault model where individual register values can be corrupted at specific program points

## Layers

**C Frontend (Coq):**
- Purpose: Parse and type-check C source, transform to Clight
- Location: `cfrontend/` (Csyntax, Clight, Cshmgen, Cminor)
- Contains: C AST definitions, semantic rules for expressions/statements, type checking
- Depends on: `common/` (AST, Values, Memory, Events), `lib/` (utilities)
- Used by: Backend passes after simplification

**Intermediate Language Definitions (Coq):**
- Purpose: Define abstract syntax and small-step semantics for each compilation stage
- Locations:
  - `cfrontend/`: Csyntax, Clight, Csharpminor
  - `backend/`: Cminor, CminorSel, RTL, LTL, Linear, Mach, Asm
- Contains: `Inductive instruction`, `type state`, `Inductive step` relations
- Pattern: Each language `L.v` defines syntax and semantics; `Lproof.v` proves preservation
- Depends on: `common/` (AST, Values, Memory, Smallstep, Globalenvs), architecture-specific files (Op, Machregs, Conventions)

**Compiler Passes (Coq + OCaml):**
- Purpose: Transform between intermediate languages, apply optimizations, allocate registers
- Locations:
  - Coq specs: `cfrontend/SimplExpr.v`, `backend/Selection.v`, `backend/RTLgen.v`, `backend/Allocation.v`, etc.
  - Proofs: Corresponding `*proof.v` files
  - OCaml extraction: Parser (`cparser/Parser.vy`, `cparser/Lexer.mll`), colorizer (`backend/RTLinfercolor.ml`)
- Contains: Monadic transformations using `res` (Result) type, error handling via `Errors.v`
- Depends on: Language definitions, dominator/liveness analysis (Kildall.v)
- Used by: Pipeline orchestrator (Compiler.v)

**Fault Tolerance Extension (Coq):**
- Purpose: Model single-fault semantics, define color system, prove fault tolerance
- Core files:
  - `backend/RTLfault.v` - Defines `fstate` (state + fault bit), `maybe_zap` relation (fault injection model)
  - `backend/RTLcolor.v` - Color datatype (Red/Green/Blue/White/Pink), well-coloredness predicates
  - `backend/RTLcolorcheck.v` - Boolean checker `check_program`, axiom for unverified oracle `infer_coloring`
  - `backend/RTLdmr.v`/`backend/RTLtmr.v` - DMR/TMR replication passes (shadow registers, check instructions)
  - `backend/RTLtolerant.v` - Backward simulation proving 3-voting faulty RTL >= 2-voting non-faulty RTL
  - `backend/Novotes.v` - Ensures programs don't use voting builtins before TMR insertion
  - `backend/Builtins2.v` - Vote builtin definitions, `VoteSemantics` typeclass, `vote_type` (Two/Three)
- Contains: Register coloring predicates, replicate builtin instructions, match relations for backward sim
- Depends on: RTL semantics, fault model definitions
- Used by: Main theorem in `driver/Complements.v`

**Architecture-Specific Code:**
- Purpose: Define target-specific operations, calling conventions, code generation
- Locations: `x86/`, `x86_64/`, `arm/`, `aarch64/`, `powerpc/`, `riscV/`
- Contains: `Op.v` (operations), `Machregs.v` (machine registers), `Asmgen.v` (assembly generation), `Conventions*.v` (ABI)
- Used by: Backend passes for final code generation

**OCaml Extraction and Driver:**
- Purpose: Extract verified Coq definitions to OCaml, implement unverified oracles, run compiler binary
- Locations:
  - `extraction/extraction.v` - Directs Coq extraction, wires `RTLinfercolor.infer_coloring` to axiom
  - `driver/Driver.ml` - Main entry point, calls color checker on intermediate RTL
  - `backend/RTLinfercolor.ml` - Unverified union-find based color inference
- Depends on: All proven Coq modules, C parser (MenhirLib-based)
- Used by: Final `ccomp` compiler binary

**Common Infrastructure (Coq):**
- Purpose: Shared definitions used across all languages
- Location: `common/`
- Contains: AST (abstract syntax tree base), Values, Memory (memory model), Events (observable behaviors), Smallstep (step relations), Globalenvs (global environment), Linking (separate compilation)
- Utilities: `lib/` provides Maps, Integers, Floats, CoqLib

## Data Flow

**Compilation Pipeline:**

```
C source code
    ↓ [parse via cparser/Parser, Lexer in OCaml]
Csyntax (parsed C AST)
    ↓ [SimplExpr.transl_program]
Clight (C with simplified expressions)
    ↓ [SimplLocals, Cshmgen]
Csharpminor / Cminor
    ↓ [Selection.sel_program]
CminorSel (instruction selection)
    ↓ [RTLgen.transl_program]
RTL (Register Transfer Language, control flow graph)
    ↓ [Tailcall, Inlining, Renumber, Constprop, CSE, Deadcode, Unusedglob]
RTL (optimized)
    ↓ [Novotes.transf_program - verify no votes]
RTL (novotes-checked)
    ↓ [DMR/TMR insertion (optional, conditional)]
RTL (with redundancy)
    ↓ [Allocation - register allocation]
LTL (Linear Transfer Language)
    ↓ [Linearize]
Linear (list of instructions)
    ↓ [Stacking - stack frame layout]
Mach (machine code)
    ↓ [Asmgen]
Asm (x86-64 assembly)
    ↓ [extract to OCaml, print to .s file]
x86-64 assembly output
```

**Fault Tolerance Path (when -tmr or -dmr flag used):**

1. RTL program reaches Novotes checker - ensures no pre-existing vote instructions
2. RTLtmr.transf_program / RTLdmr.transf_program runs:
   - Reserve shadow registers for each original register
   - Copy parameters to shadows at function entry
   - For each Iop/Iload: emit shadow copy
   - For other instructions: emit check before execution, copy result to shadow after
3. Result: 3-voting RTL (or 2-voting for DMR)
4. Color inference oracle assigns colors:
   - Red/Green/Blue: basic colors (protected during voting)
   - White/Pink: temporary (reset after use)
5. RTLcolorcheck.check_program verifies coloring matches well-coloredness rules
6. RTLtolerant.backward_simulation proved: faulty (2-voting checked RTL) >= non-faulty (3-voting RTL)
7. Composition with earlier passes proves end-to-end: C >= faulty x86

**State Management:**

- RTL state: `State stk f sp pc rs m` - stack, function, stack pointer, program counter, registers, memory
- Faulty RTL state: `fstate` wraps RTL state with boolean fault flag
- Register state: `regset` (register file), updated by Iop/Iload instructions
- Coloring state: per-PC `color` assignment (Red/Green/Blue/White/Pink) per register
- Vote-parameterized: semantics takes `VT: vote_type` and `VoteSemantics VT` as type class parameters

## Key Abstractions

**Intermediate Language:**
- Purpose: Define syntax, semantics, type system for compilation stage
- Pattern: Pair of files - `L.v` (definitions) + `Lproof.v` (semantic preservation)
- Example: `RTL.v` defines `instruction`, `function`, `program`, `state`, `step` relation; `RTLgenproof.v` proves RTLgen produces code matching RTL semantics

**Simulation Relation:**
- Purpose: Relate states between two languages, prove correctness of transformation
- Types: Forward simulation (source can be simulated by target), Backward simulation (target implies source behavior)
- Example: `RTLgenproof.match_program p tp -> forward_simulation (CminorSel.semantics p) (RTL.semantics tp)`
- Used by: Linking framework to compose proofs

**Monadic Compiler Pass:**
- Purpose: Thread error handling through transformation
- Pattern: `A -> res B` using `@@@` (apply_partial) and `@@` (apply_total) operators
- Example: `transf_rtl_program : RTL.program -> res RTL.program` chains Tailcall, Inlining, Renumber, etc.

**VoteSemantics Typeclass:**
- Purpose: Abstract over 2-voting vs 3-voting semantics for TMR/DMR
- Pattern: Sections in language definitions parameterized by `VT: vote_type` and `vsem: VoteSemantics VT`
- Enables: Same code structure supports both modes; proofs parameterized over vote type

**Color System:**
- Purpose: Classify registers by protection level in fault-tolerant mode
- Datatype: `Red | Green | Blue | White | Pink`
- Rules: Red/Green/Blue stay constant; White/Pink reset after instructions
- Used by: Backward simulation to permit register corruption only in basic colors

**Replicate Builtin:**
- Purpose: Emit check/copy instructions for TMR/DMR
- Variants: `smove_int_green`, `check_int` (and long, float, single variants)
- Wired to: OCaml extraction and runtime support

## Entry Points

**Coq Compilation Entry:**
- Location: `driver/Compiler.v`
- Function: `transf_c_program : Csyntax.program -> res Asm.program`
- Responsibilities: Orchestrate all passes, chain monadic transformations, apply flags (dmr/tmr/optimization)
- Flow: Parses command-line options from `Compopts.v`, conditionally applies passes via `total_if`/`partial_if`

**OCaml Compilation Entry:**
- Location: `driver/Driver.ml`
- Function: `compile_c_file sourcename ifile ofile`
- Responsibilities:
  1. Parse C source via `cparser/Parser`, `cparser/Lexer`
  2. Extract to Coq AST (Csyntax)
  3. Call `Compiler.transf_c_program_to_rtl` to get RTL
  4. Check coloring via `RTLcolorcheck.check_program`
  5. Call `Compiler.transf_rtl_program''` to get assembly
  6. Print assembly to output file
- Flow: Handles debugging output (Clight, RTL, LTL, Mach dumps), timing, error reporting

**Main Theorem (Proof):**
- Location: `driver/Complements.v`
- Theorem: `transf_c_program_to_rtl_preservation_faulty` (implicit in main_theorem composition)
- Composition:
  1. C semantics >= 2-voting RTL (no faults) - StandardPass.backward_simulation
  2. 2-voting RTL >= 3-voting RTL - weak agreement (trivial from no_votes)
  3. 3-voting RTL >= 3-voting RTL+TMR - TMRpass.backward_simulation
  4. 3-voting RTL+TMR >= 2-voting faulty RTL+TMR - RTLtolerant.backward_simulation
  5. Composed: C >= faulty x86 via linking framework

## Error Handling

**Strategy:** Result monad (`res` type) threading errors through transformations with monadic operators.

**Patterns:**
- `OK v` - successful result
- `Error msg` - failure with error message
- `@@@` operator: `res A -> (A -> res B) -> res B` (partial composition)
- `@@` operator: `res A -> (A -> B) -> res B` (total composition)
- `partial_if flag transform` - conditionally apply fallible transformation
- `total_if flag transform` - conditionally apply total transformation

**Errors Checked:**
- RTL coloring failures - `infer_coloring` returns `None` if coloring impossible
- Register allocation failures - `Allocation.transf_program` may fail
- Linearization failures - `Linearize.transf_program` may fail on invalid CFG
- Code generation failures - `Asmgen.transf_program` may fail on unsupported operations

## Cross-Cutting Concerns

**Logging:**
- Method: `print_*` functions defined in `Compiler.v` (stubs in Coq, implemented in OCaml extraction)
- Usage: `@@ print print_RTL` embeds debugging output in pass chain
- Levels: print_Clight, print_Cminor, print_RTL (with pass number), print_LTL, print_Mach

**Validation:**
- Typing: `RTLtyping.wf_program` checks RTL program well-formedness
- Coloring: `RTLcolor.wc_function`, `RTLcolor.wc_program` validate color consistency
- Votes: `Novotes.transf_program` ensures no voting instructions before TMR

**Memory Model:**
- Used by: All intermediate languages
- Semantics: `Memory.Mem` abstract type with `load`, `store`, `extends` relation
- Reasoning: Backward simulation uses `Memory.Mem.extends` to relate non-faulty and faulty executions

**Calling Conventions:**
- Location: `backend/Conventions.v` (architecture-independent), `x86_64/Conventions1.v` (arch-specific)
- Used by: RTL semantics (parameter passing), Allocation (register assignment), Stacking (ABI compliance)

---

*Architecture analysis: 2026-03-03*
