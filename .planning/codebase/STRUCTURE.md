# Codebase Structure

**Analysis Date:** 2026-03-03

## Directory Layout

```
compcert/
├── lib/                    # Utility library (Maps, Integers, etc.)
├── common/                 # Shared definitions (AST, Memory, Events, Linking)
├── cfrontend/              # C front-end (Csyntax, Clight, Cminor transformations)
├── backend/                # Intermediate language passes and optimizations
├── x86_64/                 # x86-64 architecture specifics (Op, Machregs, Asmgen)
├── x86/                    # x86-32 architecture specifics
├── arm/                    # ARM architecture specifics
├── aarch64/                # AArch64 architecture specifics
├── powerpc/                # PowerPC architecture specifics
├── riscV/                  # RISC-V architecture specifics
├── driver/                 # Main compiler pipeline (Compiler.v, Driver.ml)
├── cparser/                # C parser (Menhir-based, .vy/.mll files)
├── extraction/             # Coq extraction directives
├── runtime/                # Runtime support library (C code, arch-specific startup)
├── flocq/                  # Local copy of Flocq floating-point library
├── MenhirLib/              # Local copy of Menhir parser library
├── tools/                  # Utility scripts
├── test/                   # Test programs
├── doc/                    # Documentation
├── debug/                  # Debug information generation
├── import/                 # Import mechanism for separate compilation
├── export/                 # Export mechanism (CLightGen)
└── Makefile, _CoqProject   # Build configuration
```

## Directory Purposes

**lib/:**
- Purpose: General-purpose Coq utilities
- Contains: Maps (PTree, PMap, ZMap), Integers (Int, Int64, Ptrofs), Floats, CoqLib (common lemmas)
- Key files: `Maps.v`, `Integers.v`, `Floats.v`, `Decidableplus.v`, `Heaps.v`

**common/:**
- Purpose: Shared definitions used across all intermediate languages
- Contains: AST base types, Values, Memory model, Events (external interactions), Smallstep (step relations), Globalenvs (global environment), Linking (module linking), Builtins0 (basic builtins)
- Key files: `AST.v`, `Values.v`, `Memory.v`, `Events.v`, `Smallstep.v`, `Globalenvs.v`, `Linking.v`, `Switch.v`

**cfrontend/:**
- Purpose: C language front-end transformations
- Contains: Csyntax (parsed C AST), Clight (C with simplified expressions), Csharpminor, Cminor (low-level imperative)
- Transformations:
  - SimplExpr: Eliminate complex expressions, use temporaries
  - SimplLocals: Eliminate local variable declarations, allocate on stack
  - Cshmgen: Convert Clight to Csharpminor (inline statements)
  - Cminorgen: Convert Csharpminor to Cminor
- Proof files: `SimplExprproof.v`, `SimplLocalsproof.v`, `Cshmgenproof.v`, `Cminorgenproof.v`

**backend/:**
- Purpose: Low-level code generation and optimization
- Languages (ordered by pipeline):
  - Cminor: Imperative (input from cfrontend)
  - CminorSel: Instruction selection result
  - RTL: Register Transfer Language (control-flow graph)
  - LTL: Linear Transfer Language (linearized RTL)
  - Linear: List of instructions
  - Mach: Machine code (stack frame allocated)
  - Asm: Final assembly (x86 instructions)
- Optimization passes:
  - `Tailcall.v` - Eliminate tail calls → direct jumps
  - `Inlining.v` - Inline small functions
  - `Renumber.v` - Renumber nodes for canonical form
  - `Constprop.v` - Constant propagation
  - `CSE.v` - Common subexpression elimination
  - `Deadcode.v` - Eliminate dead code
  - `Unusedglob.v` - Eliminate unused globals
- Fault tolerance:
  - `RTLcolor.v` - Color system (Red/Green/Blue/White/Pink)
  - `RTLcolorcheck.v` - Color checker with oracle
  - `RTLdmr.v` - Dual modular redundancy insertion
  - `RTLtmr.v` - Triple modular redundancy insertion
  - `RTLfault.v` - Faulty semantics (fault injection model)
  - `RTLtolerant.v` - Backward simulation proving fault tolerance
  - `Novotes.v` - Verify no voting before TMR
  - `Builtins2.v` - Vote semantics and builtin definitions
- Analysis passes:
  - `Kildall.v` - Dominator/liveness analysis framework
  - `Liveness.v` - Liveness analysis for register allocation
  - `Registers.v` - Register file definition
  - `NeedDomain.v` - Register need analysis
- Supporting:
  - `RTLtyping.v` - Type checking for RTL
  - `Cminortyping.v` - Type checking for Cminor
  - `Conventions.v` - Calling conventions (arch-independent)
  - `Locations.v` - Register/stack slot locations
  - `Bounds.v` - Stack frame bounds checking
  - `ValueDomain.v` - Value abstraction for optimization

**x86_64/:**
- Purpose: x86-64 architecture specifics
- Contains:
  - `Op.v` - Operations available on x86-64
  - `Machregs.v` - Machine register definitions
  - `Conventions1.v` - x86-64 calling convention (AMD64 ABI)
  - `Asm.v` - x86-64 assembly syntax
  - `Asmgen.v` - Code generation from Mach to Asm
  - `Asmgenproof*.v` - Proofs of code generation
  - `SelectOp.v` - Instruction selection for operations
  - `CombineOp.v` - Combine commutative operations
  - `Stacklayout.v` - x86-64 stack frame layout
  - `Asmexpand.ml` - Built-in function expansion (unverified)
  - `TargetPrinter.ml` - Assembly pretty printer
- Equivalent structures in: `x86/`, `arm/`, `aarch64/`, `powerpc/`, `riscV/`

**driver/:**
- Purpose: Main compiler orchestration and command-line interface
- Coq files:
  - `Compiler.v` - Pipeline composition (chains passes via monadic operators)
  - `Complements.v` - Main theorems and linking
  - `Compopts.v` - Command-line option definitions
- OCaml files:
  - `Driver.ml` - Main entry point, integrates parsing, compilation, assembly, linking
  - `Clflags.ml` - Global command-line flags
  - `CommonOptions.ml` - Common option parsing
  - `Driveraux.ml` - Helper functions
  - `Frontend.ml` - C parsing and preprocessing
  - `Assembler.ml` - Invokes system assembler
  - `Linker.ml` - Invokes system linker
  - `Interp.ml` - Interpretation mode
  - `Timing.ml` - Timing utilities
  - `Configuration.ml` - Build configuration

**cparser/:**
- Purpose: C parser (Menhir-based)
- Contains:
  - `Parser.vy` - Menhir grammar file
  - `Lexer.mll` - OCamllex lexer definition
  - `Elab.ml` - Elaboration (semantic analysis)
  - `Cabs.v` - Parse tree AST
  - Tests: `cparser/tests/` - C parser test programs

**extraction/:**
- Purpose: Directs Coq code extraction to OCaml
- Contains: `extraction.v` - Specifies which definitions extract and how to handle axioms
- Axioms handled:
  - `RTLinfercolor.infer_coloring` - Wired to color inference oracle

**runtime/:**
- Purpose: Runtime support library (shared with compiled programs)
- C source files: `runtime/c/` - runtime functions
- Architecture-specific startup:
  - `runtime/x86_64/` - x86-64 startup code, exception handlers
  - `runtime/x86_32/`, `runtime/arm/`, `runtime/aarch64/`, etc.
- `runtime/include/` - Exported headers

**flocq/, MenhirLib/:**
- Purpose: Local copies of external libraries
- Flocq: Floating-point formalization
- MenhirLib: Parser combinator library
- Status: Included in-tree; can be replaced with system versions

**debug/:**
- Purpose: Debug information generation (DWARF)
- Contains: `Debug.ml`, `Dwarfgen.ml`, `DwarfPrinter.ml`, `DwarfUtil.ml`, `DebugInformation.ml`

**import/, export/:**
- Purpose: Separate compilation support
- Import: Load pre-compiled modules
- Export: Expose C interface (CLightGen)

## Key File Locations

**Entry Points:**

**Coq:**
- `driver/Compiler.v` - Lines 196-200: `transf_c_program` orchestrates C → Asm pipeline
- `driver/Compiler.v` - Lines 159-179: `transf_rtl_program` chain of RTL optimizations
- `driver/Complements.v` - Main theorem composition (backward simulation chain)

**OCaml:**
- `driver/Driver.ml` - Line 41: `compile_c_file sourcename ifile ofile` - main compilation function
- `driver/Driver.ml` - Line 56-62: Parse C and transform to RTL with coloring check
- `driver/Driver.ml` - Line 114-126: `process_c_file` - top-level C file handler

**Configuration:**
- `_CoqProject` - Defines Coq include paths (`-R lib compcert.lib`, etc.)
- `Makefile.config` - Build variables (ARCH, BITSIZE, etc.)
- `Makefile` - Main build orchestration
- `driver/Compopts.v` - Command-line option variables (dmr, tmr, optim_tailcalls, etc.)

**Core Logic:**

**Intermediate Languages:**
- C source → AST: `cparser/Parser.vy`, `cparser/Lexer.mll` → `cfrontend/Csyntax.v`
- Clight: `cfrontend/Clight.v` (lines 1-100 for syntax)
- Cminor: `backend/Cminor.v` (lines 1-100 for syntax)
- RTL: `backend/RTL.v` (lines 25-82 for instruction/function definition)
- LTL: `backend/LTL.v`
- Linear: `backend/Linear.v`
- Mach: `backend/Mach.v`
- Asm: `x86_64/Asm.v`

**Transformation Specifications:**
- Selection: `backend/Selection.v` - Instruction selection
- RTLgen: `backend/RTLgen.v` - Convert CminorSel → RTL
- Allocation: `backend/Allocation.v` - Register allocation (Cminor colors → machine registers)
- Linearize: `backend/Linearize.v` - Convert LTL → Linear
- Stacking: `backend/Stacking.v` - Allocate stack frame
- Asmgen: `x86_64/Asmgen.v` - Convert Mach → Asm

**Transformation Proofs:**
- `backend/Selectionproof.v` - Selection correctness
- `backend/RTLgenproof.v` - RTLgen correctness
- `backend/Allocproof.v` - Allocation correctness
- `backend/Linearizeproof.v` - Linearization correctness
- `backend/Stackingproof.v` - Stacking correctness
- `x86_64/Asmgenproof*.v` - Code generation correctness

**Fault Tolerance:**
- Color definition: `backend/RTLcolor.v` - Line 28-34: color datatype
- Color inference oracle: `backend/RTLinfercolor.ml` - Union-find implementation
- Coloring checker: `backend/RTLcolorcheck.v` - Line 73: Parameter infer_coloring axiom
- Faulty semantics: `backend/RTLfault.v` - Line 17-83: maybe_zap fault model
- Backward simulation: `backend/RTLtolerant.v` - Line 93-117: match_states relations
- DMR insertion: `backend/RTLdmr.v` - Shadow register replication
- TMR insertion: `backend/RTLtmr.v` - 3-way replication
- Vote builtins: `backend/Builtins2.v` - Line 13: VoteSemantics typeclass

**Testing:**
- `runtime/test/` - Test programs
- `test/` - Additional test cases

## Naming Conventions

**Files:**

**Coq files:**
- Language definitions: Uppercase, single word (e.g., `RTL.v`, `Cminor.v`, `Asm.v`)
- Transformation specs: Uppercase without suffix (e.g., `Selection.v`, `Allocation.v`, `Asmgen.v`)
- Proof files: `*proof.v` suffix (e.g., `Selectionproof.v`, `RTLgenproof.v`)
- Specification files: `*spec.v` suffix (e.g., `RTLgenspec.v`, `RTLdmrspec.v`)
- Analysis/library: Uppercase (e.g., `Kildall.v`, `Liveness.v`, `Maps.v`)
- Fault tolerance: Prefixed with `RTL` (e.g., `RTLfault.v`, `RTLcolor.v`, `RTLtolerant.v`)
- Backup files: Suffixed with `_backup.v` or `_backup2.v` (old iterations, ignored)

**OCaml files:**
- Extracted code: Generated from Coq, not hand-edited
- Implementation: Lowercase with underscores (e.g., `driver_aux.ml` → `Driveraux.ml`), PascalCase modules
- Parser files: `Parser.vy` (Menhir), `Lexer.mll` (OCamllex)
- Architecture modules: Arch-prefixed or in arch directory (e.g., `x86_64/TargetPrinter.ml`, `x86_64/Asmexpand.ml`)

**Directories:**
- Intermediate languages by level: `cfrontend/` (high-level), `backend/` (low-level)
- Architecture-specific: Lowercase arch names (e.g., `x86_64/`, `aarch64/`, `riscV/`)
- Library/utility: Lowercase generic names (e.g., `lib/`, `common/`, `runtime/`)

## Where to Add New Code

**New Intermediate Language or Pass:**
1. Define syntax and semantics: `backend/NewLang.v` (or `cfrontend/` if source-level)
2. Write transformation spec: `backend/NewTransform.v` (or name based on pass function)
3. Prove correctness: `backend/NewTransformproof.v`
4. Add to pipeline: Insert `Require NewTransform` and `Require NewTransformproof` in `driver/Compiler.v`
5. Chain into pipeline: Add line like `@@@ time "Description" NewTransform.transf_program` to `transf_rtl_program` or appropriate chain
6. Register in extraction: Add to `extraction/extraction.v` if needs OCaml extraction

**New Optimization:**
- If applied to RTL: Add to `transf_rtl_program` chain (lines 159-179 in `driver/Compiler.v`)
- If applied to Cminor: Add to `transf_cminor_program` chain (lines 181-186)
- Pattern: Create `Pass.v` with `transf_program : L.program -> res L.program`, then `Passproof.v`

**Fault Tolerance Enhancement:**
- Coloring rules: Extend `backend/RTLcolor.v` with new color predicates
- Replication logic: Modify `backend/RTLdmr.v` or `backend/RTLtmr.v` (shadow register generation)
- Backward simulation: Update `backend/RTLtolerant.v` (match_states, match_rs relations)
- Color checking: Extend `backend/RTLcolorcheck.v` (verify new color constraints)
- Color inference: Update `backend/RTLinfercolor.ml` (union-find algorithm)

**Architecture Support:**
- Define operations: `x86_64/Op.v` (arithmetic, logical, memory operations)
- Register file: `x86_64/Machregs.v` (define machine register names and conventions)
- Code generation: `x86_64/Asmgen.v` (Mach → Asm translation)
- Proof: `x86_64/Asmgenproof*.v` (correctness of code generation)
- Calling convention: `x86_64/Conventions1.v` (parameter passing, register allocation)
- Assembly syntax: `x86_64/Asm.v` (instruction types, syntax)
- Printer: `x86_64/TargetPrinter.ml` (pretty-print assembly)
- Expansion: `x86_64/Asmexpand.ml` (expand macros, builtins)

**Runtime Support:**
- C implementations: `runtime/c/` - Functions linked with compiled code
- Architecture startup: `runtime/x86_64/` - Startup code, exception handling
- Headers: `runtime/include/` - Exported interfaces

## Special Directories

**`backend/` - Generated/Backup files:**
- Purpose: Iteration and debugging artifacts
- Generated: None (all .v files are hand-written)
- Committed: Backup files (`*_backup.v`, `*_backup2.v`) tracked in git, but represent old iterations
- Example: `DMRproof_backup.v`, `DMRproof_backup2.v` are previous versions of DMR proof

**`.planning/` directory:**
- Purpose: GSD (Claude mapper) generated codebase documentation
- Generated: Yes (created by `/gsd:map-codebase`)
- Committed: Yes, to provide context for future mapping/implementation passes

**`runtime/` - Build Integration:**
- Purpose: Separate from proof; provides C runtime functions
- Generated: Library archive (`.a`) from C source in `make runtime`
- Committed: Source code committed; compiled artifacts in build directory

**`flocq/`, `MenhirLib/` - Vendored Dependencies:**
- Purpose: Include external libraries without external dependency
- Generated: No
- Committed: Yes, entire libraries vendored
- Alternative: Can use system versions via `LIBRARY_FLOCQ=system`, `LIBRARY_MENHIRLIB=system` in Makefile.config

---

*Structure analysis: 2026-03-03*
