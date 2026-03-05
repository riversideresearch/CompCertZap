# Codebase Structure

**Analysis Date:** 2026-03-04

## Directory Layout

```
compcert/
├── lib/                    # Coq utility library (maps, integers, floats, algorithms)
├── common/                 # Shared definitions (AST, memory, linking, semantics)
├── cfrontend/              # C frontend (Csyntax, Clight, parsing, elaboration)
├── cparser/                # OCaml C parser (Menhir-based, lexer, elaboration)
├── backend/                # RTL and lower IRs, optimizations, register allocation, code gen
├── driver/                 # Compiler orchestration (Compiler.v, Complements.v, Driver.ml)
├── extraction/             # Coq → OCaml extraction directives
├── x86/                    # x86-64 specific language definitions and code generation
├── arm/                    # ARM architecture specifics
├── aarch64/                # AArch64 architecture specifics
├── powerpc/                # PowerPC architecture specifics
├── riscV/                  # RISC-V architecture specifics
├── runtime/                # C runtime support (syscalls, memory ops)
├── flocq/                  # Floating-point library (vendor copy)
├── MenhirLib/              # Menhir parser library (vendor copy)
├── debug/                  # Debugging utilities
├── tools/                  # Build and utility scripts
├── import/                 # Import utilities for external proofs
├── export/                 # Export utilities for external tools
├── test/                   # Test cases and examples
├── doc/                    # Documentation
├── _CoqProject             # Coq project configuration
├── Makefile                # Main build rules
├── Makefile.extr           # Extraction and OCaml build rules
├── configure               # Build configuration script
└── .depend                 # Dependency tracking
```

## Directory Purposes

**lib/**
- Purpose: General-purpose Coq utilities and algorithms for use throughout the compiler
- Contains: Data structures (Maps, AVL trees, union-find), number types (Integers, Floats), algorithms (Heaps, Postorder, Kildall fixed-point iteration)
- Key files: `Maps.v` (polymorphic finite maps), `Integers.v` (machine integer semantics), `Floats.v` (IEEE754), `Lattice.v` (abstract interpretation), `UnionFind.v` (union-find for register coloring)

**common/**
- Purpose: Language-independent definitions and proof frameworks shared across all compilation passes
- Contains: AST structure definitions, memory model, value semantics, event traces, linking infrastructure, small-step semantics framework
- Key files:
  - `AST.v`: Global definitions (identifiers, function/variable declarations, linkage)
  - `Memory.v`: Byte-addressable memory model with permissions
  - `Values.v`: Semantic values (integers, floats, pointers, undefined)
  - `Events.v`: Observable events (I/O, system calls)
  - `Smallstep.v`: Generic small-step semantics (transition relations, forward/backward simulation)
  - `Linking.v`: Separate compilation and linking theory
  - `Behaviors.v`: Program execution traces and observable behavior equivalence

**cfrontend/**
- Purpose: C-level language definitions, semantics, and transformations down to Cminor
- Contains: High-level C semantics (`Csem.v`), type system (`Ctyping.v`), simplified Clight language, initial transformations
- Key files:
  - `Csyntax.v`: Abstract syntax of CompCert C (expressions, statements, declarations)
  - `Clight.v`: Simplified C language (pure expressions, statements only, no complex expr nesting)
  - `Csharpminor.v`: C#minor (lower level, primitive operations)
  - `SimplExpr.v`: Expression flattening (Csyntax → Clight)
  - `SimplLocals.v`: Stack allocation elimination (Clight → Csharpminor)
  - `Cshmgen.v`: Code generation (Csharpminor → Cminor)
  - `Cminorgen.v`: Cminor generation (further lowering)

**cparser/**
- Purpose: Implement C source code parsing and elaboration (OCaml-based, extracted separately)
- Contains: Lexer, parser (Menhir), elaboration (type checking, name resolution), machine-specific attributes
- Key files:
  - `Lexer.ml`: Tokenization of C source
  - `Parser.mly`: Menhir grammar for C syntax
  - `Elab.ml`: Elaboration (resolve types, names, storage classes)
  - `Machine.ml`: Machine-specific configuration (sizes, alignments)
  - `Checks.ml`: Additional semantic checks
  - Does NOT have `.v` proofs (extraction assumes parser correct)

**backend/**
- Purpose: Intermediate representations from RTL downward, optimizations, and target code generation
- Contains: Language definitions, transformation passes, proof modules, machine-independent optimizations
- Organization:
  - **Language definitions** (no proof): `RTL.v`, `LTL.v`, `Linear.v`, `Mach.v`, `Asm.v`
  - **Optimization passes**: `Tailcall.v`, `Inlining.v`, `Renumber.v`, `Constprop.v`, `CSE.v`, `Deadcode.v`, `Unusedglob.v`
  - **Register allocation**: `Allocation.v` (uses linear scan), `Registers.v` (register set definitions)
  - **Linearization**: `Linearize.v` (CFG → linear), `Tunneling.v` (branch optimization)
  - **Stacking**: `Stacking.v` (stack frame layout)
  - **Analysis**: `Liveness.v` (register liveness), `ValueDomain.v` (constant propagation domain), `Kildall.v` (fixed-point iteration)
  - **Fault tolerance**: `RTLfault.v` (faulty semantics), `RTLcolor.v` (color definitions), `RTLcolorcheck.v` (color verification), `RTLdmr.v`/`RTLtmr.v` (replication passes), `RTLtolerant.v` (backward simulation under fault)
  - **Checking**: `Novotes.v` (ensure no vote builtins), `RTLinfercolor.ml` (color inference oracle)
- Key file pairs (pass + proof): e.g., `Allocation.v` + `Allocproof.v`, `Inlining.v` + `Inliningproof.v`

**driver/**
- Purpose: High-level orchestration and composition of compilation passes
- Contains: Compiler pipeline definitions, linking of pass proofs, top-level entry points
- Key files:
  - `Compiler.v`: Pipeline compositions (`transf_c_program`, `transf_rtl_program`, etc.), monadic operators (`@@@`, `@@`)
  - `Complements.v`: Corollaries and top-level theorems (e.g., `transf_c_program_to_rtl_preservation_faulty`)
  - `Driver.ml`: OCaml entry point; orchestrates parsing, coloring, optional DMR/TMR, code generation

**extraction/**
- Purpose: Direct Coq → OCaml code extraction and wiring
- Contains: Extraction directives that map Coq definitions to optimized OCaml implementations
- Key file: `extraction.v` (100+ extraction pragmas for optimized operations)
- Wiring examples:
  - `Allocation.regalloc` → `Regalloc.regalloc` (OCaml register allocator)
  - `RTLcolorcheck.infer_coloring` → `RTLinfercolor.infer_coloring` (OCaml color oracle)
  - `Selection.compile_switch` → `Switchaux.compile_switch` (OCaml switch compilation)

**x86/, arm/, aarch64/, powerpc/, riscV/**
- Purpose: Architecture-specific language definitions and code generation
- Contains: Target machine's AST (Asm), operations (Op), conventions (calling, registers, stack layout), instruction selection
- Pattern (for x86):
  - `Asm.v`: x86-64 assembly AST
  - `Op.v`: x86-64 operation types
  - `Machregs.v`: Hardware register definitions
  - `Conventions1.v`: Calling conventions
  - `Asmgen.v`: Mach → Asm code generation
  - `SelectOp.v`: CminorSel → RTL instruction selection (x86-specific)
  - `SelectLong.v`: 64-bit operation handling
  - `CombineOp.v`: Peephole optimization
  - `extractionMachdep.v`: Machine-specific extraction directives

**runtime/**
- Purpose: C runtime support library linked with compiled programs
- Contains: Assembly implementations of builtins, syscall wrappers, memory operations
- Organization: `c/` (C code), `include/` (headers), architecture-specific subdirs (`x86/`, `arm/`, etc.)

**test/**
- Purpose: Test programs for compiler validation
- Contains: Small C programs to verify compilation and behavior

**doc/**
- Purpose: Project documentation (notes, papers, specifications)
- Contains: Fault tolerance documentation, proof notes, architecture diagrams

## Key File Locations

**Entry Points:**

- `driver/Compiler.v`: Coq compiler pipeline definitions
  - `transf_c_program`: C → Asm (full pipeline)
  - `transf_c_program_to_rtl`: C → RTL (for fault tolerance)
  - `transf_rtl_program'`: RTL → Asm (after optional DMR/TMR)

- `driver/Driver.ml`: OCaml entry point
  - Parses command-line arguments
  - Calls Coq-extracted `Compiler` functions
  - Invokes color checker (`RTLcolorcheck`)
  - Outputs assembly file

**Configuration:**

- `Makefile.config`: Build configuration (architecture, paths, compiler flags)
- `_CoqProject`: Coq project includes (library paths, `-R` flags for all directories)
- `Makefile.extr`: Extraction rules (Coq → OCaml, OCaml compilation)
- `compcert.ini`: Runtime configuration (architecture, machine size, ABI)

**Core Logic (Proofs and Definitions):**

- `backend/RTL.v`: RTL language definition (instructions, semantics, CFG representation)
- `backend/Liveness.v`: Liveness analysis for registers
- `backend/RTLcolor.v`: Color system (Red/Green/Blue/White/Pink)
- `backend/RTLcolorcheck.v`: Color validation
- `backend/RTLfault.v`: Faulty semantics with single-bit fault model
- `backend/RTLtolerant.v`: Backward simulation (TMR program >= faulty program)
- `backend/RTLdmr.v`: DMR instruction replication
- `backend/RTLtmr.v`: TMR instruction replication
- `backend/Builtins2.v`: Vote builtin definitions, `VoteSemantics` typeclass

**Testing and Checking:**

- `backend/Novotes.v`: Checker for vote-free programs (no TMR builtins before replication)
- `backend/RTLinfercolor.ml`: Union-find based color inference
- `cparser/Elab.ml`: C semantic checks (types, forward declarations, etc.)

## Naming Conventions

**Files:**

- `Foo.v`: Language definition or transformation pass definition
- `Fooproof.v`: Correctness proof for pass `Foo` (semantic preservation via simulation)
- `Foospec.v`: Specification or auxiliary lemmas for pass `Foo`
- `Foo.ml`: OCaml implementation (extracted from Coq or hand-written)
- `Foo.mli`: OCaml interface
- `Fooaux.ml`: OCaml auxiliary functions (helper code for extracted modules)
- `test_*.c`: Test program

**Directories:**

- `backend/`: IR definitions and transformations (RTL and below)
- `cfrontend/`: High-level C language (Csyntax, Clight)
- `arch/` (e.g., `x86/`, `arm/`): Architecture-specific code
- `lib/`: Reusable algorithmic and data structure utilities
- `common/`: Shared frameworks and definitions

**Type/Module Names:**

- Languages are typically capitalized module names: `RTL`, `Mach`, `Asm`, `Clight`
- Proof modules end with "proof": `Allocproof`, `RTLdmrproof`
- Predicates/properties are lowercase with underscores: `wc_function`, `check_program`
- Binary operations on user types use `@` symbol: `@@@` for monadic bind with error, `@@` for function application

## Where to Add New Code

**New Optimization Pass:**
- Primary pass definition: `backend/NewOpt.v` (define `transf_program : program → res program`)
- Proof: `backend/NewOptproof.v` (prove forward or backward simulation)
- Add to pipeline: Insert call in `driver/Compiler.v` between appropriate existing passes
- Extraction: Add extraction directives in `extraction/extraction.v` if hand-written OCaml helpers needed

**New Language Feature (at RTL level or higher):**
- If affects semantics: Add to instruction type in `backend/RTL.v` (or appropriate language file)
- Update all passes that touch instructions: scan `backend/` for pattern matches on instruction types
- Add proofs of invariant preservation

**Fault Tolerance Extension (new color-based constraint):**
- Update `backend/RTLcolor.v` with new color type or constraint
- Update `backend/RTLcolorcheck.v` to enforce constraint in `check_program`
- Update `backend/RTLinfercolor.ml` union-find logic to respect constraint
- Update `backend/RTLtolerant.v` backward simulation to justify new constraint

**New Architecture Target:**
- Create new directory: `newarch/`
- Define: `newarch/Asm.v`, `newarch/Op.v`, `newarch/Machregs.v`, `newarch/Conventions1.v`
- Implement: `newarch/Asmgen.v` (Mach → Asm), `newarch/SelectOp.v`, `newarch/SelectLong.v`
- Extraction: `newarch/extractionMachdep.v` for C builtin generation
- Register in: `configure` script and `Makefile.config`

**Utilities (reusable algorithms):**
- Location: `lib/` (if general purpose) or within specific module if specialized
- Pattern: Define algorithm in `.v` file, optionally provide hand-written `.ml` via extraction, include proof of correctness

## Special Directories

**extraction/ (Generated Code)**
- Purpose: Guides Coq code extraction to OCaml
- Generated: Yes (extraction.v is hand-written, but many .ml files are auto-extracted)
- Committed: extraction.v is committed; extracted .ml files generated during build

**flocq/, MenhirLib/ (Vendor)**
- Purpose: External libraries (IEEE754 floats, parser combinator library)
- Generated: No (pre-built, included in repo)
- Committed: Yes

**ocaml-4.14.2_compcert/ (Bundled OCaml)**
- Purpose: Complete OCaml compiler used for extraction and final compilation
- Generated: No (built once, included for reproducibility)
- Committed: Partial (sources only, built artifacts not committed)

**.depend, .depend.extr (Dependency Files)**
- Purpose: Track compilation dependencies (generated by Coq/OCaml)
- Generated: Yes (produced by `coqc -make-docstyle`, kept for incremental builds)
- Committed: Yes (to speed up clean builds)

**extraction/ → backend/*.ml**
- Generated files from Coq extraction; produced by running `make extraction`
- Examples: `Allocation.ml` (from `Allocation.v`), `RTLinfercolor.ml` (hand-written, wired via extraction.v)

---

*Structure analysis: 2026-03-04*
