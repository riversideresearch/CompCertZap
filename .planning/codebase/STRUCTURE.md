# Codebase Structure

**Analysis Date:** 2026-03-14

## Directory Layout

```
compcert/
├── lib/                      # Proof utilities (Maps, Integers, UnionFind, etc.)
├── common/                   # Shared definitions (AST, Values, Memory, Events, Linking)
├── cfrontend/                # C front-end (Csyntax, Clight, Csharpminor, proofs)
├── cparser/                  # OCaml C parser (Menhir-based Parser.vy, Lexer.mll)
├── backend/                  # RTL and below (optimizations, faults, lowering, proofs)
├── x86/, x86_64/, arm/,
│   aarch64/, riscV/          # Architecture-specific (Asm.v, Op.v, code generation)
├── driver/                   # Compiler orchestration (Compiler.v, Complements.v, Driver.ml)
├── extraction/               # Coq-to-OCaml extraction (extraction.v)
├── runtime/                  # C runtime support (per-architecture)
├── ccomp                     # Compiled compiler binary
├── Makefile                  # Build configuration
├── Makefile.extr             # OCaml extraction build rules
├── configure                 # Build configuration script
├── _CoqProject               # Coq IDE project file
├── CLAUDE.md                 # Project documentation (this archive)
└── doc/                      # Documentation (README, Changelog)
```

## Directory Purposes

**lib/:**
- Purpose: Proof utilities and foundational Coq theorems
- Contains: Coqlib (standard library extensions), Maps (finite maps), Integers, Floats, UnionFind, Lattice, Postorder, BoolEqual, Decidableplus
- Key files: `Coqlib.v` (most imported), `Maps.v` (PTree, PMap)
- Not generated; part of core proof foundation

**common/:**
- Purpose: Shared type definitions and semantics used by all compilation stages
- Contains:
  - `AST.v`: Abstract syntax tree definitions (function, instruction, global definitions, type system)
  - `Values.v`: Value representation (int, long, float, pointer with undefined)
  - `Memory.v` / `Memtype.v`: Abstract memory model (permissions, bytes, loads/stores)
  - `Events.v`: Externally observable events (I/O, function calls)
  - `Smallstep.v`: Operational semantics (trace, behavior definitions)
  - `Behaviors.v`: Program behaviors (infinite execution, divergence, stuck states)
  - `Globalenvs.v`: Global environment (function/variable lookup)
  - `Linking.v`: Module composition for separate compilation (`TransfLink`)
- Key patterns: Most types parameterized by architecture-specific operations
- Not generated

**cfrontend/:**
- Purpose: C parsing, typing, and intermediate languages
- Contains:
  - `Csyntax.v`: C abstract syntax tree (types, declarations, expressions, statements)
  - `Csem.v` / `Cexec.v`: C semantics (small/big step)
  - `Clight.v`: Simplified C (explicit control flow, no expressions in loops)
  - `Csharpminor.v`: C#minor (further simplification, goto/label elimination)
  - `SimplExpr.v` / `SimplExprproof.v`: Csyntax → Clight transformation
  - `Cshmgen.v` / `Cshmgenproof.v`: Clight → Csharpminor
  - Plus `SimplLocals.v`, `Cminorgen.v` (transition to Cminor)
- All `.v` files compiled to `.vo` by `make proof`
- Proofs show semantic preservation (backward simulation)

**cparser/:**
- Purpose: Parse C source files to Csyntax
- Contains:
  - `Parser.vy`: Menhir grammar (produces Parser.ml, Parser.mli)
  - `Lexer.mll`: ocamllex lexer (produces Lexer.ml)
  - `Elab.ml`: Type checking and elaboration (ast → Csyntax)
  - `C2C.ml`: Integration layer
- Generated: Parser.ml (from Parser.vy), Lexer.ml (from Lexer.mll)
- Compiled: .cmi, .cmx, .o files for linking into ccomp

**backend/:**
- Purpose: RTL and lower-level intermediate representations with optimizations and fault tolerance
- Contains (alphabetically):

  **Language Definitions:**
  - `RTL.v`: Register Transfer Language (intermediate representation used by fault tolerance)
  - `LTL.v`: Linear Transfer Language
  - `Linear.v`: Linearized (single-entry, no branches except at end)
  - `Mach.v`: Machine-like (explicit stack operations)
  - (Architecture-specific Asm.v in x86/, etc.)

  **Standard Optimizations:**
  - `Tailcall.v` / `Tailcallproof.v`: Tail call optimization
  - `Inlining.v` / `Inliningproof.v`: Function inlining
  - `Constprop.v` / `Constpropproof.v`: Constant propagation
  - `CSE.v` / `CSEproof.v`: Common subexpression elimination
  - `Deadcode.v` / `Deadcodeproof.v`: Dead code elimination
  - `Unusedglob.v` / `Unusedglobproof.v`: Remove unused globals
  - `Renumber.v` / `Renumberproof.v`: Renumber basic blocks (resets node IDs)
  - `Tunneling.v` / `Tunnelingproof.v`: Branch to branch elimination
  - `Linearize.v` / `Linearizeproof.v`: RTL → Linear
  - `CleanupLabels.v` / `CleanupLabelsproof.v`: Remove unused labels
  - `Stacking.v` / `Stackingproof.v`: Stack frame layout
  - `Allocation.v` / `Allocproof.v`: Register allocation (RTL → LTL)
  - `Debugvar.v` / `Debugvarproof.v`: Optional debugging info

  **Fault Tolerance (Core):**
  - `RTLfault.v`: Faulty RTL semantics (single-fault model with `maybe_zap`)
  - `RTLcolor.v`: Color specification (Red, Green, Blue, White, Pink)
  - `RTLcolorcheck.v`: Color invariant checker; axiomatizes `infer_coloring` oracle
  - `RTLinfercolor.ml`: Unverified OCaml color inference (union-find based)
  - `RTLagreement.v`: Weak agreement (registers agree when not faulted)

  **Fault Tolerance (DMR/TMR):**
  - `RTLdmr.v` / `RTLdmrproof.v`: Dual modular redundancy (2x shadow registers)
  - `RTLtmr.v` / `RTLtmrproof.v`: Triple modular redundancy (3x shadow registers)
  - `RTLdmrspec.v` / `RTLtmrspec.v`: Semantic specifications for replication
  - `RTLreplicateSpecCommon.v`: Shared replication semantics

  **Fault Tolerance (Tolerance Proof):**
  - `RTLtolerant.v`: Backward simulation: 3-voting RTL >= 2-voting faulty RTL (requires color invariant)
  - `Builtins2.v`: Vote builtin definitions and `VoteSemantics` typeclass
  - `Novotes.v` / `Novotesproof.v`: Checker that program has no vote builtins pre-replication

  **Helper Modules:**
  - `Liveness.v`: Live register analysis (used by coloring)
  - `ProofLiveness.v`: Proofs about liveness
  - `RTLtyping.v`: RTL type checking
  - `Registers.v`: Register definitions
  - `Locations.v`: Location tracking
  - `Conventions.v`: Calling conventions
  - `Op.v`: Architecture-independent operations (in backend, arch-specific in x86/)
  - `Bounds.v`: Stack bounds analysis
  - `Kildall.v`: Iterative dataflow framework
  - `ValueAnalysis.v`, `ValueDomain.v`, `NeedDomain.v`: Value analysis for optimizations

- All `.v` files compiled to `.vo` by `make proof`
- `.ml` file (RTLinfercolor.ml) extracted and compiled to .cmi, .cmx, .o

**x86/, x86_64/, arm/, aarch64/, riscV/, powerpc/:**
- Purpose: Architecture-specific definitions and code generation
- Configured at build time (e.g., `./configure x86_64-linux`)
- Contains (per architecture):
  - `Asm.v`: Assembly language syntax and semantics
  - `Op.v`: Machine operations (add, mul, shift, etc.)
  - `Machregs.v`: Machine registers (rax, rbx, etc. for x86_64)
  - `Asmgen.v` / `Asmgenproof.v`: Mach → Asm code generation
  - `Conventions1.v`: Calling conventions
  - `SelectOp*.v` / `SelectOp*proof.v`: Operation selection optimizations
  - `Builtins1.v`: Architecture-specific builtins
  - `Archi.v`: Architecture flags
  - `Stacklayout.v`: Stack frame layout
  - `extractionMachdep.v`: Architecture-specific extraction directives
- All `.v` files compiled; generated .cmi, .cmx, .o for extraction build

**driver/:**
- Purpose: Compiler orchestration and top-level theorems
- Contains:
  - `Compiler.v`: Monadic pipeline definitions
    - `transf_c_program`: Full pipeline (C → Asm)
    - `transf_c_program_to_rtl`: Truncated pipeline (C → RTL)
    - `transf_rtl_program` / `transf_rtl_program'`: RTL optimizations
    - `transf_rtl_program''`: RTL → Asm lowering
    - Relational specs: `CompCert's_passes`, `to_rtl_passes`, `match_prog`, `match_prog_rtl`
  - `Complements.v`: Top-level theorems
    - `transf_c_program_to_rtl_preservation_faulty`: Main fault tolerance result
    - `match_prog_rtl_asm`: RTL-to-Asm matching
  - `Driver.ml`: OCaml entry point
    - `compile_c_file`: Main compilation function
    - Color checking, intermediate RTL parsing, ASM writing
  - `Compopts.v`: Compiler options (flags for optimizations, TMR/DMR, debug)
  - `Driveraux.ml`: Auxiliary functions (error handling, timing)
- Compiled: `Complements.vo` (Coq proof), `Driver.cmi`, `Driver.cmx`, `Driver.o` (OCaml)

**extraction/:**
- Purpose: Direct Coq code extraction to OCaml and axiomatize unverified parts
- Contains:
  - `extraction.v`: Extraction directives
    - `Extraction Language Ocaml` (target language)
    - `Extraction "backend/RTLinfercolor" Compiler` (extract Compiler to RTLinfercolor.ml)
    - `Parameter infer_coloring : ...` (axiomatize the oracle)
- Generated: backend/RTLinfercolor.ml (from extraction.v), other extracted files
- Not directly compiled; guides extraction process

**runtime/:**
- Purpose: C runtime support (linking with compiled programs)
- Contains (per architecture):
  - `c/`: Generic runtime (malloc, printf, etc.)
  - `x86_64/`, `arm/`, etc.: Architecture-specific startup code
- Compiled separately; linked with compiled user programs

---

## Key File Locations

**Entry Points:**

- `driver/Compiler.v` line 196: `transf_c_program` (full C → Asm pipeline)
- `driver/Compiler.v` line 252: `transf_c_program_to_rtl` (C → RTL pipeline)
- `driver/Driver.ml` line 41: `compile_c_file` (OCaml compiler entry point)
- `ccomp`: Compiled binary (run `./ccomp input.c -o output`)

**Configuration:**

- `_CoqProject`: Coq IDE configuration (-R flags, include paths)
- `Makefile`: Top-level build rules (targets: all, proof, extraction, ccomp, clean)
- `Makefile.extr`: OCaml extraction build rules
- `Makefile.config`: Build configuration (ARCH, BITSIZE, options)
- `compcert.ini`: Compiler options template

**Core Logic:**

- **C front-end:**
  - Parse: `cparser/Parser.vy` (grammar), `cparser/Lexer.mll` (lexer)
  - Elaborate: `cparser/Elab.ml`
  - To Clight: `cfrontend/SimplExpr.v`

- **RTL transformations:**
  - Optimizations: `backend/Tailcall.v`, `backend/Inlining.v`, `backend/Constprop.v`, etc.
  - Fault tolerance: `backend/RTLdmr.v`, `backend/RTLtmr.v`, `backend/RTLtolerant.v`
  - Lowering: `backend/Allocation.v`, `backend/Linearize.v`, `backend/Stacking.v`

- **Color checking:**
  - Specification: `backend/RTLcolor.v`
  - Checker: `backend/RTLcolorcheck.v` (calls `infer_coloring` axiom)
  - Oracle: `backend/RTLinfercolor.ml` (unverified, extracted)

- **Top-level proofs:**
  - Compiler composition: `driver/Compiler.v` (lines 321–378 define `CompCert's_passes` and `to_rtl_passes`)
  - Fault tolerance: `driver/Complements.v` (uses `RTLtolerant.v` for fault refinement)

**Testing:**

- `test/`: Small test programs (if present)
- Build with `make test` (if available)

**Documentation:**

- `CLAUDE.md`: Project instructions (architecture, proof conventions, build commands)
- `README.md`: General overview
- `Changelog.md`: Version history
- `doc/`: Additional documentation

---

## Naming Conventions

**Files:**

- `Name.v`: Coq language definition or specification
- `Nameproof.v`: Semantic preservation proof for `Name.v` transformation
- `Namespec.v`: Semantic specification (alternate naming, e.g., `RTLdmrspec.v`)
- `Name.ml`: OCaml implementation (backend, drivers, extraction)
- `Name.mli`: OCaml interface signature

**Directories:**

- `lib/`: Lower-case (convention)
- `common/`, `backend/`, `cfrontend/`: Lower-case
- `x86_64/`, `aarch64/`: Architecture names with underscores
- Capitalized first letter for proof modules within directories

**Identifiers (Coq):**

- `transf_*_program`: Transformation function on whole program
- `transf_*_function`: Transformation function on single function
- `*_proof`: Forward/backward simulation lemma (e.g., `forward_simulation_proof`)
- `match_prog`: Relational specification matching input/output
- `match_*`: Match predicates for states/frames/register sets
- `*_semantics`: Semantics definition (e.g., `RTL.semantics`)

**Identifiers (OCaml):**

- `transf_*`: Transformation function
- `print_*`: Pretty-printing function (e.g., `print_RTL`)
- `compile_*`: Compilation stage function

---

## Where to Add New Code

**New Optimization Pass:**

1. **Specification:**
   - Create `backend/Newpass.v` with:
     - Transformation definition `transf_program : program → res program`
     - State type for monadic computation (if needed)
     - Invariant preservation lemmas

2. **Proof:**
   - Create `backend/Newpassproof.v` with:
     - Simulation lemma (forward or backward)
     - Proof scripts using `match_prog` framework
     - Optionally `match_if` for optional passes

3. **Integration:**
   - Add pass to `driver/Compiler.v`:
     - Include in `transf_rtl_program` sequence (between lines 162–178)
     - Add to `CompCert's_passes` list (around line 331)
   - Add proof imports to `driver/Compiler.v` (after line 79)
   - Add to Makefile dependencies (Makefile)

4. **Testing:**
   - Build: `make backend/Newpassproof.vo`
   - Full build: `make proof`

**New Intermediate Language:**

1. **Syntax/Semantics:**
   - Create `backend/Lang.v` with:
     - Type definitions (function, instruction, program)
     - Semantics (state, step rules, initial state)
   - Follow patterns from `RTL.v`, `LTL.v`

2. **Code Generation:**
   - Create `backend/LangGen.v` (PrevLang → Lang transformation)
   - Create `backend/LangGenproof.v` (correctness proof)

3. **Lowering:**
   - Create `backend/LangTo*.v` (Lang → NextLang)
   - Create `backend/LangTo*proof.v`

4. **Integration:**
   - Include in compilation pipeline as above

**New Fault Tolerance Feature:**

1. **Specification:**
   - Extend `backend/RTLcolor.v` (if color system needs changes)
   - Or create `backend/RTLnewtolerance.v` with new semantics

2. **Proof:**
   - Create `backend/RTLnewtolerance[proof].v`
   - Prove backward simulation against faulty semantics

3. **Integration:**
   - Wire into `driver/Complements.v` main theorem
   - Update `driver/Driver.ml` if oracle needed

**New Builtin Operation:**

1. **Definition:**
   - Add to `backend/Builtins2.v`:
     - Builtin signature (arguments, results)
     - Semantics via `VoteSemantics` typeclass if voting-related

2. **Architecture Support:**
   - Add to `x86_64/Op.v` (or relevant arch):
     - Operation encoding if low-level
   - Add to `x86_64/Asmgen.v` if code generation needed

3. **DMR/TMR Support:**
   - Update `backend/RTLdmr.v` / `RTLtmr.v` if replication-aware

**Utilities:**

**Shared helpers:** `lib/Coqlib.v` (extend existing)
**New data structures:** `lib/NewStructure.v`
**Per-architecture:** `<arch>/Op.v`, `<arch>/Machregs.v`

---

## Special Directories

**Generated:**

- `extraction/`: Post-extraction OCaml files (generated from Coq by `extraction.v`)
- `*.vo` / `*.vok` / `*.vos`: Compiled Coq objects (targets of `make proof`)
- `ccomp`: Compiled binary (target of `make ccomp`)
- `*.cmi` / `*.cmx` / `*.o`: Compiled OCaml (targets of `make extraction`)

**Committed:**

- All `.v` files (proofs)
- All `.ml` / `.mli` files (unverified implementations, e.g., parser, extraction)
- `Makefile*`, `_CoqProject`, `configure` (build system)
- `doc/`, `README.md`, `CLAUDE.md` (documentation)

**Not Committed:**

- `.depend`, `.depend.extr` (generated dependencies)
- `.*.aux`, `*.glob` (Coq auxiliary)
- `*.cmi`, `*.cmx`, `*.o`, `*.a` (compiled objects)
- `ccomp` binary
- Editor config (`.vscode/`, `.idea/`, etc.)

---

*Structure analysis: 2026-03-14*
