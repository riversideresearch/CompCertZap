# Architecture

**Analysis Date:** 2026-03-14

## Pattern Overview

**Overall:** Multi-stage compilation pipeline with modular semantic preservation proofs

**Key Characteristics:**
- Language-by-language transformation: C source → Csyntax → Clight → Cminor → CminorSel → RTL → LTL → Linear → Mach → Asm
- Each transformation pass has corresponding proof of semantic preservation (forward or backward simulation)
- Fault tolerance extension adds TMR/DMR insertion at RTL level with color-based correctness guarantee
- Proof composition through relational specifications (`match_prog`) that enable separate compilation and linking
- Optional intermediate passes (optimizations) gated by `Compopts` flags

## Layers

**Proof Utilities (lib):**
- Purpose: General-purpose Coq theorems and data structures used throughout the codebase
- Location: `lib/`
- Contains: Maps, Integers, UnionFind, Lattice, Postorder, BoolEqual, Axioms
- Depends on: Coq standard library
- Used by: All semantic layers

**Common Definitions (common):**
- Purpose: Shared type definitions, memory model, event semantics, behaviors, and linking framework
- Location: `common/`
- Contains: AST (abstract syntax trees), Values, Memory model, Events, Globalenvs (global environments), Linking, Smallstep, Behaviors
- Depends on: lib/
- Used by: All language semantics

**C Frontend (cfrontend, cparser):**
- Purpose: Parse C source into abstract syntax and provide C semantics
- Location: `cfrontend/` (Coq definitions), `cparser/` (OCaml parser)
- Contains: Csyntax (C AST), Clight (simplified C with explicit control flow), Csharpminor (C# language), semantics for each
- Depends on: common/
- Used by: Code generation passes

**Backend - Language Definitions (backend):**
- Purpose: RTL and lower-level intermediate representations with semantics
- Location: `backend/`
- Key files: `RTL.v` (register transfer language), `LTL.v` (linear form), `Linear.v` (linearized), `Mach.v` (machine-like), `Asm.v` (assembly in arch-specific directories)
- Depends on: common/
- Used by: Transformation passes and proofs

**Backend - Standard Optimizations (backend):**
- Purpose: RTL-level code optimization passes
- Location: `backend/`
- Passes: Tailcall, Inlining, Constprop (constant propagation), CSE (common subexpression elimination), Deadcode (dead code elimination), Unusedglob (unused global elimination)
- Each pass has `*proof.v` for semantic preservation
- Depends on: RTL.v and other intermediate langs
- Used by: Compiler pipeline via `transf_rtl_program`

**Backend - Fault Tolerance (backend):**
- Purpose: TMR/DMR replication and single-fault tolerance proof under color-based separation
- Location: `backend/`
- Key files:
  - `RTLfault.v`: Faulty semantics (single-fault model with `maybe_zap` corruption)
  - `RTLcolor.v`: Color system specification (Red/Green/Blue/White/Pink)
  - `RTLcolorcheck.v`: Boolean color checker and `infer_coloring` oracle axiom
  - `RTLinfercolor.ml`: Unverified OCaml union-find color inference (extracted from Coq)
  - `RTLdmr.v` / `RTLtmr.v`: DMR/TMR replication transformation (shadows registers, adds checks/votes)
  - `RTLdmrproof.v` / `RTLtmrproof.v`: Backward simulation proofs
  - `RTLtolerant.v`: Core tolerance proof (3-voting ≥ 2-voting under fault)
  - `RTLagreement.v`: Weak agreement definition (registers agree when not faulted)
  - `Builtins2.v`: Vote builtin definitions (`vote_type` typeclass, voting operations)
  - `Novotes.v` / `Novotesproof.v`: Checker/proof that program has no votes pre-replication
- Depends on: RTL.v, RTLcolor.v, common/, lib/
- Used by: `transf_c_program_to_rtl` and main fault tolerance theorem

**Backend - Lowering (backend):**
- Purpose: RTL → Asm transformation through LTL, Linear, Mach
- Location: `backend/`
- Passes: Allocation (register allocation), Tunneling (branch optimization), Linearize, CleanupLabels, Debugvar, Stacking, Asmgen
- Each has `*proof.v` for semantic preservation
- Depends on: RTL.v and lower languages
- Used by: Full compilation pipeline

**Architecture-Specific (x86/, x86_32/, x86_64/, arm/, aarch64/, riscV/, powerpc/):**
- Purpose: Architecture-specific definitions and code generation
- Location: `x86/`, `aarch64/` (configured at build time)
- Contains: `Asm.v` (assembly syntax/semantics), `Op.v` (operations), `Machregs.v` (machine registers), `Asmgen.v` (code generation to asm)
- Depends on: backend/
- Used by: Asmgen pass and Asmgen proof

**Driver (driver/):**
- Purpose: Compiler orchestration and top-level semantic preservation theorem
- Location: `driver/`
- Key files:
  - `Compiler.v`: Pipeline definitions (`transf_c_program`, `transf_c_program_to_rtl`, etc.) and relational specs (`CompCert's_passes`, `match_prog`)
  - `Complements.v`: Top-level theorem `transf_c_program_to_rtl_preservation_faulty` (main fault tolerance result)
  - `Driver.ml`: OCaml entry point (frontend, color checking, backend invocation)
- Depends on: All proof modules
- Used by: ccomp compiler binary

**Extraction (extraction/):**
- Purpose: Extract verified Coq code to OCaml and wire in unverified oracles
- Location: `extraction/`
- Key file: `extraction.v` (directs Coq extraction, axiomatizes `RTLinfercolor.infer_coloring`)
- Depends on: All modules to be extracted
- Used by: OCaml build process

## Data Flow

**Standard Compilation (transf_c_program):**

```
Csyntax (input)
  ↓ SimplExpr
Clight
  ↓ SimplLocals
Clight (simplified)
  ↓ Cshmgen
Csharpminor
  ↓ Cminorgen
Cminor
  ↓ Selection
CminorSel
  ↓ RTLgen
RTL (no votes, not colored)
  ↓ [Tailcall, Inlining, Renumber, Constprop, CSE, Deadcode, Unusedglob]
RTL (optimized)
  ↓ Novotes checker
RTL (verified no votes)
  ↓ [optional DMR]
RTL (DMR-replicated, 2x regs)
  ↓ [optional TMR]
RTL (TMR-replicated, 3x regs)
  ↓ Renumber
RTL (renumbered)
  ↓ [Allocation, Tunneling, Linearize, CleanupLabels, Debugvar, Stacking, Asmgen]
Asm (output)
```

**Fault Tolerance Compilation (transf_c_program_to_rtl):**

Same path, but stops at RTL level before lowering. Used by driver to check coloring before continuing to Asm.

**Semantic Preservation Chain:**

Each compilation pass relates input and output via `match_prog` relation:
- Forward simulation: Input behavior ≤ Output behavior (optimizations may remove errors)
- Backward simulation: Output behavior ≤ Input behavior (lowering preserves behavior)

Composed via `compose_passes` to create chain from Csyntax → Asm (or → RTL).

**Fault Tolerance Proof Composition:**

Four refinements stacked in `driver/Complements.v`:

1. **Standard compilation:** C (no votes) ≥ 2-voting RTL (backward sim via `transf_c_program_to_rtl`)
2. **Weak agreement:** 2-voting RTL ≥ 3-voting RTL (trivial from Novotes)
3. **TMR replication:** 3-voting RTL ≥ 3-voting RTL+TMR (backward sim via RTLtmrproof)
4. **Fault tolerance:** 3-voting RTL+TMR ≥ 2-voting faulty RTL+TMR (backward sim via RTLtolerant, requires color invariant)

## Key Abstractions

**Program (AST.program):**
- Purpose: Represents a compiled unit with global definitions and init
- Examples: `Csyntax.program`, `RTL.program`, `Asm.program`
- Pattern: Record with `prog_defs: list (ident * globdef)`, `prog_main: ident`, `prog_types: list composite_definition`

**Instruction Sequence:**
- Purpose: Control flow graph of operations
- Pattern: `fn_code : PTree.t instruction` (node → instruction map) in RTL and below
- Operations: Conditional jumps, function calls, memory access, arithmetic

**Register Set (Regset):**
- Purpose: Track live registers for coloring and matching
- Pattern: Abstract finite sets in matching predicates; `PMap.t Regset.t` maps nodes to live sets
- Used by: Liveness analysis, coloring, weak agreement matching

**Color (RTLcolor.v):**
- Purpose: Mark registers for fault tolerance (Red=shadow, Green/Blue=voting copies, White/Pink=temporary)
- Values: `Red | Green | Blue | White | Pink`
- Invariant: Basic colors (Red, Green, Blue) stable; White/Pink reset after use
- Function: `node → reg → color` (color changes per control point)

**Vote Builtin (Builtins2.v):**
- Purpose: Runtime voting operations (majority voting, shadowing)
- Parameterized by: `vote_type` (Two or Three for DMR/TMR)
- Examples: `__builtin_vote_int_two`, `__builtin_vote_long_three`
- Pattern: Via `VoteSemantics` typeclass for polymorphic semantics

**Global Environment (Globalenvs.genv):**
- Purpose: Mapping from identifiers to function/variable definitions
- Used by: Semantics for function lookup
- Pattern: Built once from program and threaded through execution

**Memory Model (Memory.mem):**
- Purpose: Abstract heap with permissions and values
- Operations: Alloc, free, load, store with permission checks
- Used by: Semantics for pointer dereference and mutable state

## Entry Points

**Coq Proofs (transf_c_program_to_rtl):**
- Location: `driver/Compiler.v` line 252
- Triggers: During full compilation or for intermediate checking
- Responsibilities:
  - Apply C → Clight → ... → RTL passes
  - Apply DMR/TMR if flags set
  - Result: RTL program with or without replication

**OCaml Compiler (compile_c_file):**
- Location: `driver/Driver.ml` line 41
- Triggers: User runs `./ccomp input.c -o output`
- Responsibilities:
  1. Parse C to Csyntax
  2. Call `transf_c_program_to_rtl` to get RTL
  3. Check coloring via `RTLcolorcheck.check_program`
  4. Call `transf_rtl_program''` to complete Asm compilation
  5. Write assembly output

**Color Checker:**
- Location: `driver/Driver.ml` line 63
- Triggers: After RTL generation, if TMR/DMR enabled
- Responsibilities: Verify color invariant holds (via `RTLinfercolor.infer_coloring` oracle)
- Failure: Exit with error (program not well-colored)

**Extraction Axiomatization:**
- Location: `extraction/extraction.v`
- Triggers: During OCaml build after Coq proof extraction
- Responsibilities: Wire unverified `RTLinfercolor.infer_coloring` OCaml implementation to Coq axiom

## Error Handling

**Strategy:** Exception-based (OCaml) for execution, `Errors.res` (Coq) for static checks

**Patterns:**

**Coq (res monad):**
```coq
Definition transf_rtl_program (f: RTL.program) : res RTL.program
```
- `OK value` on success
- `Error message` on failure (parse error, type error, allocation failure, coloring failure)
- Composed with `@@@` (apply_partial) and `@@` (apply_total)

**OCaml (Errors exception):**
```ocaml
match Compiler.transf_c_program_to_rtl csyntax with
| Errors.OK rtl -> ...
| Errors.Error msg -> fatal_error loc "%a" print_error msg
```
- Extract OCaml `unit` or `option` from Coq errors
- Print errors with location and abort

**Coloring Failure:**
```ocaml
if RTLcolorcheck.check_program rtl then ()
else begin print_endline "RTL program not well-colored!"; exit 1 end
```
- Verify color invariant before continuing
- Exit immediately if failed

## Cross-Cutting Concerns

**Logging:** Print intermediate RTLs via `print_RTL` calls in pipeline (off by default, controlled by flags)

**Validation:** Each pass verifies structural invariants (RTL typing, liveness, etc.) before proof application

**Backward Compatibility:** Optimization passes optional via `Compopts` flags; Novotes inserted to enable fault tolerance

**Separate Compilation:** `TransfLink` typeclass ensures all passes commute with linking, enabling compositional verification

---

*Architecture analysis: 2026-03-14*
