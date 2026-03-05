# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

CompCert is a formally verified C compiler written in Coq and OCaml. This fork extends it with **fault tolerance** via Triple Modular Redundancy (TMR) and a color-based separation proof. The main theorem proves that TMR-compiled programs behave correctly under a single-fault model at the RTL level.

## Build Commands

```bash
# Configure (only needed once)
./configure x86_64-linux

# Full build: Coq proofs -> extraction -> OCaml compilation -> runtime
make -j$(nproc) all

# Individual stages
make proof              # Compile all .v files to .vo (slow - full proof checking)
make extraction         # Extract OCaml from Coq (requires proof)
make ccomp              # Build the ccomp compiler binary
make runtime            # Build runtime support library

# Compile a single Coq file (respects VPATH for finding files in subdirs)
make backend/RTLtolerant.vo

# Verify proof integrity
make check-admitted     # Ensure no Admitted proofs
make check-proof        # Verify semantic preservation

# Clean
make clean              # Remove build artifacts
make cleanall           # Remove everything including generated files

# Use the compiler
./ccomp test.c -tmr -o test    # Compile with TMR fault tolerance
./ccomp test.c -dmr -o test    # Compile with DMR
```

## Architecture

### Compilation Pipeline (defined in `driver/Compiler.v`)

```
Csyntax -> SimplExpr -> Clight -> SimplLocals -> Cshmgen -> Cminorgen
  -> Cminor -> Selection -> CminorSel -> RTLgen -> RTL
  -> [Tailcall -> Inlining -> Renumber -> Constprop -> Renumber -> CSE -> Deadcode -> Unusedglob]
  -> [DMR/TMR insertion (optional)]
  -> Renumber
  -> [Allocation -> Tunneling -> Linearize -> CleanupLabels -> Debugvar (optional) -> Stacking -> Asmgen]
  -> Asm
```

Two pipeline variants:
- `transf_c_program`: full pipeline, C to Asm
- `transf_c_program_to_rtl`: truncated pipeline stopping at RTL (for fault tolerance proof)

### Key Directories

- **`lib/`** - General Coq utilities (Maps, Integers, Coqlib, UnionFind)
- **`common/`** - Shared definitions (AST, Values, Memory model, Events, Smallstep, Behaviors)
- **`cfrontend/`** - C front-end languages: Csyntax, Clight, Csharpminor and their translation proofs
- **`cparser/`** - OCaml C parser (Menhir-based: `Parser.vy`, `Lexer.mll`, `Elab.ml`)
- **`backend/`** - RTL and below: optimizations, register allocation, code generation
- **`x86/`** - x86-64 specific: `Asm.v`, `Asmgen.v`, `Op.v`, `Machregs.v`
- **`driver/`** - `Compiler.v` (pipeline), `Complements.v` (top-level theorems), `Driver.ml` (entry point)
- **`extraction/`** - `extraction.v` directs Coq extraction to OCaml

### Fault Tolerance Extension (this fork)

Core files:
- **`backend/RTLfault.v`** - Faulty RTL semantics (single-fault model with `maybe_zap`)
- **`backend/RTLcolor.v`** - Declarative color system specification (Red/Green/Blue/White/Pink)
- **`backend/RTLcolorcheck.v`** - Verified Boolean color checker (`check_program`)
- **`backend/RTLinfercolor.ml`** - Unverified OCaml color inference oracle (union-find based)
- **`backend/RTLtolerant.v`** - Backward simulation: 3-voting non-faulty >= 2-voting faulty
- **`backend/RTLdmr.v` / `backend/RTLtmr.v`** - DMR/TMR replication passes
- **`backend/RTLdmrproof.v` / `backend/RTLtmrproof.v`** - Correctness proofs for DMR/TMR passes
- **`backend/RTLagreement.v`** - Weak agreement definition for RTL
- **`backend/Novotes.v`** - Checker that program has no vote builtins pre-TMR
- **`backend/Builtins2.v`** - Vote builtin definitions, `vote_type` (Two/Three), `VoteSemantics` typeclass
- **`driver/Complements.v`** - `transf_c_program_to_rtl_preservation_faulty` (main theorem)

The fault tolerance proof composes four refinements:
1. Standard backward sim: C >= 2-voting RTL (no votes)
2. Weak agreement: 2-voting RTL >= 3-voting RTL (trivial from no_votes)
3. TMR backward sim: 3-voting RTL >= 3-voting RTL+TMR
4. Faulty backward sim: 3-voting RTL+TMR >= 2-voting faulty RTL+TMR (requires well-colored)

### Proof Conventions

- Each compiler pass `Foo.v` has a corresponding `Fooproof.v` proving semantic preservation via forward or backward simulation
- The `res` type (Result monad) threads errors; `@@@` chains partial results, `@@` chains total
- All intermediate language semantics are parameterized by `vote_type` via `VoteSemantics` typeclass (wrap definitions in `Section VOTE. Context {VT: vote_type} {vsem: VoteSemantics VT}. ... End VOTE.`)
- `TransfLink` typeclass ensures passes preserve separate compilation/linking

### OCaml Side

- `driver/Driver.ml` - Main entry point; runs color checker on intermediate RTL before final asm compilation
- `extraction/extraction.v` - Wires `RTLinfercolor.infer_coloring` to `RTLcolorcheck.infer_coloring` axiom
- `Makefile.extr` - Post-extraction OCaml build (produces `ccomp`, `clightgen`, `vcomp`)
- Architecture-specific extracted code in `x86/extractionMachdep.v`

## Coq Version and Dependencies

- Current config: x86_64-linux, gcc toolchain
- Uses local copies of Flocq (floating-point) and MenhirLib (parser)
- Coq project file: `_CoqProject` (includes `-R` flags for all directories)
- OPAM switch: `4.14.2` (OCaml)
