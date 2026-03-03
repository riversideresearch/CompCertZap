# Coding Conventions

**Analysis Date:** 2026-03-03

## Naming Patterns

**Files:**
- Coq proofs: PascalCase with `.v` extension: `RTLfault.v`, `RTLcolorcheck.v`, `RTLdmrproof.v`
- OCaml source: snake_case with `.ml` extension: `rtlinfercolor.ml`, `driver.ml`
- OCaml interfaces: `.mli` extension (e.g., `Debug.mli`, `Dwarfgen.mli`)
- Proof files follow pattern: `[Component].v` for spec, `[Component]proof.v` for proofs (e.g., `RTLdmr.v` → `RTLdmrproof.v`)

**Functions:**
- **Coq**: snake_case for predicates and inductives, CamelCase for lemmas/theorems
  - Examples: `match_states`, `val_compat_refl`, `find_funct_ptr_wc_fundef` in `RTLtolerant.v`
  - Proof-related: `Lemma`, `Theorem` keywords always capitalized
  - Predicates use lowercase: `val_compat`, `maybe_zap`, `wc_program`, `wc_function`, `match_regsets` (from `RTLtolerant.v`, `RTLfault.v`)
- **OCaml**: snake_case for functions and values
  - Examples: `convert_positive`, `find`, `union`, `fresh`, `regs_of_function` in `RTLinfercolor.ml`
  - Union-find primitives: `make`, `find`, `union`, `eq` (concise names for core algorithms)
  - Helper functions: `int_of_positive`, `positive_of_int`, `string_of_uf_node` (semantic naming showing transformation direction)

**Variables:**
- **Coq**: Lowercase with semantic names: `rs` (regset), `m` (memory), `f`/`fd` (function/fundef), `col` (coloring), `stk` (stack), `pc` (program counter), `pc'` (successor PC)
- **OCaml**: Abbreviated or semantic: `r` (register), `c` (color), `p` (positive integer), `rs` (register state)

**Types:**
- **Coq**: PascalCase for inductives: `val_compat`, `color`, `fstate` (record with `fs_state`, `fault` fields), `fstep` (inductive for faulty step)
- **OCaml**: PascalCase for types: `uf_node`, `instruction'` (machine-integer variant of instruction)
- Color values: `Red`, `Green`, `Blue`, `White`, `Pink` (capitalized)

## Code Style

**Formatting:**
- No explicit formatter configured. Code follows traditional Coq/OCaml styles.
- Indentation: Coq proofs use 2-space indentation in most cases
- OCaml uses standard formatting with 2-space indentation

**Linting:**
- No ESLint or Prettier setup (not a JavaScript project)
- Coq uses built-in checker via `coqc` with warnings configured in `Makefile` (e.g., `-w -unused-pattern-matching-variable`)
- OCaml code compiled with standard `ocamlopt` warnings enabled during build

## Import Organization

**Order (Coq):**
1. Standard library imports: `From Coq Require` (e.g., `From Coq Require Export String ZArith Znumtheory List Bool Lia`)
2. Local module imports: `Require Import` for same-project dependencies
3. Specific imports grouped logically

**Example from `RTLfault.v`:**
```coq
Require Import
  AST
  Builtins2
  Coqlib
  Events
  Globalenvs
  Integers
  Maps
  Memory
  Op
  Registers
  RTL
  Smallstep
  Values
.
```

**Example from `RTLtolerant.v`:**
```coq
Require Import
  AST
  Behaviors
  Builtins2
  Coqlib
  Events
  Globalenvs
  Linking
  Maps
  Registers
  RTLtmr
  RTLtmrspec
  RTL
  RTLcolor
  RTLfault
  Smallstep
  Values
.

Import ListNotations.
Local Open Scope string_scope.
```

**Path Aliases:**
- No explicit alias system used. All imports qualified by module path (e.g., `Memory.Mem.extends`, `RTL.step`)
- Some files open scopes locally: `Local Open Scope string_scope.` (for RTL/color names) or `Local Open Scope positive_scope.`

**Order (OCaml):**
1. Standard library/Batteries modules: `open Printf`, `open Str`
2. Local application modules: `open Clflags`, `open Driveraux`, `open Frontend`
3. Imported submodules and opened namespaces clearly listed

**Example from `Driver.ml`:**
```ocaml
open Printf
open Commandline
open Clflags
open CommonOptions
open Timing
open Driveraux
open Frontend
```

## Error Handling

**Patterns:**
- **Coq**: Uses `res` type (Result monad) defined in `Errors.v`
  - Chains errors with `@@@` (operator for binding partial functions): composition of monadic operations
  - Example use: `transf_c_program_to_rtl` returns `res program`
  - No exceptions in verified code; errors propagated as values
- **OCaml**: Exceptions for non-recoverable errors, `Result` type for computational failures
  - `ColorError` exception raised in `RTLinfercolor.ml` for invalid color operations
  - Explicit error handling in driver with `match Compiler.transf_c_program_to_rtl csyntax with | Errors.OK ... | Errors.Error ...` pattern in `Driver.ml`

**Proof by contradiction:**
- Tactic `byContradiction` defined in `Coqlib.v` as `exfalso`
- Used for proofs ending in contradiction, though most proofs are constructive

## Logging

**Framework:** Console output via standard Coq/OCaml I/O
- **Coq**: Limited use of `print_string` within proofs; mostly logging in OCaml side
- **OCaml**: `Printf.printf` and `print_endline` for logging during compilation
  - Example from `RTLinfercolor.ml`: `print_endline @@ "RTL program is well-colored :)"` in `Driver.ml` line 64
  - Debug output: `print_col` and `print_cols` functions (can be enabled with `print_endline` directives)

**Patterns:**
- Informational messages at key stages: parsing, translation, color checking
- Error messages printed to stderr via standard error reporting
- Timing information logged if enabled via `Timing` module in `Driver.ml`

## Comments

**When to Comment:**
- Proofs generally avoid comments; tactics explain themselves
- OCaml code includes file headers with copyright/license (CompCert standard)
- Critical algorithm explanations in docstrings (e.g., DMR replication strategy in `RTLdmr.v` lines 1-16)
- Complex invariants documented at point of definition
- Example from `RTLinfercolor.ml` line 12: `(* This file provides an implementation of the color inference oracle declared in Colorcheck.v with the following type: *)`

**JSDoc/TSDoc:**
- Coq: Uses `(** ... *)` documentation comments for definitions
  - Example: `(** The color of a register isn't necessarily the same at all points in a function. ... *)` in `RTLcolor.v`
- OCaml: Minimal formal documentation; relies on clear naming and type signatures
- No automated documentation generation system (no Odoc setup visible)

## Function Design

**Size:**
- Coq lemmas/theorems: Brief, focused on single properties. Examples:
  - `val_compat_refl`: 2 lines of proof
  - `wc_col_succ_exists`: ~12 lines of proof with clear case analysis
  - Larger proofs factored into multiple lemmas (e.g., `maybe_zap_preserves_match_states` is ~30 lines with clear structure in `RTLtolerant.v`)
- OCaml functions: Medium size with clear purposes
  - `convert_instr`: ~30 lines for comprehensive instruction conversion
  - Union-find primitives: 1-5 lines for atomic operations
  - Inference: ~500+ lines spread across multiple functions with state monad

**Parameters:**
- **Coq**: Heavy use of implicit arguments (curly braces) to reduce boilerplate
  - Example: `Lemma val_compat_trans (v1 v2 v3 : val)` takes explicit values, implicit universe levels
  - `match_states` predicate takes bool for fault flag, two RTL.state variants
- **OCaml**: Explicit parameters, sometimes using labeled arguments
  - Union-find: node operations take nodes as explicit parameters
  - Color conversion: `convert_positive : int -> positive` (explicit conversion direction)

**Return Values:**
- **Coq**: Proofs return propositions (Prop); constructive proofs build witnesses
  - Lemmas structured to extract computational content when needed
  - Match relations return `Prop` but can be refined to `sigT` when need computational witness
- **OCaml**: Return option types, result types, or unit for side effects
  - `infer_coloring : function -> option (node -> PTree.t color)` (may fail)
  - `convert_positive : int -> positive` (no option; raises exception on invalid input per design)
  - Imperative updates to mutable union-find nodes

## Module Design

**Exports:**
- **Coq**: Files are modules; all definitions visible unless shadowed
  - Core definitions exported implicitly; parameter axioms (like `infer_coloring` in `RTLcolorcheck.v` line 73) are declared as `Parameter` for linking with unverified implementations
  - `Section` mechanism groups related definitions with shared context (e.g., `Section VOTE` in `RTLdmrproof.v`)
- **OCaml**: `.mli` interface files control exports
  - Example: `Debug.mli` exposes minimal interface
  - No module functors visible in core compiler (though Menhir generates some)

**Barrel Files:**
- Not used; each file is a single module with specific responsibility
- Compound names like `RTLdmr.v` (specification) + `RTLdmrproof.v` (proof) kept separate to allow independent consumption
- `Builtins2.v` extends builtins with fault tolerance specifics (vote type, vote semantics typeclass)

## Sections and Contexts (Coq-specific)

**Pattern:**
- `Section [Name]` establishes shared context (variables, hypotheses)
- Closed with `End [Name]`
- Used heavily for parameterizing proofs over general vote type: `Section VOTE. Context {VT: vote_type} {vsem: VoteSemantics VT}.`
- Example in `RTLtolerant.v`: `Section match_states` contains match relation definitions, closed with `End match_states`
- Proof section: `Section PRESERVATION` contains lemmas about symbol preservation, function translation assuming hypothesis `TRANSF: match_prog prog tprog`

## Error Type Pattern

- All compiler passes return `res` (Result type): `res_type` = `OK value | Error message_string`
- Monadic composition via `bind` (`@@` operator) for total functions, `@@@` for partial
- Examples: `transf_fundef`, `transf_program` return `res [fundef|program]`
- Critical for separate compilation: `TransfLink` typeclass ensures passes preserve linking properties

---

*Convention analysis: 2026-03-03*
