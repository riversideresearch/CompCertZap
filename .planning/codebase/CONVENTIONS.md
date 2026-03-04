# Coding Conventions

**Analysis Date:** 2026-03-04

## Language Overview

CompCert spans two distinct language ecosystems:
- **Coq** (~278 `.v` files) - Formal proofs and intermediate languages (lib, common, backend, cfrontend, driver, cparser)
- **OCaml** (~60 `.ml` files) - Runtime extraction, parsing, code generation, and oracle implementations

Each follows its respective language conventions while maintaining interoperability through `extraction.v`.

## Coq Conventions

### File Organization and Naming

**Files:**
- Definition files: `[Language].v` (e.g., `RTL.v`, `Clight.v`)
- Proof files: `[Component]proof.v` (e.g., `RTLtmrproof.v`, `Stackingproof.v`)
- Specification files: `[Component]spec.v` (e.g., `RTLtmrspec.v`)
- Color system: `[Component]color*.v` (e.g., `RTLcolor.v`, `RTLcolorcheck.v`)

**Location patterns:**
- Core definitions: `backend/[Language].v`, `common/[Language].v`
- Proofs with definitions: Keep in same directory as corresponding proof file
- Architecture-specific: `x86/`, `aarch64/`, `arm/` directories

### Import Organization

**Standard import blocks** (see `backend/RTLtmrproof.v` lines 1-7):

```coq
Require Import
  AST
  Builtins2
  Coqlib
  Events
  Globalenvs
  Integers
  Linking
  Maps
  Op
  Registers
  RTL
  RTLcolor
  RTLfault
  Smallstep
  Values
.
```

**Pattern:**
1. Core modules first (AST, Coqlib, Events, Values)
2. Standard data structures (Maps, Integers, Globalenvs)
3. Domain-specific modules (RTL, RTLcolor, RTLfault)
4. Import statement on separate line
5. One module per line, ordered alphabetically within groups

**Post-import declarations** (see `common/Errors.v` line 22):
- `Close Scope [scope]` after imports if needed
- `Set Implicit Arguments` before significant definitions
- `Open Scope` localized to sections requiring specific scope

### Section and Context Structure

**Pattern** (see `backend/RTLtmrproof.v` lines 14-16):

```coq
Section VOTE.
Context {VT: Builtins2.vote_type} {vsem: Builtins2.VoteSemantics VT}.

  Section PRESERVATION.
    Variable prog: program.
    Variable tprog: program.
    Hypothesis TRANSF: match_prog prog tprog.

    (* Nested lemmas and definitions *)
  End PRESERVATION.

End VOTE.
```

**Conventions:**
- Outer sections: capitalized names (`VOTE`, `PRESERVATION`)
- Context parameters: `{VT: vote_type} {vsem: VoteSemantics VT}` for parameterization over voting semantics
- Variables: lower_case (e.g., `prog`, `tprog`, `ge`, `tge`)
- Hypotheses: UPPER_CASE (e.g., `TRANSF`, `WT_FN`, `REGS`)
- Lemmas in sections can reference section variables without explicit parameters

### Naming Conventions

**Types and Constructors:**
- Inductive types: CamelCase (e.g., `color`, `instruction`, `match_states`)
- Constructors: Leading capital (e.g., `Red`, `Green`, `Iop`, `Icall`)
- Option types: Implicit in name (e.g., `Some`, `None`)

**Functions and Predicates:**
- Definitions: snake_case (e.g., `maj_vote`, `match_regsets`, `eval_addressing`)
- Helper predicates: snake_case with `_` (e.g., `is_basic`, `reg_used`, `wt_function`)
- Lemmas/theorems: snake_case (e.g., `rm_wf_neq_2_3`, `match_regsets_eval_addressing`)

**Variables in Proofs:**
- Hypothesis names: UPPER_CASE prefix (e.g., `WT_FN`, `REGS`, `STACKS`, `STK`)
- Generated variables: lower_case or pattern-bound (e.g., `x`, `s`, `i1`, `EQ`)
- Register names: `r1`, `r2`, `r3` for shadow copies in TMR context
- Register maps: `rm` (replication map), `re` (register environment)

**Equation Names:**
- Monad inversion: `EQ1`, `EQ2` (see `backend/Inliningspec.v` lines 144-145)
- Case analysis: `H`, `H0`, `H1` in sequence

### Proof Structure Conventions

**Proof organization** (see `backend/RTLtmrproof.v` lines 206-215):

```coq
Lemma lemma_name (params) : statement.
Proof.
  intros. (* Pattern match on goals *)
  destruct (peq r1 r1'); subst.
  - (* Subcase 1: r1 = r1' *)
    rewrite Hr1 in Hr1'; inv Hr1'.
    eapply rm_wf_neq_2_3; eauto.
  - (* Subcase 2: r1 <> r1' *)
    specialize (Hwf r1 r2 r3 Hn Hr1).
    destruct Hwf as [Hnodup Hwf].
    specialize (Hwf r1' r1 r3' Hn' n Hr1').
    inv Hwf; apply H1; right; right; right; left; reflexivity.
Qed.
```

**Patterns:**
- Start with `intros` to introduce hypotheses
- Use `destruct` for case analysis with inline comments (e.g., `(* Subcase 2: ... *)`)
- Subgoals marked with `-` and `+` for binary splits
- Reuse tactics: `inv H`, `subst`, `eauto`, `reflexivity`
- Chain reasoning with semicolons: `intro; destruct`

**Tactic conventions:**
- `inv H` - inversion with automatic substitution (defined in `lib/Coqlib.v` line 25)
- `monadInv H` - for result monad inversion (see `backend/Inliningspec.v` lines 151-171)
- `exploit` - for forward application (defined in `lib/Coqlib.v` lines 48-80)
- `eauto`, `auto` - for automation with explicit context
- `lia` - linear integer arithmetic
- `extlia` - extended linear integer arithmetic
- `congruence` - for equality reasoning

### Comment Conventions

**Documentation comments:**

```coq
(** * Section title *)

(** ** Subsection title *)

(** The color of a register isn't necessarily the same at all points
    in a function. White is a temporary color that gets reset to red
    after a use (or pink then red in the case of smoves). So, red
    registers are variously red or white/pink throughout the function,
    but green and blue registers stay green and blue respectively
    (unless they are reused with a different color by assigning to
    them the result of a differently-colored computation). *)
```

**Patterns:**
- Section headers: `(** * Title *)` for major sections
- Subsection headers: `(** ** Title *)`
- Documentation: Block comments `(** ... *)` above definitions
- Inline comments: Line comments with `(*` and `*)` for clarifications

**When to comment:**
- Non-obvious function purposes (see `backend/RTLcolor.v` lines 21-27)
- Complex invariant definitions (see `backend/RTLtmrproof.v` lines 31-48)
- Proof strategy for complex cases
- Do NOT comment obvious patterns (e.g., list destructuring)

### Error Handling

**Result monad** (see `common/Errors.v` lines 47-49):

```coq
Inductive res (A: Type) : Type :=
| OK: A -> res A
| Error: errmsg -> res A.
```

**Monadic operations:**
- `do X <- A ; B` notation for sequential composition
- `bind f g` for function chaining
- `@@@` operator chains partial results (error monad)
- `@@` operator chains total functions

**Error construction:**
```coq
error (MSG "message" :: POS pc :: nil)
```

**Patterns in TMR context** (see `backend/RTLtmr.v` lines 110-112):
- Errors for unexpected types: `error (MSG "Replicate.v:maj_vote: unexpected Tany32 or Tany64")`
- Include position information: `:: POS pc ::`
- Reserve and update instructions: `do succ <- reserve_instr`

## OCaml Conventions

### File Organization

**Files by purpose:**
- Main entry point: `driver/Driver.ml` (lines 41-87 for compilation)
- Extracted verified code: `extraction/` directory (auto-generated from Coq)
- Unverified oracles: `backend/RTLinfercolor.ml` (color inference)
- Architecture support: `x86/`, `aarch64/` directories with TargetPrinter, Asmexpand, etc.
- Parsing: `cparser/` with Lexer.mll, Parser.mly (Menhir-based)

### Import Style

**Pattern** (see `backend/RTLinfercolor.ml` lines 1-8):

```ocaml
open AST
open BinNums
open Datatypes
open Maps
open Op
open Registers
open RTL
open RTLcolor
```

**Conventions:**
- Use `open` for extracted modules and standard imports
- Qualifyfor clarity if ambiguous
- No explicit `(* ... *)` comments in extracted files (from Coq)
- Newline after imports before type definitions

### Naming Conventions

**Functions:**
- snake_case for all functions (e.g., `int_of_positive`, `convert_positive`, `find node`)
- Single-letter variables in tight loops acceptable (e.g., `i`, `j`)
- Descriptive names for utility functions: `string_of_positive`, `convert_positive`

**Types:**
- Type aliases: snake_case (e.g., `uf_node`, `instruction'`)
- Record fields: snake_case (e.g., `mutable parent`, `mutable rank`)

**Pattern matching:**
- Inline for single-case patterns (see `backend/RTLinfercolor.ml` lines 127-133)
- Multi-line for complex cases (see `backend/RTLinfercolor.ml` lines 197-214)

### Code Style

**String operations:**
```ocaml
let string_of_positive p = string_of_int @@ int_of_positive p
```

**Patterns:**
- Pipe operator `|>` or `@@` for function composition
- Pattern matching with `function` keyword for single argument
- Guards with `if` in match expressions
- Mutable state only where necessary (union-find `parent` and `rank`)

**Comments:**
- Explain non-obvious algorithms (see `backend/RTLinfercolor.ml` lines 56-64 union-find)
- Mark copy/pasted code (see `backend/RTLinfercolor.ml` line 44)
- Document exceptions (see `backend/RTLinfercolor.ml` line 17)

### Exception Handling

**Custom exceptions:**
```ocaml
exception ColorError of string

let rec go (j : int) : positive =
  if j == 1 then
    Coq_xH
  else if j mod 2 == 0 then
    Coq_xO (go @@ j / 2)
  else
    Coq_xI (go @@ j / 2)
```

**Patterns:**
- Raise on invalid input (e.g., negative integers for positive_of_int)
- Use result patterns in extracted code when possible
- Exceptions primarily in oracle implementations

### Union-Find Implementation

**Data structure** (see `backend/RTLinfercolor.ml` lines 46-79):

```ocaml
type uf_node = {
    mutable parent : uf_node;
    mutable rank : int;
  }

let make () =
  let rec node = { parent = node; rank = 0 } in
  node

let rec find node =
  if node.parent == node then
    node
  else begin
      node.parent <- find node.parent; (* Path compression *)
      node.parent
    end

let union node1 node2 =
  let root1 = find node1 in
  let root2 = find node2 in
  if root1 != root2 then begin
      if root1.rank < root2.rank then
        root1.parent <- root2
      else if root1.rank > root2.rank then
        root2.parent <- root1
      else begin
          root2.parent <- root1;
          root1.rank <- root1.rank + 1
        end
    end
```

**Conventions:**
- Immutable self-referential node creation for roots
- Path compression in `find` operation
- Union by rank for efficiency
- Physical equality `==` for union-find node comparison

## Cross-Language Conventions

### Semantic Parameterization

**Vote type abstraction** (see `backend/RTLtmrproof.v` lines 14-15):

```coq
Section VOTE.
Context {VT: Builtins2.vote_type} {vsem: Builtins2.VoteSemantics VT}.
```

**Pattern:**
- Parameterize proof modules over `vote_type` (Two or Three voting)
- Use `VoteSemantics` typeclass for semantics
- Enables reuse for DMR (Two) and TMR (Three) without code duplication
- Extracted oracle must implement matching interface

### Translation Correspondence

**Proof organization** (see `backend/RTLtmrproof.v` lines 20-24):

```coq
Definition match_prog (prog tprog: program) :=
  match_program (fun cu f tf => transf_fundef f = OK tf) eq prog tprog.

Lemma transf_program_match:
  forall prog tprog, transf_program prog = OK tprog -> match_prog prog tprog.
Proof.
  intros. eapply match_transform_partial_program_contextual; eauto.
Qed.
```

**Patterns:**
- Every transformation has a `transf_*` function
- Every transformation has a corresponding `match_prog` relation
- Forward/backward simulation lemmas establish semantic preservation
- Linking support through `TransfLink` typeclass

### Build Integration

**Makefile targets:**
- `make proof` - Compile all `.v` files
- `make extraction` - Extract verified OCaml from Coq
- `make ccomp` - Build final OCaml binary
- `make clean` / `make cleanall` - Remove artifacts

**Extraction directive** (see `extraction/extraction.v`):
- Wires `RTLinfercolor.infer_coloring` to `RTLcolorcheck.infer_coloring`
- Axiom in Coq proof, oracle implementation in OCaml
- Post-extraction Makefile handles OCaml compilation

---

*Convention analysis: 2026-03-04*
