# Coding Conventions

**Analysis Date:** 2026-03-14

## Naming Patterns

### Files

**Coq (`.v`) files:**
- **Proofs:** Paired naming: semantic definition in `X.v`, proof in `Xproof.v`
  - Example: `RTL.v` (semantics) paired with `RTLfault.v` (extension) and `RTLfaultproof.v` (proof)
  - Example: `RTLtmr.v` (transformation) paired with `RTLtmrproof.v` (preservation proof)
- **Color system:** Related files prefixed with color concept
  - `RTLcolor.v` - declarative specification
  - `RTLcolorcheck.v` - boolean checker
  - `RTLinfercolor.ml` - OCaml oracle implementation
- **Architecture-specific:** Suffixed with architecture name
  - `backend/x86/Asm.v`, `backend/x86/Asmgen.v`
  - `backend/aarch64/Asm.v`, `backend/aarch64/Conventions1.v`
  - `extraction/x86/extractionMachdep.v`

**OCaml (`.ml` / `.mli`) files:**
- **Print utilities:** `Print{Language}.ml` for pretty-printing
  - `PrintAsm.ml`, `PrintCminor.ml`, `PrintRTL.ml`, `PrintLTL.ml`
- **Auxiliary implementations:** `{Module}aux.ml` for helper functions
  - `Asmexpandaux.ml`, `RTLgenaux.ml`, `Linearizeaux.ml`, `Selectionaux.ml`
- **Transformation pass:** `{Pass}.ml` directly implements the pass logic
  - `Regalloc.ml`, `IRC.ml`, `Inliningaux.ml`

### Functions

**Coq (pure logical definitions):**
- **Predicates:** CamelCase with context-sensitive suffixes
  - `val_compat` (value compatibility)
  - `match_rs` (register set matching)
  - `not_regular_state` (state classification)
  - `is_basic` (property check)
  - Suffixed `_upto` for weakened versions: `match_rs_upto`
- **Definitions:** lowercase_with_underscores
  - `zap_allowed`, `rs_compat`, `faulty_semantics`
- **Conversion functions:** `{type}_of_{type}` or `{action}_{type}`
  - `color_of_uf_node`, `convert_positive`, `convert_instr`
  - `smove_int_sem`, `maj_vote_sig_of_typ`

**Coq (proof-level):**
- **Lemmas/Theorems:** CamelCase
  - `val_compat_refl`, `val_compat_trans`, `val_lessdef_compat`
  - `match_rs_weaken`, `match_rs_color_weaken`
- **Constructor names:** CamelCase with inductive type prefix
  - `val_compat_undef`, `val_compat_int`, `val_compat_ptr`
  - `maybe_zap_refl`, `maybe_zap_reg`
  - `is_basic_red`, `is_basic_green`, `is_basic_blue`

**OCaml:**
- **Functions:** lowercase_with_underscores
  - `make`, `find`, `union`, `eq`
  - `convert_positive`, `convert_instr`, `get`
  - `instr_constraints`, `function_constraints`, `infer_coloring`
- **Pattern matching helpers:** Action_Type or object_action
  - `regs_of_builtin_res`, `regs_of_builtin_arg`
  - `string_of_uf_node`, `string_of_positive`
- **Record field access:** lowercase in record definition, accessed via dot notation
  - `{ mutable parent : uf_node; mutable rank : int }`

### Variables

**Coq (theorem statements):**
- **Single-letter or meaningful abbreviations:**
  - Type/semantic elements: `A`, `B` (types in generics)
  - Registers: `r`, `r1`, `r2`, `r3`, `res` (result register)
  - Register sets: `rs`, `rs1`, `rs2` (register state)
  - Colors: `c`, `col` (color function mapping registers to colors)
  - State components: `stk` (stack), `sp` (stack pointer), `pc` (program counter), `m` (memory)
  - Function: `f` (RTL function)
  - Global environment: `ge` (global environment)
  - Booleans: `b`, `faulted`, `fault`
  - Live sets: `live`, `s1`, `s2` (register sets), `s_mid` (intermediate)
  - Instructions: `instr`, `i`, `ni` (node+instruction pair)
  - Traces: `t` (execution trace)

**OCaml:**
- **Per-node state:** `cols` (array of color hashtables per node)
- **Union-find nodes:** `n`, `node1`, `node2`, `root1`, `root2`
- **Registers:** `r`, `args`, `src`, `res` (result), `regs`
- **Hashtables:** `col` (current node's color mapping)
- **Functions:** `f` (Coq function), `func` or `fn` (OCaml function)

### Types

**Coq:**
- **Inductive type names:** CamelCase
  - Color system: `color` (inductive), `is_basic` (predicate), `is_color` (notation)
  - Semantics: `fstate` (faulty state record), `fstep` (faulty step relation)
  - Instructions: `instruction`, `maybe_zap` (zapping relation)
  - Values: `val_compat` (compatibility relation)
  - States: `not_regular_state` (classification)
- **Record type names:** lowercase
  - `fstate` - record with `fs_state` and `fault` fields

**OCaml:**
- **Type aliases:** lowercase or with prime suffix
  - `instruction'` (converted instruction with int registers instead of positives)
  - `uf_node` (union-find node with mutable parent/rank)

## Code Style

### Formatting

**Coq:**
- **Indentation:** 2 spaces
- **Import blocks:** Grouped at top of file, each import on separate line
  ```coq
  Require Import
    AST
    Builtins2
    Coqlib
    Events
    ...
  ```
- **Local scope declarations:** Grouped near imports
  ```coq
  Import ListNotations.
  Local Open Scope string_scope.
  ```

**OCaml:**
- **Indentation:** 2 spaces
- **Type annotations:** Present on function signatures
  ```ocaml
  let convert_positive (p : positive) : positive = ...
  let get (col : (int, uf_node) Hashtbl.t) (r : int) : uf_node = ...
  ```
- **Operator precedence:** Uses `@@` (function application) and `@` (list append)
  - `string_of_int @@ int_of_positive p` for chained calls
  - List.map and List.fold with function arguments

### Linting

**Configuration:** No `.eslintrc` or style checker detected. Code follows CompCert conventions.

**Key style observations:**
- Coq: Heavy use of `match`/`destruct` for case analysis; `Proof` blocks use tactic style
- OCaml: Mutable state used explicitly (`mutable` keyword); imperative style with hash tables

## Import Organization

**Coq (`.v` files):**

Order:
1. Base Coq imports: `From Coq Require Import`, `From MenhirLib Require Import`
2. CompCert library utilities: `Require Import Coqlib`, `Maps`, `Integers`
3. Common CompCert infrastructure: `AST`, `Values`, `Memory`, `Globalenvs`, `Smallstep`, `Behaviors`, `Events`, `Linking`
4. Current compilation target: `RTL`, `Asm`, `Clight`, `Csyntax`
5. Domain-specific imports: `Builtins2`, `Registers`, `ProofLiveness`, `Op`
6. Related passes/proofs: `RTLtmr`, `RTLfault`, `RTLcolorcheck`, `RTLtolerant`
7. Extensions/utilities: `Novotes`, `RTLagreement`, `Asmagreement`

**Pattern:** `Require Import` for standard/CompCert modules, `Require` for architecture-specific or extension modules

**Scopes:**
- `Local Open Scope string_scope` - for string literals in definitions (e.g., builtin names)
- `Local Open Scope color_scope` - for infix operators like `=?`
- `Local Open Scope error_monad_scope` - for `do` notation and `@@` bind operators
- `Import ListNotations` - for list syntax `[a; b; c]`

**OCaml (`.ml` files):**

Order:
1. Coq-generated modules: `open AST`, `open BinNums`, `open Datatypes`
2. CompCert library: `open Maps`, `open Registers`, `open RTL`
3. Domain modules: `open Op`, `open RTLcolor`

## Error Handling

**Coq:**

**Pattern: Result type (`res` monad)**
- Use `res A` for operations that may fail
- Definition in `common/Errors.v`: `Inductive res (A: Type) := OK: A -> res A | Error: errmsg -> res A`
- Error messages: `MSG "description"`, `CTX positive` (context), `POS positive` (position)
- Monadic bind: `bind` and `bind2` functions
- Syntactic sugar: `do` notation (imported from `error_monad_scope`)
  ```coq
  do x <- f; g x  (* equivalent to bind f (fun x => g x) *)
  do (x, y) <- f; g x y  (* equivalent to bind2 f (fun x y => g x y) *)
  ```

**Pattern: Proof assertions**
- `Defined` for transparent proofs (computational content needed)
- `Qed` for opaque proofs (proof irrelevant)
- Use `inv H` tactic macro (from Coqlib) for inversion with immediate substitution
- `destruct` with pattern guards for exhaustive case analysis

**OCaml:**

**Pattern: Exception-based error handling**
```ocaml
exception ColorError of string

let positive_of_int (i : int) : positive =
  if i < 1 then
    raise (ColorError ("positive_of_int: int must be positive, got " ^ string_of_int i))
  else ...
```

**Pattern: Option type**
- `Option.find_opt` for querying hashtables
- `match ... with | Some v -> v | None -> default`
- Functions return `option` type for optional results: `match green_smove_sig_of_typ ty with | None => None | Some (nm, kind) => ...`

## Logging

**Framework:** No structured logging framework. Uses:
- `print_string`, `print_newline` for debug output
- `Printf.sprintf` or string concatenation for formatting

**Patterns in RTLinfercolor.ml:**
```ocaml
let print_col (col : (int, uf_node) Hashtbl.t) : unit =
  Hashtbl.iter (fun r c ->
      print_string @@ "x" ^ string_of_int r ^ "=" ^ string_of_uf_node c ^ ", "
    ) col;
  print_newline ()
```

**No structured logging in Coq** - proofs are checked at compile time.

## Comments

**Coq:**

**Style:**
- Block comments: `(* Text *)` for multi-line explanations
- Markdown documentation: `(** Documentation *)` for items exported in documentation
- Inline tactical comments: inline within proofs with `(*` `*)`

**When to comment:**
1. **Before definitions:** Explain semantic meaning or proof strategy
   - `(* Technically we could/should allow faults (and not vote on) on most builtins... *)`
   - `(** Generate fault-tolerant instruction sequence corresponding to the input instruction... *)`
2. **Before lemmas:** State the lemma's role in the proof
   - `(** When a fault has occurred elsewhere and regsets remain unchanged, they still match. *)`
3. **At section boundaries:** Mark proof scope changes
   - `Section RELSEM. ... End RELSEM.`
   - `(** Pure val_compat lemmas (no global environment dependency) *)`
4. **In complex proofs:** Explain proof structure with intermediate comments

**OCaml:**

**Style:**
- Brief inline comments for logic: `(* Path compression *)`
- Summary comments for complex algorithms:
  ```ocaml
  (* Union-find version, with liveness bounded quantification and sparse
     colorings (hash tables).

     At a high level, the algorithm builds a set of equality constraints
     between register colors at RTL program points... *)
  ```

## Function Design

**Size:** No explicit line limit enforced. Observe actual functions:
- **Coq:** Lemmas typically 5-30 lines (proofs), definitions often inline match expressions
- **OCaml:** Functions 10-50 lines, with recursive functions using pattern matching

**Parameters:**
- **Coq:** Implicit arguments via `{}` in type signatures; explicit with `@`
- **OCaml:** Type annotations on parameters; uses currying for partial application

**Return Values:**
- **Coq:** Every definition has explicit return type; lemmas conclude with `Prop`
- **OCaml:** Explicit return type in signature; uses `option` for optional results and `res` (from Coq) for error propagation

## Module Design

**Exports:**
- **Coq:** All `Definition`, `Lemma`, `Theorem` items are exported by default
- **OCaml:** `.mli` files define interface; `.ml` implementations must match

**Barrel Files:** Not used. Each module is a single `.v` or `.ml` file.

**Parameterization:** Coq uses `Section` and `Context` for parameter binding:
```coq
Section VOTE.
  Context {VT: vote_type} {vsem: VoteSemantics VT}.
  (* Definitions parameterized by vote_type *)
End VOTE.
```

---

*Convention analysis: 2026-03-14*
