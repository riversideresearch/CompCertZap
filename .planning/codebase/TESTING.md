# Testing Patterns

**Analysis Date:** 2026-03-03

## Test Framework

**Framework:**
- **Coq Proofs as Primary Verification**: Semantic preservation proofs serve as the main correctness validation
- All intermediate language transformations proven to preserve meaning via simulation lemmas
- No traditional unit test framework (Jest, Vitest, etc.) - not a JavaScript/TypeScript project

**Assertion Library:**
- Coq's built-in `Require` and proof tactics: `intro`, `apply`, `rewrite`, `simpa`, `omega`, `lia`
- Auxiliary tactics in `lib/Coqlib.v`: `inv` (inversion), `exploit` (exploit modus ponens), `predSpec`, `caseEq`, `destructEq`
- Manual assertion patterns via `Lemma ... : Prop` statements

**Run Commands:**
```bash
make proof                  # Compile all .v files to .vo (full proof checking, slow)
make backend/RTLtolerant.vo # Verify specific file and dependencies
make extraction            # Extract Coq to OCaml (requires proof)
make ccomp                 # Build compiler binary (includes OCaml build)
make check-admitted        # Ensure no unproven Admitted statements
make check-proof           # Verify semantic preservation properties
```

## Test File Organization

**Location:**
- **Proof files embedded in source**: No separate test directory
- Each compiler pass has companion proof file:
  - `backend/RTLdmr.v` (transformation spec) → `backend/RTLdmrproof.v` (correctness proof)
  - `backend/RTLcolor.v` (color spec) → `backend/RTLcolorcheck.v` (verified checker)
- Main theorem linking all passes: `driver/Complements.v` contains `transf_c_program_to_rtl_preservation_faulty`

**Naming:**
- Specification files: `[Component].v`
- Proof files: `[Component]proof.v`
- Core semantics files: `[Component].v`
- Example: `backend/RTLfault.v` defines faulty semantics; linked to tolerance proof in `backend/RTLtolerant.v`

**Structure:**
```
lib/                          # Utilities and basic lemmas
├── Coqlib.v                 # Tactics (inv, exploit) and library lemmas
├── Maps.v                   # Tree maps and functional data structures
└── UnionFind.v              # (if exists) Union-find data structure

backend/                      # Compiler backend and fault tolerance
├── RTL.v                    # Base RTL language semantics
├── RTLfault.v              # Faulty RTL semantics (maybe_zap model)
├── RTLcolor.v              # Color spec (Red/Green/Blue/White/Pink)
├── RTLcolorcheck.v         # Verified color checker (Parameter infer_coloring)
├── RTLinfercolor.ml         # Unverified OCaml color inference (union-find)
├── RTLdmr.v                # DMR replication transformation
├── RTLdmrproof.v           # DMR correctness proof (forward simulation)
├── RTLtmr.v                # TMR replication transformation
├── RTLtmrproof.v           # TMR correctness proof
├── RTLtolerant.v           # Backward simulation: 3-voting non-faulty >= 2-voting faulty
├── RTLagreement.v          # Weak agreement definition
└── Novotes.v               # Checker: program contains no vote builtins pre-TMR

driver/
├── Complements.v           # Main theorem: transf_c_program_to_rtl_preservation_faulty
└── Driver.ml               # Pipeline: parse → translate → color check → asm gen
```

## Test Structure

**Suite Organization:**

Proofs organized by semantic refinement level:

```
Proof (C semantics >= 2-voting RTL without replication)
  ↓ (monadic composition of passes, each with simulation)
Proof (2-voting RTL no replication >= 3-voting RTL no replication)
  ↓ (weak agreement - trivial from no-vote checker)
Proof (3-voting RTL >= 3-voting RTL with TMR)
  ↓ (forward simulation in RTLtmrproof.v)
Proof (3-voting RTL+TMR >= 2-voting faulty RTL+TMR)
  ↓ (backward simulation in RTLtolerant.v, requires well-coloring)
QED main theorem
```

**Example from `RTLdmrproof.v` lines 1-100:**

```coq
(** * Forward simulation proof for DMR pass. *)

Section VOTE.
Context {VT: Builtins2.vote_type} {vsem: Builtins2.VoteSemantics VT}.

Definition match_prog (prog tprog: program) :=
  match_program (fun cu f tf => transf_fundef f = OK tf) eq prog tprog.

Lemma transf_program_match:
  forall prog tprog, transf_program prog = OK tprog -> match_prog prog tprog.
Proof.
  intros. eapply match_transform_partial_program_contextual; eauto.
Qed.

(** * Simulation match relations. *)

Inductive match_states : state -> state -> Prop :=
| match_regular_states : forall stk tstk f tf sp pc rs rs' m re rm
    (WT_FN: wt_function f re)
    (WT_RS: wt_regset re rs)
    (STACKS: match_stackframes stk tstk (fn_sig f))
    (FUN : match_function re rm f tf)
    (REGS : match_regsets f.(fn_params) f.(fn_code) rm rs rs'),
    match_states (State stk f sp pc rs m) (State tstk tf sp pc rs' m).

Section PRESERVATION.
  Variable prog: program.
  Variable tprog: program.
  Hypothesis TRANSF: match_prog prog tprog.

  Lemma symbols_preserved (s : ident) :
    Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof. apply (Genv.find_symbol_match TRANSF). Qed.

  (* ... more lemmas ... *)
End PRESERVATION.
```

**Patterns:**
- **Setup**: Define `match_prog`, `match_states`, match predicates for all relevant components
- **Teardown**: End proof section; combine lemmas into composite theorem
- **Assertion pattern**: Lemmas assert invariants as types; proof term is witness

**Example Setup Pattern (from `RTLtolerant.v` lines 52-119):**

```coq
Section match_states.
  (* Lemma: regsets match under fault, allowing one basic color to differ *)
  Definition match_rs (col : reg -> option color) (faulted : bool)
    (rs1 rs2 : regset) : Prop :=
    if faulted then
      exists c, is_basic c /\
             forall r, col r <> Some c -> Val.lessdef (rs1 # r) (rs2 # r)
    else
      forall r, Val.lessdef (rs1 # r) (rs2 # r).

  (* Inductive match relation on program states *)
  Inductive match_states : bool -> RTL.state -> fstate -> Prop :=
  | match_states_State :
    forall col stk1 stk2 f sp pc rs1 rs2 m1 m2 (b : bool)
      (STK: Forall2 (match_stackframes b) stk1 stk2)
      (WC_FUN: wc_function col f)
      (RS_COMPAT: rs_compat rs1 rs2)
      (RS: match_rs (col pc) b rs1 rs2)
      (MEM: Memory.Mem.extends m1 m2),
      match_states b (State stk1 f sp pc rs1 m1)
                   {| fs_state := State stk2 f sp pc rs2 m2; fault := b |}.
End match_states.
```

## Mocking

**Framework:** None needed for Coq proofs
- Semantics are defined constructively; no external dependencies to mock
- Non-verified oracle `RTLinfercolor.infer_coloring` (OCaml) is axiomatized in `RTLcolorcheck.v`

**Patterns:**
- **Axioms as mocking boundaries**: `Parameter infer_coloring : function -> option (node -> PTree.t color)` in `RTLcolorcheck.v` line 73
- Verified checker calls this oracle; oracle implementation in OCaml is trusted (unverified)
- Extraction wires OCaml implementation to Coq Parameter via `driver/Driver.ml` line 63: `RTLcolorcheck.check_program rtl`

**What to Mock:**
- External function calls (modeled as events in `Events.v`)
- I/O operations (represented as trace events)
- Platform-specific behavior (assembly code generation in architecture-specific files like `x86/Asmgen.v`)

**What NOT to Mock:**
- Compiler state: all state is explicitly threaded (no global mutable state in proofs)
- Memory model: fully specified in `common/Memory.v`
- Value representations: fully axiomatized in `common/Values.v`

## Fixtures and Factories

**Test Data:**
- No explicit test fixtures in Coq
- Proof by existential quantification over generic parameters
- Example pattern from `RTLtolerant.v`: tests hold for any well-colored program, any state, any regsets satisfying match relation

**Location:**
- Inline in proof goals: `forall prog : program`, `forall s : RTL.state`
- Parametric in vote type: `Context {VT: vote_type}` allows same proof to work for Two, Three voting

## Coverage

**Requirements:** No formal coverage metric enforced
- All compiler passes must prove semantic preservation
- All transformations must establish match relations for all possible states
- Color checker must validate all RTL instructions (checked in `RTLcolorcheck.v` lines 120-176)

**View Coverage:**
```bash
# Check which proofs are complete (no Admitted)
grep -r "Admitted" backend/*.v

# View proof structure
coq_makefile -f _CoqProject -o Makefile
make -n backend/RTLtolerant.vo  # Shows dependencies
```

## Test Types

**Semantic Preservation Proofs (Simulation):**
- **Scope**: Each compiler pass proves output program refines input program via forward or backward simulation
- **Approach**: Define match relation on states; show for all matched input states, one step in input language corresponds to zero or more steps in output language
- **Examples**:
  - `RTLdmrproof.v`: Forward simulation (DMR replication preserves semantics)
  - `RTLtmrproof.v`: Forward simulation (TMR replication preserves semantics)
  - `RTLtolerant.v`: Backward simulation (well-colored TMR program refines faulty program with 3-vs-2 voting)

**Integration Tests (Composed Proofs):**
- **Scope**: Full compilation pipeline from C to Asm (or C to RTL for fault tolerance)
- **Approach**: Chain individual pass proofs via `transitive_simulation` in `Smallstep.v`
- **Main theorem**: `transf_c_program_to_rtl_preservation_faulty` in `driver/Complements.v`
  - Input: C program without replication (Csyntax)
  - Output: TMR-replicated RTL program with coloring
  - Refinement: Under fault model, 2-voting executions of faulty program simulate 3-voting non-faulty execution

**No E2E tests in traditional sense** - instead, proof theorems establish end-to-end behavior:
- `program_behavior_preserved`: Traces of output program ⊆ traces of input program (failure is allowed but not false success)

## Common Patterns

**Async Testing:**
- Not applicable (deterministic semantic proofs)
- All recursion in proofs is well-founded and proven to terminate

**Error Testing:**
- Checked via compiler error messages in OCaml wrapper
- Example from `Driver.ml` lines 59-68:
```ocaml
let rtl =
  match Compiler.transf_c_program_to_rtl csyntax with
  | Errors.OK rtl -> rtl
  | Errors.Error msg -> let loc = file_loc sourcename in
                        fatal_error loc "%a" print_error msg in
if RTLcolorcheck.check_program rtl then
  (* print_endline "RTL program is well-colored :)" *)
  ()
else begin
    print_endline "RTL program not well-colored!"
    (* exit 1 *)
  end;
```

**Proof by Contradiction:**
- Tactic: `byContradiction` (= `exfalso`) in `Coqlib.v`
- Pattern: `exfalso` to switch goal to `False`, then derive contradiction from hypotheses
- Example: Proving injectivity of injections via contradiction

**Proof by Induction:**
- Mutual recursion in instructions/functions proven by mutual induction
- Stack frames analyzed inductively (base case nil, cons case with IH)
- Example from `RTLtolerant.v` lines 153-159:
```coq
Lemma forall2_match_stackframes_fault stk1 stk2 :
  Forall2 (match_stackframes false) stk1 stk2 ->
  Forall2 (match_stackframes true) stk1 stk2.
Proof.
  induction 1; constructor; auto.
  apply match_stackframes_fault; auto.
Qed.
```

**Simulation Proofs:**
- Pattern: Show for all matched states, input step can be followed by zero or more output steps with matching resulting states
- Invert step constructors to case on instruction type
- Instantiate match predicate with specific instruction result
- Example structure in `RTLdmrproof.v`:
```coq
Lemma step_simulation s1 t s1' s2 :
  match_states s1 s2 ->
  Step (semantics prog) s1 t s1' ->
  exists s2', Step (semantics tprog) s2 t s2' /\ match_states s1' s2'.
Proof.
  intros Hmatch Hstep.
  inv Hmatch.                          (* Case on match state constructor *)
  - inv Hstep.                          (* Case on input step *)
    + (* Case: Iop instruction *)
      ...
    + (* Case: Iload instruction *)
      ...
```

## Test Execution Flow

**Full Proof Workflow:**

1. **Parse all .v files** (with `coq_makefile`)
2. **Type-check and verify each proof incrementally** (via `coqc`)
   - Dependencies tracked by import order
   - Each module built independently then composed
3. **Extract verified code to OCaml** (via `Extraction` plugin)
   - `RTLinfercolor.infer_coloring` implementation in OCaml linked via axiom
4. **Compile OCaml to native binary** (via `ocamlopt`)
   - `ccomp` executable contains proven compiler + unverified inference oracle
5. **Manual integration test**: Run `ccomp test.c -tmr -o test` and verify output

**Example Build Sequence:**
```bash
make clean
make proof                          # Step 1-2: all .v to .vo
make extraction                     # Step 3: .v to OCaml .ml
make ccomp                          # Step 4: .ml to ccomp binary
./ccomp test/dmr_log.c -tmr -o test # Step 5: integration test
```

## Coverage Gaps and Known Issues

**Admitted Proofs:**
- ~25 `Admitted` statements found in backup files (`DMRproof_backup*.v`, `RTLAgreement_backup.v`)
- Active codebase in main files appears to have completed proofs (no `Admitted` visible in `RTLdmr.v`, `RTLdmrproof.v`, `RTLfault.v`, `RTLtolerant.v`)
- Backup files are not part of build (not listed in `_CoqProject` or `Makefile`)

**Untested Areas:**
- Color inference oracle (`RTLinfercolor.ml`) is unverified (assumed correct)
- Assembly generation in architecture-specific files (not retested with this fault tolerance extension)
- Runtime support library (C runtime in `runtime/` directory)

**Manual Testing:**
- Single test case: `test/dmr_log.c` with command `ccomp -finline-asm dmr_log.c -dmr -dasm && ./a.out`
- No systematic regression test suite
- No property-based testing framework

---

*Testing analysis: 2026-03-03*
