# Testing Patterns

**Analysis Date:** 2026-03-14

## Test Framework

**Runner:**
- **Coq proof checking:** `coqc` compiler runs all proofs; all `.v` files in `Makefile` targets
- **Configuration:** `_CoqProject` file specifies module paths and compilation order
- **Make targets:** `make proof` compiles all Coq proofs to `.vo` files
- **No external test framework** - proofs ARE the tests

**OCaml side:**
- **Extraction:** `make extraction` extracts OCaml code from Coq proofs
- **Compilation:** `make ccomp` builds the compiler binary from extracted code
- **Runtime test:** `runtime/test/test_int64.c` provides basic C test case
- **No unit testing framework** - testing happens via compiled program behavior

**Run Commands:**
```bash
make proof              # Compile all .v files to .vo (full proof checking)
make all                # Full build: proof -> extraction -> OCaml compilation
make clean              # Remove build artifacts
make distclean          # Remove everything including generated files
./ccomp test.c -tmr -o test    # Use compiler with TMR fault tolerance
```

## Test File Organization

**Location:**
- **Coq proofs:** Co-located with semantic definitions in same directory
  - `backend/RTL.v` (semantics) + `backend/RTLfault.v` (extension)
  - `backend/RTLfault.v` (definition) + implicit test via proof compilation
  - `backend/RTLfaultproof.v` (proof that faults are handled correctly)
  - `backend/RTLtolerant.v` (main tolerance proof)
- **OCaml testing:** Single integration test
  - `runtime/test/test_int64.c` - C program testing 64-bit integer operations
- **No separate test directory** - proofs embedded in source files

**Naming:**
- **Coq:** `{Module}proof.v` proves semantic preservation for `{Module}.v`
- **OCaml:** No test naming convention; single runtime test

**Structure:**
```
backend/
├── RTLfault.v           # Faulty semantics definition + basic lemmas
├── RTLfaultproof.v      # (implicit: backward sim proof)
├── RTLtolerant.v        # Backward simulation: non-faulty >= faulty
├── RTLcolor.v           # Color system specification
├── RTLcolorcheck.v      # Boolean color checker + proof
├── RTLinfercolor.ml     # OCaml oracle (unverified)
├── RTLtmr.v             # TMR transformation
├── RTLtmrproof.v        # TMR semantic preservation proof
```

## Test Structure

**Coq proof organization:**

All proofs follow standard CompCert semantic preservation pattern. Example from `RTLtolerant.v`:

```coq
Section match_states.

  (** When a fault has occurred elsewhere and regsets [rs1] and [rs2]
      are unchanged, they still match. *)
  Lemma match_rs_upto_fault res live col (pc : node) (rs1 rs2 : regset) :
    match_rs_upto res live (col pc) false rs1 rs2 ->
    match_rs_upto res live (col pc) true rs1 rs2.
  Proof. intro H; exists Red; split; auto; constructor. Qed.

  Inductive match_stackframes (faulted : bool)
    : RTL.stackframe -> RTL.stackframe -> Prop := ...

  Inductive match_states (faulted : bool)
    : RTL.state -> RTL.state -> Prop := ...

  (* Large section of supporting lemmas *)
  Lemma match_states_call ...
  Lemma match_states_return ...

  (* Main simulation proof *)
  Theorem backward_sim :
    backward_simulation (RTL.semantics ...) (faulted_semantics ...).
  Proof. ... Qed.

End match_states.
```

**Patterns:**
- **Setup:** Define matching relations (`match_rs`, `match_stackframes`, `match_states`)
- **Lemmas:** Prove invariant properties of matching relations
- **Theorem:** Main semantic preservation theorem using simulation framework
- **Teardown:** `End` section to close proof context

## Mocking

**Framework:**
- **Not applicable** - Coq proofs are mathematical, not implementation tests
- **Extracted code:** Coq axioms for unverified parts get mocked implementations

**Patterns in RTLinfercolor.ml:**
```ocaml
exception ColorError of string

(* Unverified oracle implementation *)
let infer_coloring (f : coq_function) (live : Regset.t PMap.t)
    : (node -> PTree.t color) option =
  try
    (* Union-find algorithm to infer colors *)
    let cols = init_cols f in
    ...
    Some (fun pc -> ptree_of_uf_node_array (cols pc))
  with ColorError _ -> None
```

**What to Mock:**
- External function calls (via builtins and semantics)
- Oracles with unverified implementations (e.g., `RTLinfercolor.infer_coloring`)
- Platform-specific behavior (handled via architecture-specific `Op.v`, `Machregs.v`, `Asm.v`)

**What NOT to Mock:**
- Semantic definitions - these are the ground truth
- Proven transformations - proof ensures correctness
- CompCert standard library operations - treated as trusted axioms

## Fixtures and Factories

**Test Data:**

CompCert proofs use concrete semantic definitions as test cases. Example state construction in `RTLfault.v`:

```coq
Inductive fstep : fstate -> trace -> fstate -> Prop :=
| fstep_step_State : forall stk f sp pc rs m t s' s'' b b'
    (STEP: @RTL.step Builtins2.Two Builtins2.VoteSemantics_Two ge
             (State stk f sp pc rs m) t s')
    (ZAP: maybe_zap f pc s' b s'' b'),
    fstep
      {| fs_state := State stk f sp pc rs m; fault := b |}
      t
      {| fs_state := s''; fault := b' |}.
```

State components:
- `State stk f sp pc rs m` - RTL state with stack, function, pointer, PC, register state, memory
- `Callstate stk f args m` - function call state
- `Returnstate stk v m` - function return state

**Location:**
- **Coq:** Test predicates and relations embedded in proof files
  - `maybe_zap` relation defines allowed faults
  - `match_rs` predicate defines register matching for simulation
  - `match_states` predicate defines full state matching

## Coverage

**Requirements:**
- **Mandatory:** All `Lemma` and `Theorem` items must compile (no `Admitted` proofs in production)
- **Verification command:** `make check-admitted` ensures no unproven assumptions
- **Note:** No coverage metrics; proofs are either complete or incomplete

**View Coverage:**
```bash
make check-admitted     # Ensure no Admitted proofs
grep -r "Admitted\|admit" backend/*.v  # Find incomplete proofs
```

## Test Types

**Proof-based testing (Coq):**

### Unit Lemmas
- **Scope:** Single property or transformation step
- **Approach:** Direct induction and case analysis
- **Example:** `val_compat_refl`, `val_compat_trans` (properties of value compatibility)
  ```coq
  Lemma val_compat_refl (v : val) :
    val_compat v v.
  Proof. destruct v; constructor. Qed.
  ```

### Invariant Lemmas
- **Scope:** Properties preserved across execution steps
- **Approach:** Prove invariant holds at each step
- **Example:** `match_rs_weaken` (live set properties preserved across steps)
  ```coq
  Lemma match_rs_weaken s1 s2 col faulted rs1 rs2 :
    Regset.Subset s1 s2 ->
    match_rs s2 col faulted rs1 rs2 ->
    match_rs s1 col faulted rs1 rs2.
  ```

### Semantic Preservation
- **Scope:** Transformation correctness (e.g., TMR insertion preserves behavior)
- **Approach:** Backward simulation between source and target semantics
- **Example:** Main theorem in `driver/Complements.v`
  ```coq
  Lemma transf_rtl_program'_forward_simulation p tp :
    match_prog_rtl_asm p tp ->
    forward_simulation (RTL.semantics p) (Asm.semantics tp).
  ```

### Integration Testing (C programs)
- **Scope:** Full compiler pipeline (C -> RTL -> Asm)
- **Approach:** Compile C, run executable, verify behavior
- **Example:** `runtime/test/test_int64.c`
  ```c
  /* Tests 64-bit integer operations under TMR *)
  int main() { ... }
  ```

## Common Patterns

**Inductive predicate matching:**
```coq
Inductive match_rs (live : Regset.t) (col : reg -> color) (faulted : bool)
  (rs1 rs2 : regset) : Prop :=
  if faulted then
    exists c, is_basic c /\
           forall r, Regset.In r live -> col r <> c -> Val.lessdef (rs1 # r) (rs2 # r)
  else
    forall r, Val.lessdef (rs1 # r) (rs2 # r).
```

**Proof by induction on step sequences:**
```coq
Lemma match_states_step :
  forall state1 state2,
  match_states state1 state2 ->
  forall state2',
  RTL.step ge state2 trace state2' ->
  exists state1',
  RTL.step ge state1 trace state1' /\
  match_states state1' state2'.
```

**Async/step-based testing (via simulation):**
- Simulation framework (`Smallstep.v`) defines `forward_simulation` and `backward_simulation`
- Step relation: `step : state -> trace -> state -> Prop`
- Simulation: Establishes that for every step in target, there's a matching step(s) in source
- Traces: Sequences of events (external function calls, I/O) that must match

**Error scenario testing:**
- **Faulty execution:** `RTLfault.v` defines `maybe_zap` to inject single bit-flip faults
- **Color checking:** `RTLcolorcheck.check_program` verifies fault-tolerance properties
- **Agreement lemmas:** `RTLagreement.v` proves non-faulty and faulty paths reach agreement

## Proof Tactics and Patterns

**Common tactical approaches:**

```coq
(* Pattern matching on inductive definitions *)
Proof.
  destruct faulted.
  - (* faulted = true case *)
    destruct RS as (c & Hc & RS).
    exists c; split; [auto|].
    intros r Hr Hcol. apply RS; auto.
  - (* faulted = false case *)
    auto.
Qed.

(* Inversion for simulation hypotheses *)
Proof.
  inv STEP.
  - (* State step *)
    destruct ZAP.
    + (* No zap *)
      exists state'; exact (...).
    + (* Zap occurred *)
      exists state''; exact (...).
  - (* Call/Return step *)
    exact (...).
Qed.

(* Recursive simulation *)
Proof.
  induction steps.
  - (* Base case: empty step sequence *)
    exists state1; split; [exact ...; exact ...].
  - (* Inductive case: step::steps *)
    inv H. (* Invert step *)
    destruct IH as (state1' & STEPS & MATCH).
    exists state1''; split; [exact ...; exact ...].
Qed.
```

---

*Testing analysis: 2026-03-14*
