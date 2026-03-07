# Plan: Extending Fault Tolerance to RISC-V Asm, Revision 2

## Goal

Prove an Asm-level analogue of `transf_c_program_to_rtl_preservation_faulty` with a
theorem shape as close as possible to the current RTL theorem:

```coq
Theorem transf_c_program_preservation_faulty :
  forall p tp beh,
    transf_c_program p = OK tp ->
    Asmcolorcheck.check_program tp = true ->
    program_behaves (Asmfault.faulty_semantics tp) beh ->
    exists beh', program_behaves (Csem.semantics p) beh'
              /\ behavior_improves beh' beh.
```

The key requirements are:

1. Keep the corrected refinement composition from the newer plan.
2. Avoid making the fault semantics depend on the inferred coloring.
3. Resolve the interprocedural proof issue by carrying explicit caller context in the
   Asm match relation.
4. Avoid up-front Asm liveness machinery unless the proof actually needs it.

## High-Level Design

### 1. Keep the newer overall proof composition

Use the same proof shape as the newer plan:

```text
C >=2 RTL(no votes) >=3 RTL(no votes) >=3 RTL+TMR >=3 Asm >=2,faulty Asm
 (1) standard       (2) weak agree    (3) TMR sim  (4) backend (5) faulty sim
```

The weak-agreement step remains at RTL, exactly as in the current RTL proof.
We do not try to re-express the full theorem using the old plan's `Asm3 -> Asm2 -> C`
chain.

### 2. Parameterize RISC-V Asm by vote type

Adopt the newer plan's `Section VOTE` approach for `riscV/Asm.v` and downstream
RISC-V proof files, instead of introducing a separate `Asm3.v`.

Reason:

- It matches the x86 structure.
- It avoids duplicating the whole Asm semantics and proof maintenance burden.
- It gives the right source/target pair directly:
  `@Asm.semantics Three ...` vs `Asmfault.faulty_semantics`.

### 3. Use Asm-local provenance tags, not coloring-driven fault semantics

The central change from the newer plan is:

- **Do not** define faultability from the inferred coloring.
- **Do** preserve the needed provenance at Asm generation time by inserting explicit
  Asm-only tag instructions.

The ambiguity to solve is real: after Asm generation, the final opcode alone is not
enough to know whether an instruction should be faultable. For example, the same
`Psubl` instruction can originate from both protected and unprotected RTL operations.

The right place to preserve this information is **at Asm generation time**, while the
translator still knows the source operation.

### 4. Keep the color system register-only at first

At Asm level, the fault model still corrupts registers only, not memory.

Therefore:

- color only data registers (`data_preg = true`)
- do **not** introduce abstract stack-slot locations in the first version
- do **not** implement Asm liveness optimization in the oracle/checker initially

Spilled values live safely in memory; the relevant issue is how reloads re-enter the
register-colored world. The Asm checker should treat loads as producing White results,
and any re-entry into colored redundancy must happen through explicit smove/vote
discipline.

### 5. Use a ghost caller-context stack in the Asm tolerant proof

The main proof issue with the newer plan is interprocedural state.

Asm states do not expose an explicit call stack, unlike RTL's `Callstate` /
`Returnstate`. Therefore, the Asm faulty simulation should **not** try to get by with
only "current-state" constructors. Instead, it should carry a ghost stack of caller
contexts, analogous in role to `match_stackframes` in `backend/RTLtolerant.v`.

This is the main structural fix over both previous plans.

## Tagging Design

### New Asm pseudo-instruction

Add a new RISC-V Asm pseudo-instruction to `riscV/Asm.v`, for example:

```coq
Inductive ftag_kind :=
| FT_faultable
| FT_protected
| FT_neutral.

Inductive instruction :=
...
| Pftag (k: ftag_kind).
```

The exact tag vocabulary can be adjusted, but the first version only needs enough to
distinguish:

- writes that are in the fault model
- writes that are intentionally outside the fault model
- instructions with no relevant writable data-register destination

### Semantics of tags

`Pftag` should be a semantic no-op:

- `E0`
- memory unchanged
- register file unchanged except `PC := PC + 1`

This keeps Asm semantics fixed and lets the standard theorem quantify over a single
`faulty_semantics tp`, not a checker-produced parameter.

### Placement convention

Use a simple canonical convention:

- every real instruction that matters to fault classification is immediately preceded
  by one `Pftag`
- tags never appear in any other position

This makes later validation easy and avoids needing the fault semantics to guess which
instruction a tag belongs to.

### Where tags are inserted

Emit tags in `riscV/Asmgen.v`, not after Asm generation.

That is the latest point where the compiler still knows the source operation that is
being lowered. A later post-pass over plain Asm would not have enough information.

### What tags classify

For the first version, tags should classify **Asm instructions**, not RTL operations.

If one RTL operation expands to several Asm instructions, each resulting Asm
instruction gets its own tag according to whether that particular write should be in
the fault model.

This avoids hidden assumptions about expansion boundaries.

## Phased Plan

### Phase 0: Parameterize RISC-V Asm by vote type

**Files**

- `riscV/Asm.v`
- `riscV/Asmgenproof.v`
- `riscV/Asmgenproof1.v`
- `riscV/SelectOpproof.v`
- `riscV/SelectLongproof.v`
- any transitive RISC-V proof files that mention `Asm.semantics` / `Asm.step`
- `driver/Complements.v`

**Actions**

1. Wrap the RISC-V Asm semantics section in:
   `Section VOTE. Context {VT: vote_type} {vsem: VoteSemantics VT}.`
2. Generalize `semantics_determinate` for the parameterized semantics.
3. Rebuild the RISC-V backend proofs under the parameterized interface.
4. Confirm that instantiation at `Three` works cleanly for the backend-to-Asm
   composition.

**Exit criteria**

- RISC-V build succeeds with vote-parameterized Asm semantics.

### Phase 1: Add Asm fault-tag infrastructure

**Files**

- `riscV/Asm.v`
- `riscV/Asmgen.v`
- `riscV/Asmgenproof.v`
- `riscV/Asmgenproof1.v`
- `riscV/TargetPrinter.ml`

**Actions**

1. Add `Pftag`.
2. Give `Pftag` no-op semantics in `riscV/Asm.v`.
3. Decide whether `TargetPrinter` elides `Pftag` completely or prints it as a comment.
   For the proof it is just a pseudo-instruction.
4. Modify `Asmgen` so that emitted code follows the canonical "tag immediately before
   classified instruction" convention.
5. Update `Asmgenproof` to account for the extra silent steps. This will likely use
   stuttering / `plus` where previous proofs used a single straight-line execution.

**Design rule**

Tags are inserted by the compiler, not by the checker and not by the driver.

**Exit criteria**

- `Asmgen` produces tagged Asm.
- `Asmgenproof` is repaired.

### Phase 2: Tag-derived fault classification and faulty Asm semantics

**New file**

- `riscV/Asmfault.v`

**Actions**

1. Define the faulty state wrapper with a global fault bit, as in RTL.
2. Define helper functions over Asm code:
   - locate the current instruction position from `PC`
   - read the immediately preceding `Pftag`
   - determine the writable data-register destination(s) of the current instruction
3. Define `zap_allowed` from the tag and the current instruction, not from the
   coloring.
4. Keep the first theorem's fault model narrow:
   - fault only data-register destinations
   - exclude `PC`, `RA`, `SP`
   - exclude votes, smoves, and any other instructions intentionally outside coverage
5. Define `faulty_semantics` directly on the tagged Asm program.

**Why this is better than the newer plan**

The fault model is now fixed by the program syntax plus tag discipline, not by the
checker's inferred coloring. That gives a stronger theorem shape and a clearer notion
of covered faults.

**Exit criteria**

- `riscV/Asmfault.v` compiles standalone.

### Phase 3: Declarative Asm color system over registers only

**New file**

- `riscV/Asmcolor.v`

**Actions**

1. Define per-function coloring:
   `asm_coloring := Z -> preg -> color`
2. Color only data registers (`data_preg r = true`).
3. Start with an all-data-register formulation, not an Asm liveness-bounded one.
4. Define color rules for:
   - arithmetic/logical instructions
   - loads/stores
   - branches/jumps/jump tables
   - calls/returns/tailcalls
   - vote/smove builtins
5. Add **tag consistency** to the declarative spec:
   - if an instruction is tagged `FT_faultable`, its destination must be a basic color
     and the instruction must satisfy the unprotected-style rule
   - if it is tagged `FT_protected`, its destination must be White and it must satisfy
     the protected-style rule
   - `FT_neutral` is allowed only where appropriate

This keeps provenance checking and coloring checking aligned, while still separating
their roles:

- tags determine which faults are modeled
- colors prove separation

**Important simplification**

Do not add stack-slot colors in the first version.

If a spill/reload pattern later turns out to require more structure, revisit it with a
targeted extension, not a full location-liveness system.

**Exit criteria**

- `riscV/Asmcolor.v` compiles.

### Phase 4: Verified Boolean checker

**New file**

- `riscV/Asmcolorcheck.v`

**Actions**

1. Follow the RTL structure:
   - unverified `infer_coloring`
   - verified boolean checker
2. Keep the top-level checker result boolean:

```coq
check_program : Asm.program -> bool
```

3. `check_program` should validate:
   - tag placement is canonical
   - the inferred coloring satisfies the Asm well-coloredness judgment
   - tags and colors agree
4. Prove:

```coq
Lemma check_program_sound :
  check_program p = true ->
  asm_wc_program p.
```

where `asm_wc_program` packages both coloring validity and tag discipline.

**Rationale**

The checker should certify the existence of a good coloring, but the theorem should not
need to mention the coloring value.

**Exit criteria**

- `riscV/Asmcolorcheck.v` compiles with full soundness proof.

### Phase 5: Unverified coloring oracle

**New file**

- `riscV/Asminfercolor.ml`

**Actions**

1. Implement a first dense oracle over code position × data register.
2. Do **not** add sparse liveness optimization initially.
3. Revisit performance only if concrete workloads show a problem.

**Why**

The RTL liveness optimization was primarily needed because the register-like domain
grew with function size. Here the colored domain is fixed-size machine registers.
The proof cost of threading Asm liveness everywhere should not be paid up front.

**Fallback**

If the Asm tolerant proof later becomes too brittle with the all-register invariant,
add a **proof-only** live/caller-save filter there first, before changing the oracle.

**Exit criteria**

- Oracle compiles and checker extraction is wired.

### Phase 6: Asm-level faulty backward simulation with ghost caller contexts

**New file**

- `riscV/Asmtolerant.v`

**Core theorem**

```coq
Theorem asm_faulty_backward_simulation :
  asm_wc_program prog ->
  backward_simulation
    (@Asm.semantics Three VoteSemantics_Three prog)
    (Asmfault.faulty_semantics prog).
```

**Key structural decision**

Do not try to express the match relation using only current Asm states.

Instead define:

1. a current-state invariant over the current function, current code position,
   current coloring, and current fault bit
2. a ghost stack of caller contexts, each carrying enough information to re-establish
   the caller-side invariant after return

Suggested caller-context contents:

- caller function block
- caller return position
- caller per-position coloring (or enough to recover it)
- saved fault status / excluded color information
- any extra agreement facts needed for return

This is the Asm analogue of RTL's `match_stackframes`.

**Register invariant**

Start with an all-data-register invariant:

```coq
asm_match_rs current_col faulted rs1 rs2
```

where:

- non-faulted case: `Val.lessdef` for all data registers
- faulted case: `Val.lessdef` for all data registers except the excluded basic color
- non-data registers (`RA`, `X31`, etc.) tracked separately by equality
- `rs_compat` retained as in RTL

**Calls and returns**

Handle these explicitly:

1. **Internal call**
   - push a caller context onto the ghost stack
   - switch to the callee's coloring and well-coloredness proof
2. **External call**
   - use a dedicated constructor or case carrying the caller context, then restore the
     caller invariant after `exec_step_external`
3. **Internal return**
   - pop one caller context and re-establish the caller invariant at the return point
4. **Tailcall**
   - do not pretend it is an ordinary call/return pair
   - model it as replacing the current caller context appropriately

**Why this resolves the main flaw in the newer plan**

The newer plan had no convincing place to store caller return-site information.
This version does.

**Memory relation**

Use `Mem.extends` as in RTL.

Do not assume store backwardness "for free". Instead, structure the proof as in the
RTL tolerant proof and reuse the same `loadv_extends` / `storev_extends` /
`free_parallel_extends` / external-call lemmas where applicable.

**Fallback if proof becomes too brittle**

Only if necessary, introduce a proof-local filter at call boundaries or a lightweight
Asm proof-liveness notion. Do not make this the default design.

**Exit criteria**

- `riscV/Asmtolerant.v` compiles with no `Admitted`.

### Phase 7: Backend preservation lemma to Asm@Three

**File**

- `driver/Complements.v`

**Actions**

1. Reuse the newer plan's factoring of:
   - C to pre-TMR RTL
   - pre-TMR RTL to post-TMR RTL
   - post-TMR RTL to final Asm
2. Compose existing backend forward simulations instantiated at `Three`.
3. Convert the composed backend simulation to backward simulation using
   `forward_to_backward_simulation`.
4. Prove an Asm-level analogue of the existing RTL preservation lemmas.

**Reason**

This is the part the older plan got wrong directionally; keep the newer plan's
composition, not the old one.

**Exit criteria**

- preservation lemma from RTL@Three to Asm@Three is proved.

### Phase 8: Final theorem in `driver/Complements.v`

**Target theorem**

```coq
Theorem transf_c_program_preservation_faulty :
  forall p tp beh,
    transf_c_program p = OK tp ->
    Asmcolorcheck.check_program tp = true ->
    program_behaves (Asmfault.faulty_semantics tp) beh ->
    exists beh', program_behaves (Csem.semantics p) beh'
              /\ behavior_improves beh' beh.
```

**Proof composition**

1. Faulty Asm@Two is refined by non-faulty Asm@Three via the new Asm tolerant theorem.
2. Asm@Three is refined by RTL@Three via the composed backend theorem.
3. RTL@Three is refined by pre-TMR RTL@Three via the existing TMR theorem.
4. Pre-TMR RTL@Three is refined by C via the existing weak-agreement + standard
   compiler-correctness chain.
5. Compose `behavior_improves` transitively.

This preserves the correct refinement direction from the newer plan while keeping the
stronger theorem shape from the old RTL-style statement.

### Phase 9: Driver / extraction integration

**Files**

- `extraction/Extraction.v`
- `driver/Driver.ml`

**Actions**

1. Wire `Asmcolorcheck.infer_coloring` to `Asminfercolor.infer_coloring`.
2. Run the Asm checker on the final tagged Asm program in the driver.
3. Keep the RTL checker only as a temporary diagnostic during migration.

## Open Design Choices

### Should tags remain in the final printed assembly?

Two acceptable choices:

1. Printer elides them completely.
2. Printer emits them as comments / target-specific ignored directives.

The proof only needs them in the Coq/driver Asm representation.

### How many tag classes are really needed?

The first implementation should use the smallest tag vocabulary that supports the
fault model. If `FT_faultable` and `FT_protected` are enough, avoid extra classes.

### What if all-register matching is too strong?

Fallback order:

1. strengthen the ghost caller-context stack
2. add targeted proof-local filtering at call boundaries
3. only then consider an Asm proof-liveness analysis

Do **not** start by building sparse location liveness into the whole checker/oracle
pipeline.

## Main Risks

1. **Asmgen proof churn from inserted tags**
   - Mitigation: keep tags as inert one-step pseudo-instructions and localize the proof
     updates to straight-line execution lemmas.
2. **Interprocedural simulation complexity**
   - Mitigation: design the ghost caller-context stack before proving instruction cases.
3. **Tag/color consistency gaps**
   - Mitigation: make tag agreement part of the declarative `asm_wc_program`, not an
     informal side condition.
4. **Performance concern in the dense oracle**
   - Mitigation: measure first. Add optimization only if there is a demonstrated need.

## Validation Checklist

1. RISC-V build succeeds after vote-parameterization and tag insertion.
2. `make check-admitted` passes.
3. New files build:
   - `riscV/Asmfault.vo`
   - `riscV/Asmcolor.vo`
   - `riscV/Asmcolorcheck.vo`
   - `riscV/Asmtolerant.vo`
   - `driver/Complements.vo`
4. `make ccomp` succeeds.
5. Compiling a TMR test for RISC-V runs the Asm checker and accepts expected outputs.
