# Codebase Concerns

**Analysis Date:** 2026-03-14

## Arch-Specific `is_protected` Definition

**Issue:** Architecture-specific logic hardcoded in generic RTL backend

Files: `backend/RTL.v:903-904`

The `is_protected` operation contains x86-specific cases (e.g., `Osubl` conditioned on `Archi.ptr64`, pointer comparisons conditioned on `Archi.ptr64 = false`). These belong in target-specific `Op.v` files, not in generic RTL layer code.

**Impact:** Multi-target builds (x86, RISC-V, ARM) have incorrect semantics for protected operations on non-x86 targets. The current architecture-agnostic location makes it easy to miss target-specific constraints.

**Fix approach:** Relocate `is_protected` and related operation classification to `x86/Op.v`, `riscV/Op.v`, etc. Update `backend/RTL.v` to import the target-specific definition through `Archi` module.

---

## Builtin Treatment Overly Conservative

**Issue:** All builtins treated identically despite varying safety profiles

Files: `backend/RTLfault.v:50-61`, `backend/RTLtmr.v:161-244`, `backend/RTLcolor.v`, `backend/RTLcolorcheck.v`, `backend/RTLinfercolor.ml`

Current approach:
- All `Ibuiltin` instructions force their arguments to vote (White), execute once in regular world, copy result to shadows
- Faulty RTL disallows all faults on builtins (`zap_allowed` returns `False`)
- Color system forces all builtins except `smove`/`vote` to White
- Commented-out code suggests this was known to be too conservative

**Impact:**
- Safe pure builtins (e.g., `__builtin_bswap`, `__builtin_clz`) cannot be faulted/recovered, forcing unnecessary voting overhead
- Reduces effective fault tolerance scope
- Inconsistency across TMR pass, faulty semantics, and coloring system

**Fix approach:** See comprehensive plan in `plans/builtin-treatment-plan.md`. Requires coordinated changes across 5 files in 5 phases:
1. Define shared classification (`builtin_can_replicate`, `builtin_can_fault`) in `backend/RTL.v`
2. Validate semantic support in `common/Builtins.v` / `common/Events.v`
3. Update TMR pass (`backend/RTLtmr.v`, `backend/RTLtmrproof.v`)
4. Update coloring (`backend/RTLcolor.v`, `backend/RTLcolorcheck.v`, `backend/RTLinfercolor.ml`)
5. Relax faulty semantics (`backend/RTLfault.v`, `backend/RTLtolerant.v`)

**Risk level:** High (especially phase 5 - semantic monotonicity validation against `val_compat` fault model)

---

## Fault Tolerance Proof Limited to RTL

**Issue:** Theorem covers only RTL level, not final assembly code

Files: `driver/Complements.v:546-570`, `doc/fault_tolerance.md:21`

Main theorem: `transf_c_program_to_rtl_preservation_faulty` stops before register allocation. Documentation states:

> "Extension to the level of asm is possible; it is mostly a matter of implementing a color checker for the backend of choice. See ref:TODO."

Three `ref:TODO` placeholders in `doc/fault_tolerance.md` (lines 21, 95, 167) point to unwritten ASM extension details.

**Impact:** Fault tolerance guarantee applies only to RTL intermediate code. Users cannot trust generated assembly to be fault tolerant without additional proof work.

**Current infrastructure:** `x86/Asmagreement.v` exists but is not wired into main theorem.

**Fix approach:**
1. Complete ASM-level color checker for active backends (x86-64, RISC-V)
2. Extend simulation chain through Allocation → Tunneling → Linearize → Stacking → Asmgen
3. Integrate color checker as formal pass in `driver/Compiler.v`
4. Lift main theorem from RTL to ASM level

---

## Color Checker Soundness-Only Proof

**Issue:** Checker is sound but not complete

Files: `backend/RTLcolorcheck.v:484-496, 521-522`

Proved: If checker accepts → program is well-colored (soundness)
Not proved: If well-colored → checker accepts (completeness)

Commented-out lemma: `check_col_function_complete` marked as "Maybe not necessary but should be true anyway"

Additional note: Without assumptions about `infer_coloring` oracle behavior, cannot prove `check_function_complete` because invalid coloring oracle can reject valid programs.

**Impact:** Valid programs may be rejected if union-find oracle fails to find a valid coloring, even though one exists. Creates unnecessary barrier to compilation.

**Fix approach:**
1. Prove `infer_coloring` correctness properties separately
2. Add assumptions to `check_function_complete` about oracle behavior
3. Either complete the proof or document the required oracle properties explicitly

---

## Non-Replicated Instructions Reduce Fault Coverage

**Issue:** Only `Iop` instructions (and only non-protected ones) are triplicated

Files: `backend/RTLtmr.v:210-223`, `backend/RTLfault.v:55-59`, `todo1.md:46-56`

Current limitation:
- `Iload` results unprotected; fault on load goes undetected (mitigated by setting `zap_allowed (Iload) = False`)
- `Icond` branches vote arguments but execute once; fault on condition evaluation undetected
- `Icall` results unprotected until smoves propagate
- All builtins (even pure ones) vote arguments, execute once, copy results

**Impact:** Limits fault tolerance to operations explicitly listed as safe. Reduces overall fault coverage.

**Fix approach:**
1. Extend TMR to triplicate safe loads and builtins (depends on builtin classification completion)
2. Consider triplicating conditional branches (architectural impact on control flow)
3. Audit memory semantics for load replication safety

**Difficulty:** Medium-High (requires reasoning about memory ordering and load semantics)

---

## Strong Agreement Proof Incomplete/Commented Out

**Issue:** Strong agreement formalization entirely commented out

Files: `backend/RTLagreement.v:18-70, 96-136, 163-204`

Commented components:
- `agreement_at_state` predicate
- `strong_agreement` definition
- `strong_agreement_implies_weak_agreement` theorem
- `forward_simulation_preserves_weak_agreement` (only x86 version in `x86/Asmagreement.v` is active)

**Impact:** Only weak agreement is proved (sufficient for current proof but less elegant). Code is hard to understand with large commented sections. Maintenance burden if strong agreement becomes necessary later.

**Fix approach:**
1. Either complete strong agreement formalization with proofs
2. Or remove commented code and document why weak agreement is sufficient
3. Consolidate duplicate agreement definitions across `RTLagreement.v` and `x86/Asmagreement.v`

---

## Stale Documentation

**Issue:** Proof completion not reflected in documentation

Files: `doc/fault_tolerance.md:272-278` (and line 3)

Documentation says: "the corresponding changes to the faulty simulation proof are not done yet"

However: Liveness integration was completed in commit `4e7c6185`. Related changes:
- `RTLcolor.v` quantifies over live registers only
- `RTLcolorcheck.v` uses `ProofLiveness.analyze`
- `RTLtolerant.v` fully updated for liveness

**Impact:** Readers misunderstand current proof status. Line 3 references old branch name `fault-tolerance-backward-sim2-union-find`.

**Fix approach:** Update `doc/fault_tolerance.md`:
- Line 3: Remove branch reference or update to current branch
- Lines 272-278: Document liveness integration as complete
- Update three `ref:TODO` markers with actual content or explicit forward references

---

## Check Builtins Are Semantic Stubs

**Issue:** Check builtins return `Vundef` without actual verification

Files: `backend/Builtins2.v`

`__builtin_check_*` builtins are defined to return `Vundef` at RTL level. They have no semantic effect—actual verification happens through color system and simulation proof.

**Impact:**
- Code inspection shows "check" operations but they do nothing at RTL semantics
- Potential confusion about verification strategy
- If ASM extension adds memory faults, check builtins might need real semantics

**Mitigation:** Already present - color system ensures well-colored programs satisfy separation invariant

**Fix approach:** Add documentation explaining check builtin semantics (why they're stubs, where real work happens)

---

## Tany32/Tany64 Types Cause Hard Failure

**Issue:** TMR/DMR pass fails instead of handling abstract register types

Files: `backend/RTLtmr.v:110-111`, `backend/RTLdmr.v:90`

When pass encounters register typed `Tany32` or `Tany64`, it raises error. These abstract types can appear in CompCert IRs.

**Impact:** Programs with such registers cannot be compiled with TMR/DMR, even though conservative handling is possible.

**Fix approach:** Default to conservative (voting) strategy for abstract types instead of failing:
```coq
| Tany32 | Tany64 => (* fall back to voting strategy *)
```

---

## Overly Coarse Union-Find Array Indexing

**Issue:** RTLinfercolor assumes dense RTL node numbering

Files: `backend/RTLinfercolor.ml:28-29, 184-186, 405-406`

Implementation uses array indexed directly by RTL node index. Comment acknowledges:

> "This representation is efficient, but it assumes the RTL node numbers are dense enough to index the per-node arrays directly."

**Impact:** If node numbers become sparse (e.g., nodes 0, 100, 10000), array allocates massive unused space, causing memory blow-up.

**Risk:** Low current risk (node numbers typically dense in practice) but fragile assumption.

**Fix approach:** Use hashtable-based coloring state instead of array (accepts performance trade-off for robustness):
```ocaml
let init_cols (f : coq_function) : (node, (int, uf_node) Hashtbl.t) Hashtbl.t =
  Hashtbl.create 100
```

---

## CSE Proof Missing Novotes Hypothesis

**Issue:** CSE optimization proof doesn't require Novotes property despite needing it

Files: `backend/CSEproof.v:1574-1576`

Commented TODO:
```coq
(* TODO: make this theorem take Novotes as extra hypothesis, and
   precede this step in the compiler with one that checks that
   property. *)
```

**Impact:** CSE could theoretically introduce or expose vote-like patterns. Proof doesn't rule this out. Compile pipeline doesn't check Novotes before CSE.

**Fix approach:**
1. Add `Novotes` hypothesis to CSE preservation theorem
2. Insert Novotes check before CSE in compiler pipeline
3. Thread Novotes property through full pipeline proof

**Difficulty:** Low-Medium (requires tracing CSE optimization through preservation proof)

---

## No Memory Fault Model

**Issue:** Fault model covers only register corruption, not memory faults

Files: `backend/RTLfault.v`

`maybe_zap` only modifies register sets; never modifies memory `m`. Single-fault model assumes all bit-flips happen in registers.

**Impact:** Incomplete fault tolerance story. Real systems have memory faults (bit-flips in DRAM, stack, heap). Current proof doesn't address these.

**Scope consideration:** This is not necessarily a bug—RTL-level proof might intentionally limit scope. But it should be documented as a known limitation.

**Fix approach:** Document as limitation with rationale. Memory fault extension requires:
1. Define `val_compat`-style relation for memory corruption
2. Extend `maybe_zap` to optionally corrupt load results
3. Reprove simulation accounting for memory indeterminism

---

## Color Checker Not in Formal Pipeline

**Issue:** Color check is OCaml guard, not verified pass in Coq pipeline

Files: `driver/Driver.ml`, `doc/fault_tolerance.md:27`, `driver/Complements.v`

Color check inserted as runtime guard in `Driver.ml` on intermediate RTL. Not included in `Compiler.v` formal pipeline.

**Impact:** Main theorem assumes well-colored program as hypothesis, but nothing in Coq proves programs actually get checked. If OCaml checker is buggy or crashes, theorem doesn't apply.

**Fix approach:**
1. Define `check_program` as formal pass in `backend/RTLcolorcheck.v`
2. Add to `Compiler.v` pipeline after TMR
3. Prove pass is idempotent (well-colored programs pass, badly-colored programs fail)
4. Update main theorem to discharge `check` obligation automatically

**Difficulty:** Low-Medium (checker already proved sound; just needs pipeline integration)

---

## Test Coverage Gaps

**Issue:** No automated test suite for fault tolerance properties

Files: (entire codebase)

No test files found: `find . -name "*.test.*" -o -name "*.spec.*"` yields nothing

**Impact:**
- No regression detection for TMR/DMR transformations
- No verification that color checker rejects badly-colored programs
- Manual testing only for compiler binary

**Fix approach:**
1. Add test suite in `tests/` with fault-tolerance cases:
   - Small C programs with expected TMR structure
   - Color checker acceptance/rejection cases
   - Faulty semantics reference behavior
2. Use `ctest` or similar to validate compiler transformations
3. Add liveness analysis sanity checks

**Effort:** Medium (requires test infrastructure and reference oracle)

---

## Unverified OCaml Union-Find Implementation

**Issue:** Color oracle implementation not formally verified

Files: `backend/RTLinfercolor.ml:62-99`

Comment: "Union-find version, literally copy/pasted from Google AI"

Union-find code is extracted OCaml performing constraint collection and solving. Not verified; correctness depends on algorithm implementation.

**Impact:** Coloring oracle could produce invalid colorings due to bugs in path compression or union-by-rank. Checker might accept invalid colorings if oracle is wrong.

**Mitigation:** Checker is proved sound (if checker accepts, coloring is valid per spec). But oracle completeness unproven.

**Fix approach:**
1. Write comprehensive property-based tests for union-find
2. Verify against reference implementation
3. Consider alternative: prove oracle in Coq and extract (heavier but more assurance)

---

## Builtin Argument Remapping Utilities Duplicated

**Issue:** Multiple copies of builtin argument mapping logic

Files: `backend/RTLtmr.v`, `backend/RTLdmr.v` (both reimplement `AST.map_builtin_arg`)

**Impact:** Maintenance burden. If builtin argument structure changes, multiple sites need updating. Risk of inconsistency.

**Fix approach:** Use `AST.map_builtin_arg` and `AST.map_builtin_res` helpers consistently. Remove duplicate definitions. Update plan `plans/builtin-treatment-plan.md` section 3 already calls this out.

---

## Vote Semantics Parameterization Cognitive Load

**Issue:** All intermediate language semantics parameterized by vote type (Two vs Three)

Files: Throughout `backend/`, `cfrontend/` (uses `Section VOTE. Context {VT: vote_type} ...`)

Every language definition wrapped in vote-type context adds ~20 lines of boilerplate per file. Makes code harder to read and modify.

**Rationale:** Vote type only affects vote builtin semantics. Three-voting required for faulty simulation proof technical device.

**Impact:** High cognitive load for maintainers unfamiliar with design. Difficult to isolate core language from fault-tolerance machinery.

**Mitigation:** Vote type only matters in vote builtin semantics. All other operations identical. Design is sound but verbose.

**Fix approach (future):** Consider factoring out vote builtins separately from core semantics, reducing parameterization. Would require significant refactoring and is lower priority than semantic correctness.

---

## Large Proof Files Difficult to Navigate

**Issue:** Key proof files exceed 2000 lines

Files with high line counts:
- `backend/RTLtmrproof.v` (2574 lines)
- `backend/RTLtolerant.v` (2258 lines)
- `backend/RTLdmrproof.v` (1665 lines)

**Impact:** Proof maintenance and comprehension difficult. Small changes risk unintended side effects. Proof search slow.

**Fix approach:**
1. Break large proof files into smaller modules by case/scenario
2. Factor out helper lemmas to separate files
3. Use section structure to group related proofs
4. Consider proof assistant features (namespaces, module types) for organization

---

## Incomplete Builtin Classification Consistency

**Issue:** Multiple predicates for builtin behavior lack unified definition

Files: `backend/RTL.v` (`is_green_smove_builtin*`, `is_blue_smove_builtin*`, `is_vote_builtin*`) scattered across codebase

**Impact:** Easy to miss a builtin when adding new case. Inconsistency between TMR, coloring, faulty semantics hard to detect.

**Fix approach:** Already planned in `plans/builtin-treatment-plan.md` Phase 1. Implement shared classification point.

---

## Memory Model Limitations Not Documented

**Issue:** RTL memory model assumptions not explicit

Files: `backend/RTL.v`, `common/Memory.v`

**Implicit assumptions:**
- Memory operations are deterministic given inputs
- Load results fully determined by address/chunk (no hidden state)
- Memory locations do not spontaneously change between steps

**Impact:** If fault-tolerance extended to memory, these assumptions become critical constraints. Currently undocumented.

**Fix approach:** Add prose documentation to `doc/fault_tolerance.md` explaining memory model scope and limitations for fault tolerance.

---

## Liveness Analysis Overestimate Risk

**Issue:** `ProofLiveness.v` conservative liveness analysis may overestimate live sets

Files: `backend/ProofLiveness.v`

Analysis computes `live !! pc = union of live_in from successors`. This is correct but may be overly conservative if liveness definition differs from actual register usage.

**Impact:** Coloring constraints generated for more registers than necessary, potentially rejecting valid colorings.

**Mitigation:** Overestimation is sound (may reject valid programs but won't accept invalid ones).

**Fix approach:** Audit liveness computation against standard dataflow analysis. Add test cases verifying liveness precision.

