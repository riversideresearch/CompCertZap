# Codebase Concerns

**Analysis Date:** 2026-03-04

## Admitted Proofs

**Critical Color Checker Proof Gap:**
- Issue: The key soundness proof for the Boolean color checker is admitted, not completed
- Files: `backend/RTLcolorcheck.v:443`
- Impact: The `check_col_instr_sound` lemma (line 245-443) proves that passing the Boolean color check implies semantic well-coloredness. This proof is left incomplete with `Admitted` at line 443. The entire 200+ line proof is commented out (lines 249-442), suggesting it was abandoned mid-implementation.
- Risk: Any bug in the Boolean checker could be hidden. The checker implements complex instruction-specific color constraints, and without this soundness proof verified, the RTL-to-faulty-RTL refinement may not hold.
- Fix approach: Either complete the commented proof by working through each instruction case, or refactor the checker to use a more directly-verifiable approach. The proof structure is partially there - it needs to handle all instruction types (Inop, Iop protected/safe, Iload, Istore, Icall, Itailcall, Ibuiltin with special cases for smoves and votes, Icond, Ijumptable, Ireturn).

## Tech Debt

**Color System Complexity:**
- Area: TMR/DMR color-based separation proof
- Files: `backend/RTLcolor.v`, `backend/RTLcolorcheck.v`, `backend/RTLinfercolor.ml`
- Issue: The color system (Red/Green/Blue/White/Pink) defines register invariants that constrain how operations execute across three worlds. The constraints are complex:
  - Protected operations (like division) must have White inputs and outputs, triggering majority voting
  - Safe operations require all arguments to have the same color as the result
  - Smove builtins transition between colors (White->Pink->Red/Green/Blue)
  - Vote builtins aggregate Red/Green/Blue into White
- Problem: These constraints are hard to understand, audit, and extend. Instruction-specific rules in `check_col_instr` (line 81-220) are deeply nested and difficult to reason about. Each new instruction type or builtin requires careful color constraint reasoning.
- Maintainability: Adding support for new builtins (beyond current green_smove, blue_smove, and vote builtins) requires coordinated changes across RTLcolor.v, RTLcolorcheck.v, and RTLinfercolor.ml with no direct verification that the constraints remain sound.

**Unverified Color Inference Oracle:**
- Area: Color assignment algorithm
- Files: `backend/RTLinfercolor.ml` (unverified), wired to axiom in `backend/RTLcolorcheck.v:74-75`
- Issue: The OCaml color inference (union-find based) is not proven correct. It's extracted as an axiom `infer_coloring` with type `function -> PMap.t Regset.t -> option (node -> reg -> color)`.
- Risk: If the inference is unsound (assigns incorrect colors), the final program may not satisfy color well-coloredness, and the fault tolerance proof chain breaks. No verification that the inference respects the instruction color constraints.
- Fix approach: Either formalize the inference algorithm in Coq with a soundness proof, or add extensive runtime validation and error reporting to catch miscolored programs before compilation proceeds.

**Incomplete CSE Theorem Documentation:**
- Issue: Theorem `transf_program_correct` in `backend/CSEproof.v:1574-1596` has a TODO comment indicating it needs refactoring
- Files: `backend/CSEproof.v:1574-1576`
- Impact: Comment states "make this theorem take Novotes as extra hypothesis, and precede this step in the compiler with one that checks that property."
- Context: The CSE (Common Subexpression Elimination) pass operates on RTL without knowing whether the input has vote builtins. The Novotes check happens elsewhere in the pipeline, creating a coupling issue.
- Fix approach: Refactor the compiler pipeline to check Novotes before CSE, then make CSE's correctness depend on the Novotes precondition.

## Fragile Areas

**Liveness Analysis Dependency:**
- Component: RTL fault tolerance refinement
- Files: `backend/RTLtolerant.v:68, 91` (LIVE hypothesis in match_states), `backend/RTLcolorcheck.v:484`
- Fragility: The backward simulation from 3-voting RTL to 2-voting faulty RTL critically depends on liveness analysis results. If liveness analysis fails (returns None), the color checker fails silently (`check_function` line 484-491 returns false), and compilation aborts. However:
  - Liveness analysis is conservative but may fail on malformed code
  - No error messages distinguish "malformed" from "failed to color"
  - The color checker doesn't communicate *why* it failed to the user
- Safe modification: When liveness analysis fails, ensure the compiler provides actionable error feedback. Consider making the check earlier in the pipeline so failures happen before major transformations.

**Protected vs Safe Operation Classification:**
- Component: TMR transformation and color checking
- Files: `backend/RTLtmr.v:186-210`, `backend/RTLcolorcheck.v:85-96`, `backend/RTLcolor.v:118-123`
- Fragility: Operations are classified as "protected" (e.g., division) or "safe" (e.g., addition) via `is_protectedb`. Protected operations get majority voting; safe operations execute in all three worlds.
- Risk: The classification is defined in `backend/Op.v` (extracted from Coq). If a new architecture introduces operations with different safety semantics, the classification may be wrong. For example:
  - An operation might trap on both safe and unsafe inputs (not just unsafe)
  - An operation might have state-dependent behavior (modify control flow or memory)
- Safe modification: Document the safety contract clearly. Make protected operations easier to extend than just editing Op.v. Consider a verification that protected operations' semantics are truly deterministic and don't have side effects beyond their declared result.

**Color Well-Coloredness Assumption at All Program Points:**
- Component: RTLtolerant backward simulation
- Files: `backend/RTLtolerant.v:62-98` (match_stackframes, match_states)
- Fragility: The simulation assumes `wc_function col f` holds at every function on the stack. If a function is reachable but not well-colored, the simulation breaks. The color checker runs once on the TMR-transformed program, but:
  - If optimizations after TMR somehow invalidate colors, this isn't caught
  - If a function is dynamically loaded or passed as a function pointer, coloring isn't re-checked
  - The assumption couples the simulation proof to the specific color checker output
- Safe modification: Make coloring information part of the program representation so it flows through all transformations. Alternatively, add a global coloring validity check at the end of the pipeline.

## Known Limitations

**Single-Fault Model Restrictiveness:**
- Issue: Fault tolerance theorem assumes exactly one fault can occur during execution
- Files: `backend/RTLfault.v:63-73` (maybe_zap allows one register zap per instruction), `backend/RTLtolerant.v:1366`
- Scope: Covers transient bit flips in register values at protected operation results. Does not cover:
  - Multiple simultaneous faults
  - Faults in non-instruction locations (memory, stack, control flow)
  - Byzantine failures in voting or state divergence
  - Timing-based attacks
- Mitigation: The limitation is documented in the architecture but worth flagging because extending to multi-fault requires major proof redesign.

**Builtin Coverage Gaps:**
- Issue: Not all RTL builtins are handled specially in TMR transformation
- Files: `backend/RTLtmr.v:214-222` (fallback for unspecified builtins)
- Problem: Most builtins execute only in the regular world with majority voting on arguments. This is safe but means:
  - I/O operations (stdio, file I/O) are not replicated → concurrent I/O in three worlds can cause duplicate output or file corruption
  - Memory allocation builtins (malloc, free) are not replicated → the three worlds may have divergent heap layouts
  - Builtins with side effects (e.g., random number generation) only execute once in the regular world
- Scope: Current implementation handles green_smove, blue_smove, and vote builtins explicitly (lines 152-191). All others use default (lines 193-202).
- Risk: Silent behavioral differences if a program relies on I/O or allocation semantics under TMR. The compiler doesn't warn the user.
- Fix approach: Audit which builtins are used in practice. For critical ones (allocation, I/O), either replicate them or document that they're not supported under TMR.

## Performance Bottlenecks

**Color Inference Scalability:**
- Problem: The `RTLinfercolor.ml` union-find algorithm must color every register at every program point
- Files: `backend/RTLinfercolor.ml`, invoked in `driver/Driver.ml` before final code generation
- Issue: For large functions with many registers, union-find may have suboptimal complexity if not carefully implemented. The algorithm is unverified, so performance characteristics are not formally analyzed.
- Impact: On large programs, compilation may be slow. No benchmark data available.
- Improvement path: Profile the color inference on real CompCert-compiled binaries. If slow, consider a two-phase approach: quick conservative coloring, then local refinement for hot paths.

**Liveness Analysis Every Function:**
- Problem: `Liveness.analyze` is called for every function during color checking (RTLcolorcheck.v:484) and then again during TMR transformation (RTLtmr.v:298)
- Files: `backend/RTLcolorcheck.v:484`, `backend/RTLtmr.v:297-300`
- Issue: Liveness analysis is O(n log n) per function. Analyzing twice is wasteful.
- Improvement path: Cache liveness results in the program representation after the first analysis. Pass them through the pipeline.

## Missing Critical Features

**No Verification of Color Optimization Preservation:**
- Issue: The compiler applies standard RTL optimizations (Constprop, CSE, Deadcode) before color checking, but these optimizations are not proven to preserve color well-coloredness
- Files: `driver/Compiler.v:47-53` (optimization pipeline before color check)
- Problem: Optimizations may eliminate instructions that constrain colors. For example:
  - Deadcode elimination removes live-out register assignments that might be needed for color preservation
  - Constant propagation might turn a safe operation into a protected one or vice versa
  - CSE might eliminate redundant operations that maintained color consistency
- Risk: An optimized RTL program might fail the color check even if the original passed. This causes compilation failure with no clear explanation to the user.
- Scope: Not strictly a bug, but a design gap. The proof in RTLtolerant.v assumes the program is well-colored but doesn't prove that optimizations maintain that property.
- Fix approach: Either disable optimizations before TMR (conservative), or prove that key optimizations preserve color well-coloredness (ambitious).

**No Multi-World Memory Isolation Verification:**
- Issue: The three worlds (regular, green shadow, blue shadow) are simulated using the same memory model and register file
- Files: `backend/RTLfault.v:18-19` (fstate has a single RTL.state with shared memory), `backend/RTLtolerant.v:96` (match_states uses shared Memory.Mem)
- Problem: The implementation relies on software instrumentation (smove and vote builtins) to maintain separation. There is no hardware verification that writes in one world don't corrupt another. If a smove fails or a vote builtin doesn't execute, worlds can diverge without detection.
- Risk: A bug in a builtin implementation would break the fault tolerance guarantee at the ISA level.
- Mitigation: In a real implementation, hardware would enforce world isolation. The Coq proof assumes correct builtin semantics.

**No Proof of Coloring Completeness:**
- Issue: The color checker has a `check_col_function_sound` lemma (soundness) but no completeness proof
- Files: `backend/RTLcolorcheck.v:445-465` (sound), lines 468-479 (completeness is commented out and marked impossible)
- Comment: "check_col_function_complete not possible because we don't assume anything about infer_coloring" (line 504-505)
- Impact: A function might be colorable but the inference algorithm fails to find a coloring. The compiler rejects valid programs. No way to debug why a function is uncolorable.
- Scope: Inherent to the oracle-based design. Can't fix without formalizing the inference algorithm.

## Security Considerations

**No Proof of Fault Tolerance Against Malicious Faults:**
- Risk: The TMR guarantee assumes faults are random bit flips, not adversarial. A carefully crafted fault (e.g., zapping a register at a specific instruction) could potentially cause all three worlds to vote the same wrong value if the attacker knows the program structure.
- Files: `backend/RTLfault.v:63-73` (maybe_zap allows any compatible value), `backend/RTLtolerant.v:26-27` (match_rs only constrains one color per instruction)
- Scope: The proof is secure against single random faults but not against adaptive adversaries. This is acceptable for transient fault tolerance but not sufficient for Byzantine fault tolerance.
- Mitigation: Use only for radiation/soft-error protection. Don't rely on it for cryptographic key protection or security-critical operations.

**Majority Voting Doesn't Guarantee Consistency:**
- Issue: The vote builtin (RTLcolorcheck.v:180-191) aggregates three values into one but doesn't verify that at least two are identical
- Files: `backend/Builtins2.v` (vote builtin semantics - not fully readable)
- Problem: If the three worlds have diverged (e.g., due to two faults or an earlier undetected fault), voting on three different values produces an arbitrary result. The proof assumes votes have at least two identical inputs.
- Risk: A second fault before a vote could cause silent data corruption.
- Mitigation: The single-fault model limits this. After one fault, the next voting opportunity aggregates two correct + one faulty value, which is sound.

## Testing & Verification Gaps

**No End-to-End Regression Tests for TMR:**
- Issue: There are no regression test suites specifically for TMR transformation correctness
- Files: Test directory structure not explored; likely in `test/` or similar
- Problem: Without concrete test cases, subtle bugs in color inference or the TMR transformation can slip through. For example:
  - A function with unusual control flow (switches, computed jumps) might not be colored correctly
  - Edge cases in smove/vote handling might not be exercised
  - Interactions between inlining and coloring might break in rare cases
- Improvement: Develop a set of test programs with known correct colorings and verify the inference produces the same result.

**Color Checker Correctness Not Independently Verified:**
- Issue: The Boolean color checker (`check_col_instr` in RTLcolorcheck.v) has no external oracle or independent implementation to cross-validate against
- Files: `backend/RTLcolorcheck.v:81-220`
- Problem: If the checker has a subtle bug (e.g., off-by-one in register set iteration), all transformed programs would inherit that bug, and no test would catch it because tests would use the same checker.
- Improvement: Implement a reference color validator in OCaml and cross-test the extracted Coq checker against it.

## Documentation Gaps

**Color System Design Document Missing:**
- Issue: The color system is complex (5 colors, special semantics for each) but no high-level design document explains the rationale
- Files: `backend/RTLcolor.v`, `backend/RTLcolorcheck.v` (detailed but hard to follow)
- Problem: Future maintainers must reverse-engineer the design from Coq proofs. Adding new builtins or instructions requires understanding the whole system.
- Mitigation: Write a separate design document explaining:
  - Why 5 colors are needed (not 3)
  - What each color represents (e.g., Red = copy of main value, Green/Blue = copies, White = temporary)
  - Why smoves transition through Pink
  - Design rationale for protected vs safe operations

---

**Summary:** The codebase is feature-complete for single-fault TMR but has several unverified steps (color inference, color checker soundness) and missing extended coverage (multiple faults, all builtin types, memory isolation). The architecture is sound but fragile in places where liveness analysis or color well-coloredness could fail silently. Recommend completing the color checker proof and formalizing the inference algorithm as higher-priority improvements.

*Concerns audit: 2026-03-04*
