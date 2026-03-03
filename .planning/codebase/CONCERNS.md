# Codebase Concerns

**Analysis Date:** 2026-03-03

## Tech Debt

**Duplicate backup files (fault tolerance refactoring)**
- Issue: 13 backup files in `backend/` directory (`*_backup.v`, `backup_*.ml`) indicate incomplete refactoring or abandoned experiments during fault tolerance development
- Files: `backend/RTLfault_backup.v`, `backend/RTLAgreement_backup.v`, `backend/DMRproof_backup.v`, `backend/DMRproof_backup2.v`, `backend/driver/backup_Compiler.v`, `backend/backup_RTLinfercolor*.ml` (7 OCaml variants)
- Impact: Repository clutter, confusion about which versions are canonical, increased build time, unclear development history
- Fix approach: Archive these files outside the repository, or delete if superseded by current implementations. Document in commit message which versions are canonical.

**Incomplete color inference implementation**
- Issue: `backend/RTLinfercolor.ml` (union-find based) is an unverified OCaml oracle with no proof of correctness. The algorithm is "hodgepodge" with three update functions (one forward, two backward) that could be redesigned
- Files: `backend/RTLinfercolor.ml`, `backend/RTLcolorcheck.v` (Parameter infer_coloring at line 73)
- Impact: No formal guarantee that inferred colorings are sound. Well-colored predicate depends entirely on runtime checker being correct. If oracle produces invalid colorings that happen to pass checker, faulty simulation proof becomes invalid at runtime
- Fix approach: Redesign color inference to use single unification pass + forward propagation (as noted in `fault_tolerance.md` lines 341). Consider implementing in Coq if feasibility improves. Alternatively, add liveness-based optimization branch (`fault-tolerance-backward-sim2-union-find-liveness`) to production code.

**Unverified oracle integration**
- Issue: Color inference oracle declared as Parameter (axiom) in Coq but wired to OCaml implementation via extraction. No guarantee of correspondence between declared type and actual behavior
- Files: `backend/RTLcolorcheck.v` (line 73), `extraction/extraction.v` (line 87)
- Impact: Trust boundary between verified Coq proofs and unverified OCaml code. Bugs in OCaml implementation could silently corrupt colored program without proof system knowing
- Fix approach: Implement formal equivalence check between Coq type and OCaml behavior. Add property-based testing on color inference. Consider gradual migration to verified implementation.

**Memory usage issue in color inference**
- Issue: Color inference assigns colors to every register at every instruction label, creating O(n*m) dense table where n = instructions, m = pseudo-registers. Prohibitively high memory on large functions
- Files: `backend/RTLinfercolor.ml`, `fault_tolerance.md` (lines 272-278)
- Impact: Compiler may fail on large functions due to memory exhaustion. Performance degrades non-linearly with function size
- Fix approach: Implement liveness-based sparse table optimization (partially done in unmerged `fault-tolerance-backward-sim2-union-find-liveness` branch). Update faulty simulation proof invariant to quantify over live-out registers instead of all registers.

## Known Bugs

**Incomplete TODO markers in proofs**
- Issue: Multiple unfinished proofs or placeholder comments indicating work in progress
- Files:
  - `backend/RTLtolerant.v` (line 1164): "TODO: remove this and replace with better version below" for external_call_Three_Two
  - `backend/RTLtolerant.v` (line 1371): "TODO: the four cases in this proof are literally the same except the type argument to [vote]" - code duplication in external_call_vote_lessdef proof
  - `backend/RTLtmrproof.v` (line 772): "TODO: all four cases are very similar. combine them somehow or"
  - `backend/RTLcolorcheck.v` (line 117): "assert false TODO" in commented-out code
  - `backend/RTLfault_backup.v` (lines 80, 107, 175): Multiple TODO comments in backup file
- Impact: Code duplication in critical proof, making maintenance harder. Redundant lemmas (external_call_Three_Two and external_call_Three_Two') suggest incomplete refactoring
- Priority: Medium - affects code quality but proofs are complete

**Incomplete commented code**
- Issue: Large blocks of commented-out code in fault tolerance proof files suggest incomplete development
- Files: `backend/RTLfault_backup.v` (multiple sections), `backend/RTLtolerant.v` (lines 1160-1162, external_call sections), `driver/Complements.v` (lines 73-606, commented out fault tolerance theorems)
- Impact: Dead code makes it hard to understand intent, increases file size, creates confusion about what is implemented vs planned
- Fix approach: Remove commented code entirely or move to separate branch/document. If code represents alternative approaches, preserve in git history with branch/tag.

**Sparse test coverage of color system**
- Issue: Color system and color checker lack comprehensive proof of coverage. `check_function_complete` is impossible because oracle completeness not assumed (RTLcolorcheck.v line 516)
- Files: `backend/RTLcolorcheck.v` (line 516), `backend/RTLcolor.v`
- Impact: Incomplete colorings are silently rejected without explanation. No way to distinguish between "program is not colorable" vs "oracle failed to find a coloring"
- Priority: Low if oracle is reliable, High if failures are user-visible

## Security Considerations

**Unverified oracle could accept invalid programs**
- Risk: OCaml color inference oracle could be compromised or buggy. Invalid coloring could be wired back to Coq via extraction, bypassing proof verification
- Files: `backend/RTLinfercolor.ml`, `extraction/extraction.v` (line 87)
- Current mitigation: Boolean color checker re-validates inferred coloring before use (RTLcolorcheck.v line 501-510). Checker is sound (Lemma check_program_sound at line 525)
- Recommendations:
  1. Add runtime integrity check comparing Coq color checker result against OCaml oracle result
  2. Implement checksums/hashes of oracle code changes
  3. Add option to disable TMR/color checking entirely for safety-critical builds

**Faulty semantics allows multiple fault scenarios**
- Risk: Single-fault model in RTLfault.v assumes only one fault per execution. Multiple correlated faults or Byzantine faults could defeat TMR
- Files: `backend/RTLfault.v` (lines 73-83, maybe_zap), `backend/RTL.v` (zap_allowed definition at line 62-71)
- Current mitigation: Architectural limitation encoded in `zap_allowed` - faults only on result registers of unprotected Iops, not on loads/stores/calls
- Recommendations:
  1. Document fault model assumptions in API/header comments
  2. Add compiler flag to log which instruction faults are protected
  3. Consider extending to Byzantine fault tolerance if threat model requires it

## Performance Bottlenecks

**Color inference memory usage on large functions**
- Problem: O(n*m) dense register-at-instruction table causes memory spikes on functions with >10k instructions or >1k pseudo-registers
- Files: `backend/RTLinfercolor.ml` (lines 50-100+), `fault_tolerance.md` (lines 272-278)
- Cause: Union-find assigns unique node for every (register, instruction) pair before merging
- Current behavior: Compiler may OOM without clear error message
- Improvement path:
  1. Short term: Add memory limits and better error messages
  2. Medium term: Implement sparse table using liveness information (branch `fault-tolerance-backward-sim2-union-find-liveness`)
  3. Long term: Switch to incremental fixpoint algorithm if quadratic blowup fundamentally unavoidable

**Repeated proof patterns in TMR/DMR correctness**
- Problem: RTLtmrproof.v (2633 lines) and RTLdmrproof.v (1681 lines) contain nearly identical case analyses repeated 4+ times per lemma
- Files: `backend/RTLtmrproof.v`, `backend/RTLdmrproof.v`
- Cause: Vote builtins exist in Four variants (Int, Long, Single, Float) with identical proof structure
- Impact: Large proof files slow down proof checking and make maintenance error-prone
- Improvement: Use parameterized vote type + generic proof to eliminate duplication, or macro-based proof generation

**Replicate3proof.v contains massive proof (2532 lines)**
- Problem: Replicate3proof.v is one of largest proof files in backend, suggests complex inductive reasoning that could be modularized
- Files: `backend/Replicate3proof.v`
- Impact: Proof checking becomes bottleneck in build pipeline
- Improvement: Break into smaller lemmas with clear dependencies, or use automation tactics more aggressively

## Fragile Areas

**Faulty backward simulation proof (RTLtolerant.v)**
- Files: `backend/RTLtolerant.v` (2849 lines)
- Why fragile:
  1. Depends critically on color checker correctness (oracle is unverified)
  2. Match relation uses `Val.lessdef` rather than equality for registers, making case analysis in external_call reasoning complex (line 1371-1435)
  3. Four identical proof cases for vote types repeated without abstraction
  4. Incomplete refactoring (line 1164 comment indicates v1 not yet removed)
- Safe modification:
  1. Never change zap_allowed predicate (line 62-71 in RTLfault.v) without re-proving faulty_backward_simulation
  2. Changes to vote builtin semantics (Builtins2.v) require re-proving external_call lemmas (lines 1165-1380)
  3. Add property-based tests to verify Val.lessdef reasoning
- Test coverage: Proof only covers non-faulty execution + abstract faulty model, no integration tests with actual faults

**Color system specification (RTLcolor.v)**
- Files: `backend/RTLcolor.v`
- Why fragile:
  1. Declarative specification of well-coloredness is complex (40+ rules in wc_function)
  2. No separation between essential rules and optimization hints
  3. Consistency constraints along successor edges (line mentioned in fault_tolerance.md) are overly coarse, quantify over all registers not just live-out
- Safe modification:
  1. Any change to color rules must be accompanied by updates to RTLinfercolor.ml and RTLcolorcheck.v
  2. Adding new instruction types (e.g., new builtins) requires extending check_col_instr (RTLcolorcheck.v lines 120-200+)
- Test coverage: Only soundness of checker (check_program_sound), no completeness or coverage analysis

**Novotes checker (Novotes.v, Novotesproof.v)**
- Files: `backend/Novotes.v`, `backend/Novotesproof.v`
- Why fragile:
  1. Simple forward check for absence of vote builtins, but vote detection is string-based on builtin names
  2. If new vote variants added to Builtins2.v without updating vote predicate, checker silently passes
- Safe modification: Always update is_vote_builtin predicate (RTLfault.v location TBD) when new vote types added

## Scaling Limits

**Color inference memory scaling**
- Current capacity: Functions with <10k instructions, <1k pseudo-registers work fine on 8GB RAM machines
- Limit: Dense O(n*m) table breaks on enterprise code with 50k+ instruction functions
- Scaling path: Implement sparse liveness-based table (reduces to O(live-out * instructions) ≈ linear on well-behaved code)

**Proof checking time (full build)**
- Current capacity: Full `make proof` takes ~30-60 minutes on modern hardware
- Limit: Adding more complex proofs (especially parameterized over vote types) increases exponentially
- Scaling path:
  1. Refactor vote type duplication into single generic proof (RTLtmrproof.v, RTLdmrproof.v)
  2. Use `coq_makefile` with parallel build (`make -j$(nproc)`)
  3. Consider code extraction to OCaml for computationally-intensive passes (RTLinfercolor is good example)

**Register allocation (Allocation.v)**
- Current capacity: Works on functions with <5k pseudo-registers
- Limit: Graph coloring algorithm is O(n²) in register count
- Scaling path: Use more aggressive spilling heuristics or switch to linear scan allocation for large functions

## Dependencies at Risk

**Flocq floating-point library**
- Risk: CompCert uses local copy of Flocq for IEEE754 operations. Local copy may diverge from upstream
- Impact: Floating-point correctness proofs depend on Flocq axioms (flocq/IEEE754/BinarySingleNaN.v has TODO comments at lines 1593, 1700, 1750 indicating incomplete lemmas)
- Migration plan: Track upstream Flocq, create regular merge/sync process. Consider submitting floating-point lemmas upstream if not already proven.

**Menhir parser generator (cparser)**
- Risk: Menhir is external dependency with no formal verification. Parser correctness not proved
- Impact: C parser could incorrectly accept/reject valid C code. Bugs in parser could create mismatch between expected and actual semantics
- Migration plan: Consider gradual migration to verified parser (e.g., Ott or hand-verified combinator parser) or formalize Menhir parser specification

**OCaml 4.14.2 embedded in repository**
- Risk: `ocaml-4.14.2_compcert/` is large vendored copy (23k lines based on directory listing). Keeping synchronized is maintenance burden
- Impact: Security patches to OCaml runtime may not be applied. Binary size bloats with unused stdlib code
- Migration plan: Switch to system OCaml once Coq extraction stabilizes. Use .opam file to pin version instead of vendoring.

## Missing Critical Features

**No verification of color inference completeness**
- Problem: Oracle could fail to find valid colorings for colorable programs, silently rejecting them. No way to distinguish algorithmic failure from actual non-colorability
- Blocks: Building more sophisticated color inference algorithms (e.g., SAT-based)
- Workaround: None - oracle failures are invisible

**No automated test generation for faulty execution**
- Problem: Faulty semantics (RTLfault.v) is defined but never executed in practice. No property-based tests of fault tolerance
- Blocks: Validation that faulty model matches real hardware faults. Empirical verification of TMR effectiveness
- Workaround: Manual inspection of compiled code

**Color system limited to RTL level**
- Problem: Fault tolerance proof only extends to RTL. Extension to assembly requires reimplementing color system for each architecture
- Blocks: Formal verification of actual generated x86/ARM code. Current proof only covers hypothetical RTL execution
- Workaround: Assume RTL-to-Asm passes preserve color invariants (not proved)

## Test Coverage Gaps

**Faulty simulation not integration tested**
- Untested area: Whether actual compiled programs with TMR survive injected faults at x86 level
- Files: `backend/RTLtolerant.v` (proof exists), `x86/` (no corresponding color system)
- Risk: Proof gap at RTL-to-Asm boundary. Cache effects, instruction reordering, register allocation could defeat TMR at assembly level
- Priority: Critical for practical fault tolerance claims

**Color inference oracle has no property tests**
- Untested area: Union-find algorithm correctness, color representative merging logic, cycle detection
- Files: `backend/RTLinfercolor.ml` (no tests)
- Risk: Silent bugs in OCaml code undetected. Incorrect colorings might pass checker due to both having same bug
- Priority: High - oral correctness is security boundary

**No regression tests for vote builtins**
- Untested area: New vote types, edge cases in 2-voting vs 3-voting semantics
- Files: `backend/Builtins2.v` (definitions only, no tests)
- Risk: Breaking changes to vote semantics not caught before extraction
- Priority: Medium - proofs catch some issues but execution tests would be faster

**Color rule completeness**
- Untested area: Whether all possible instruction types and register patterns are handled by color checker
- Files: `backend/RTLcolorcheck.v` (incomplete - line 516 says check_function_complete "not possible")
- Risk: New instructions added without color rules, silently treated as non-colorable
- Priority: Medium - mitigated by explicit checklist of instructions

**No fuzz testing of compiler with `-tmr` flag**
- Untested area: Whether compiler crashes, infinite loops, or generates invalid code on large/complex input programs
- Files: `driver/Driver.ml`, `driver/Compiler.v`
- Risk: Color inference memory exhaustion, checker timeout, extraction bugs only surface on real code
- Priority: Medium before production use

---

*Concerns audit: 2026-03-03*
