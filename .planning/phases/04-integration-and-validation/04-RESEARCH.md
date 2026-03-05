# Phase 4: Integration and Validation - Research

**Researched:** 2026-03-04
**Domain:** CompCert build system integration -- Coq proof compilation, OCaml extraction, binary compilation, end-to-end testing
**Confidence:** HIGH

## Summary

Phase 4 is the final integration and validation phase. All prior phases are complete:
- Phase 1 created `backend/ProofLiveness.v` (conservative liveness analysis) -- zero Admitted, .vo exists
- Phase 2 updated `backend/RTLcolor.v` and `backend/RTLcolorcheck.v` to reference `ProofLiveness.analyze` and completed `check_col_instr_sound` -- zero Admitted, .vo files exist
- Phase 3 completed the faulty backward simulation in `backend/RTLtolerant.v` with liveness-bounded `match_rs` -- zero Admitted, .vo exists (3.5 MB)

The remaining work is to verify that the full build pipeline works end-to-end: (1) rebuild `driver/Complements.vo` which contains the top-level `transf_c_program_to_rtl_preservation_faulty` theorem, (2) confirm zero Admitted across all touched files, and (3) rebuild the `ccomp` compiler binary and verify it can compile C programs with `-tmr`.

Critically, **no source changes are expected to Complements.v**. The file does not directly reference `ProofLiveness` or `Liveness` -- it consumes `faulty_backward_simulation` (from `RTLtolerant`) and `check_program_sound` (from `RTLcolorcheck`) which internally use `ProofLiveness.analyze`. The theorem signature is unchanged: `faulty_backward_simulation : forall prog, wc_program prog -> backward_simulation ...`. Since `Complements.v` calls it at line 558 as `apply faulty_backward_simulation` and feeds it `RTLcolorcheck.check_program_sound`, the existing proof should work without modification.

**Primary recommendation:** This is a pure verification/build phase. Run `make driver/Complements.vo`, then `make check-admitted`, then `make ccomp`, and finally test the binary with `ccomp -tmr -S`. No code changes expected; if Complements.vo fails to build, diagnose and fix the API mismatch (most likely a `live` parameter or `wc_program` definition change).

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|-----------------|
| INTG-01 | driver/Complements.vo rebuilds successfully (no source changes expected) | Complements.v uses `faulty_backward_simulation` (line 558) and `check_program_sound` (line 559) -- both are unchanged signatures from RTLtolerant and RTLcolorcheck. Dependency chain: Complements.v -> RTLtolerant.vo + RTLcolorcheck.vo -> ProofLiveness.vo. All upstream .vo files already exist. |
| INTG-02 | `make check-admitted` passes for all touched files | The `check-admitted` target greps all .v files in FILES for `admit\|Admitted\|ADMITTED`. Verified: ProofLiveness.v has 0 Admitted, RTLcolor.v has 0, RTLcolorcheck.v has 0 (line 487 is commented out: `(* Admitted. *)`), RTLtolerant.v has 0, Complements.v has 0. |
| INTG-03 | `make ccomp` succeeds (compiler binary builds end-to-end) | Build chain: proof -> extraction -> OCaml compilation. The extraction via `extraction/extraction.v` wires `RTLcolorcheck.infer_coloring` to `RTLinfercolor.infer_coloring` (line 87). ProofLiveness is proof-only -- it is not extracted and does not appear in `extraction/extraction.v`. The existing `ccomp` binary already works with `-tmr` (tested: `ccomp -tmr -S` produces correct x86-64 assembly). After rebuilding, the binary should work identically. |
</phase_requirements>

## Standard Stack

### Core
| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| Coq | 8.20.0 | Proof checker -- compiles .v to .vo | Project build infrastructure |
| GNU Make | system | Build orchestration | CompCert's Makefile drives proof, extraction, OCaml compilation |
| OCaml | 4.14.2 | Compiler binary target | CompCert extracts Coq to OCaml, then compiles to native binary |

### Supporting
| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| coqchk | 8.20.0 | Independent proof checker | `make check-proof` for extra validation (optional) |
| grep | system | Admitted check | `make check-admitted` scans for proof holes |

### Alternatives Considered
| Instead of | Could Use | Tradeoff |
|------------|-----------|----------|
| `make check-admitted` (grep) | `coqchk` (type-checker) | `coqchk` is stronger (verifies proof terms) but much slower; grep catches the obvious holes |

## Architecture Patterns

### Build Chain
```
make proof         ->  All .v files compiled to .vo (Coq proof checking)
make extraction    ->  extraction/extraction.v runs Coq extraction to OCaml
make ccomp         ->  Makefile.extr compiles extracted OCaml + handwritten OCaml to ccomp binary
```

### Dependency Chain for Complements.vo
```
driver/Complements.vo depends on:
  backend/RTLtolerant.vo     [Phase 3 output - already built]
  backend/RTLcolorcheck.vo   [Phase 2 output - already built]
  backend/RTLfault.vo        [unchanged]
  backend/RTLagreement.vo    [unchanged]
  backend/Novotes.vo         [unchanged]
  backend/Novotesproof.vo    [unchanged]
  backend/Builtins2.vo       [unchanged]
  x86/Asmagreement.vo        [unchanged]
  driver/Compiler.vo         [unchanged]
  ... (all standard CompCert passes)
```

### Key Theorem Chain in Complements.v (lines 546-570)
```
transf_c_program_to_rtl_preservation_faulty:
  1. faulty_backward_simulation (RTLtolerant) -- 3-voting >= faulty
     wc_program from check_program_sound (RTLcolorcheck)
  2. transf_rtl_program_to_rtl'_preservation -- RTL-to-RTL passes (DMR/TMR/Renumber)
  3. transf_c_program_to_rtl'_preservation' -- C-to-RTL backward sim + weak agreement
  4. behavior_improves_trans (composition)
```

### Pattern 1: No Source Changes Expected
**What:** Complements.v does not import ProofLiveness or Liveness directly. It consumes upstream results through their public API.
**When to use:** When the integration phase only needs to rebuild, not modify.
**Evidence:**
```coq
(* Complements.v line 558-559: *)
2: { apply faulty_backward_simulation.
     apply RTLcolorcheck.check_program_sound; auto. }
```
Both `faulty_backward_simulation` and `check_program_sound` maintain their original signatures:
- `faulty_backward_simulation : forall prog, wc_program prog -> backward_simulation (RTL.semantics Three prog) (faulty_semantics prog)`
- `check_program_sound : forall p, check_program p = true -> wc_program p`

The `wc_program` type flows through `wc_function` which now internally uses `ProofLiveness.analyze` instead of `Liveness.analyze`, but this is an implementation detail hidden behind the same type signature.

### Pattern 2: Testing ccomp with -tmr
**What:** Verify the compiled binary works by generating assembly from a trivial C program.
**When to use:** INTG-03 validation.
**Example:**
```bash
echo 'int main() { return 0; }' > /tmp/test_tmr.c
./ccomp /tmp/test_tmr.c -tmr -S -o /tmp/test_tmr.s
echo $?  # should be 0
```
Use `-S` flag to stop at assembly generation (avoids linker failures due to missing runtime library installation). The `-tmr` flag triggers TMR replication and the color checker, which exercises the full pipeline including `check_program` -> `infer_coloring` -> `check_function`.

### Anti-Patterns to Avoid
- **Making unnecessary source changes to Complements.v:** The file should compile as-is. If it doesn't, the issue is in an upstream file's API, not in Complements.v itself.
- **Running `make all` as first step:** Start with `make driver/Complements.vo` to isolate proof issues from extraction/OCaml issues. Build incrementally.
- **Skipping the TMR test:** Building `ccomp` is necessary but not sufficient. Must verify `-tmr` flag works, which exercises the color checker.
- **Using `make -j` for first proof rebuild:** When dependencies have changed, parallel make can occasionally hit ordering issues. Use `make driver/Complements.vo` (single target) first.

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Full build | Manual coqc commands | `make driver/Complements.vo` | Makefile handles VPATH, include paths, dependency ordering |
| Admitted checking | Manual grep | `make check-admitted` | Already correctly configured to scan all FILES |
| Binary build | Manual ocamlfind/ocamlopt | `make ccomp` | Makefile.extr handles extraction dependencies, link order, libraries |
| Test program | Complex C programs | `int main() { return 0; }` with `-tmr -S` | Minimal program that still exercises TMR + color checker |

**Key insight:** This phase is entirely about running existing build targets and verifying their outputs. No new code should be written.

## Common Pitfalls

### Pitfall 1: Stale .vo Files Causing Build Confusion
**What goes wrong:** `make driver/Complements.vo` says "nothing to do" even though upstream files changed, because timestamps are out of order.
**Why it happens:** If `Complements.vo` somehow has a newer timestamp than its dependencies, make skips recompilation.
**How to avoid:** Delete `driver/Complements.vo` before building, or run `make -B driver/Complements.vo` to force rebuild. Currently, `Complements.vo` does not exist (confirmed), so this is not an issue for the first build.
**Warning signs:** `make` says "Nothing to be done" but the .vo file was never built with the new ProofLiveness-based dependencies.

### Pitfall 2: check-admitted Catching Commented-Out Admitted
**What goes wrong:** `make check-admitted` finds `Admitted` in a comment and exits with error.
**Why it happens:** The grep pattern `grep -w 'Admitted'` matches inside comments. RTLcolorcheck.v line 487 has `(* Admitted. *)` which is commented out.
**How to avoid:** The current `check-admitted` target uses `grep -w 'admit\|Admitted\|ADMITTED'` against `.v` files. Verified: the grep `-w` flag requires word boundaries, and `(* Admitted. *)` is `Admitted` as a word, so it WILL match even in a comment. However, the actual `check-admitted` target in the Makefile (line 437) is: `grep -w 'admit\|Admitted\|ADMITTED' $^`. This will match commented-out Admitted. If this is a problem, the commented line must be removed or altered.
**Warning signs:** `check-admitted` fails pointing to RTLcolorcheck.v line 487 despite the Admitted being in a comment.

### Pitfall 3: Extraction Timestamp Invalidation
**What goes wrong:** `make ccomp` triggers full re-extraction because `extraction/STAMP` is older than newly rebuilt .vo files.
**Why it happens:** `extraction/STAMP` depends on `$(FILES:.v=.vo)`. Rebuilding `Complements.vo` or `RTLtolerant.vo` makes STAMP older. Re-extraction takes a long time.
**How to avoid:** This is expected behavior and not avoidable without `touch extraction/STAMP`. Since ProofLiveness is proof-only and not extracted, re-extraction will produce identical OCaml code, just with a time cost. Alternatively, if no .v files changed (only .vo files were rebuilt), you could `touch extraction/STAMP` to skip re-extraction. But this is safe ONLY if no Coq source file was modified.
**Warning signs:** `make ccomp` running extraction again for 5+ minutes even though no source files changed.

### Pitfall 4: Linker Failure on TMR Test
**What goes wrong:** `ccomp test.c -tmr -o test` fails with "cannot find -lcompcert".
**Why it happens:** The runtime library is not installed or not in the library path. The development build doesn't install runtime.
**How to avoid:** Use `ccomp -S` flag (stop at assembly) or `ccomp -c` (stop at object). The `-S` flag is sufficient to verify the full compiler pipeline including TMR insertion and color checking.
**Warning signs:** Linker errors about `-lcompcert` or missing `__compcert_*` symbols.

### Pitfall 5: wc_program Definition Change Breaking Complements.v
**What goes wrong:** `faulty_backward_simulation` has a different signature than expected because `wc_program` (or `wc_function`) definition changed.
**Why it happens:** Phase 2 changed `wc_function` to use `ProofLiveness.analyze` instead of `Liveness.analyze`. If `wc_program` or `wc_function` is transparent (not opaque), Coq may try to unfold it during unification, causing issues.
**How to avoid:** This should not happen because `wc_program` is an inductive, and its type signature has not changed -- only the analysis it references internally changed. `check_program_sound` still produces `wc_program`. `faulty_backward_simulation` still consumes `wc_program`. The types compose.
**Warning signs:** Type errors in Complements.v mentioning `ProofLiveness.analyze` -- this would indicate a signature leak.

## Code Examples

### Build Sequence for Integration
```bash
# Step 1: Build Complements.vo (tests INTG-01)
make driver/Complements.vo

# Step 2: Check for Admitted proofs (tests INTG-02)
make check-admitted

# Step 3: Build ccomp binary (tests INTG-03 partial)
make ccomp

# Step 4: Test ccomp with TMR (tests INTG-03 complete)
echo 'int main() { return 0; }' > /tmp/test_tmr.c
./ccomp /tmp/test_tmr.c -tmr -S -o /tmp/test_tmr.s
echo "TMR test exit code: $?"
```

### Diagnosing Complements.vo Build Failure
```bash
# If make driver/Complements.vo fails, check which theorem is broken:
# The error will be at the `apply` or `eapply` that references the changed theorem.
# Most likely candidates:
#   Line 558: apply faulty_backward_simulation
#   Line 559: apply RTLcolorcheck.check_program_sound

# Check the actual theorem signature:
grep -A3 'Theorem faulty_backward_simulation' backend/RTLtolerant.v
grep -A3 'Lemma check_program_sound' backend/RTLcolorcheck.v
```

### Handling Commented-Out Admitted
```bash
# If check-admitted fails on RTLcolorcheck.v line 487:
# The line is: (* Admitted. *)
# Options:
#   1. Remove the comment entirely
#   2. Change to: (* Previously Admitted, now proved. *)
#   3. Accept the false positive (the grep is line-oriented, not comment-aware)

# Check what check-admitted actually matches:
grep -nw 'admit\|Admitted\|ADMITTED' backend/RTLcolorcheck.v
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| Liveness.analyze in RTLcolor, RTLcolorcheck, RTLtolerant | ProofLiveness.analyze everywhere | Phases 1-3 (this project) | Complements.v unaffected (no direct reference) |
| check_col_instr_sound Admitted | Fully proved | Phase 2 | check_program_sound now fully grounded |
| faulty_backward_simulation with Admitted holes | Fully proved, zero Admitted | Phase 3 | Top-level theorem chain is complete |

**Deprecated/outdated:**
- The commented-out proof scripts in Complements.v (lines 74-248, 280-639) are legacy code from earlier development. They do not affect compilation and should not be uncommented.

## Open Questions

1. **check-admitted vs commented Admitted**
   - What we know: RTLcolorcheck.v line 487 contains `(* Admitted. *)` inside a Coq comment. The `check-admitted` Makefile target uses `grep -w 'Admitted'` which may match inside comments.
   - What's unclear: Whether the grep pattern actually matches `(* Admitted. *)` as a word boundary match. The `.*` in `(* Admitted. *)` means `Admitted` has word boundaries on both sides (space before, period after).
   - Recommendation: Test `make check-admitted` first. If it fails, remove or rephrase the comment. This is a 1-second fix.

2. **Extraction rebuild time**
   - What we know: `make ccomp` triggers re-extraction if any .vo file is newer than `extraction/STAMP`. All four .vo files from Phases 1-3 are newer. Re-extraction takes 5-10 minutes.
   - What's unclear: Whether `touch extraction/STAMP` is safe since no Coq source files were logically changed in a way that affects extraction output.
   - Recommendation: Let extraction re-run. It produces identical output since ProofLiveness is not extracted. The time cost is acceptable for final validation.

## Validation Architecture

### Test Framework
| Property | Value |
|----------|-------|
| Framework | Coq 8.20.0 proof checker + GNU Make + OCaml 4.14.2 compiler |
| Config file | `Makefile`, `Makefile.extr`, `_CoqProject` |
| Quick run command | `make driver/Complements.vo` |
| Full suite command | `make driver/Complements.vo && make check-admitted && make ccomp` |

### Phase Requirements to Test Map
| Req ID | Behavior | Test Type | Automated Command | File Exists? |
|--------|----------|-----------|-------------------|-------------|
| INTG-01 | Complements.vo rebuilds successfully | integration (build) | `make driver/Complements.vo` | Source exists; .vo does not exist yet |
| INTG-02 | check-admitted passes for all touched files | integration (grep) | `make check-admitted` | N/A -- Makefile target |
| INTG-03 | ccomp binary builds and works with -tmr | integration (build + run) | `make ccomp && echo 'int main(){return 0;}' > /tmp/t.c && ./ccomp /tmp/t.c -tmr -S -o /tmp/t.s` | ccomp binary exists (will be rebuilt) |

### Sampling Rate
- **Per task commit:** `make driver/Complements.vo` (proof chain verification)
- **Per wave merge:** `make driver/Complements.vo && make check-admitted && make ccomp`
- **Phase gate:** All three commands succeed + TMR test passes

### Wave 0 Gaps
None -- existing build infrastructure covers all phase requirements. No new test files, no new Makefile targets needed. The only possible gap is the commented-out `(* Admitted. *)` in RTLcolorcheck.v which may need removal (1-line change).

## Sources

### Primary (HIGH confidence)
- `driver/Complements.v` (905 lines) -- direct inspection of `transf_c_program_to_rtl_preservation_faulty` theorem and its proof (lines 546-570)
- `.depend` file -- confirmed Complements.vo dependency chain includes RTLtolerant.vo and RTLcolorcheck.vo
- `Makefile` (445 lines) -- verified `check-admitted` target (line 436-438), `ccomp` target (line 278-279), `extraction` target (line 263-273)
- `backend/RTLtolerant.v` -- verified `faulty_backward_simulation` signature (lines 3232-3235) and section structure (Section TOLERANCE with `Variable prog` and `Hypothesis WC_prog`)
- `backend/RTLcolorcheck.v` -- verified `check_program_sound` signature (lines 530-531)
- `extraction/extraction.v` -- confirmed ProofLiveness is not extracted; only `RTLcolorcheck.infer_coloring` is wired (line 87)
- Live testing -- `ccomp -tmr -S` works on current binary, producing valid x86-64 assembly

### Secondary (MEDIUM confidence)
- Phase 3 VERIFICATION.md -- confirmed all FSIM requirements satisfied, zero Admitted, .vo artifacts exist

### Tertiary (LOW confidence)
- None

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH -- pure build system verification, all tools already configured and working
- Architecture: HIGH -- full dependency chain traced through Makefile, .depend, and Coq source imports
- Pitfalls: HIGH -- all pitfalls identified through direct inspection and live testing of current build
- No-change prediction: HIGH -- verified Complements.v does not reference ProofLiveness/Liveness, confirmed theorem signatures are unchanged

**Research date:** 2026-03-04
**Valid until:** Indefinite (build system is stable, no external dependencies)
