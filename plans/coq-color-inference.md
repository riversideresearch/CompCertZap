# Plan: Move RTL Color Inference from OCaml to Coq

## Goal

Replace the handwritten OCaml color inference oracle in
`backend/RTLinfercolor.ml` with a Coq implementation that is extracted as
ordinary compiler code.

This is **not** a plan to verify the inference algorithm. The checker
soundness theorem already depends only on the returned coloring passing
`RTLcolorcheck.check_col_function`, not on any semantic specification of
the inference procedure itself.

## Why this is worth doing

- Removes the bespoke extracted-constant hook at
  `extraction/extraction.v:87`.
- Eliminates the current untrusted handwritten OCaml module from the
  compile path.
- Fixes the sparse-node-numbering fragility naturally by using map keys
  instead of array indexes.
- Keeps the trust story simpler: the algorithm remains unchecked, but it
  is no longer an external oracle living outside the Coq/extraction path.

## Non-goals

- Do **not** prove correctness or completeness of color inference in this
  change.
- Do **not** redesign the color checker specification.
- Do **not** optimize aggressively before a working extracted version
  exists.

## Current baseline

- `backend/RTLcolorcheck.v:74-75` declares `infer_coloring` as a Coq
  parameter.
- `extraction/extraction.v:87` replaces that parameter with
  `RTLinfercolor.infer_coloring`.
- `backend/RTLinfercolor.ml` implements an imperative union-find solver
  using arrays for nodes and hash tables for registers.
- `backend/Tunneling.v` already demonstrates that CompCert's Coq-side
  `lib/UnionFind.v` is usable in extracted code.

## Recommended design

Implement a new Coq module that computes colorings directly from RTL code
and liveness sets using `UnionFind.UF(PTree)`.

### Representation

Use union-find elements keyed by a single `positive`.

- Reserve a small fixed set of keys for the five colors:
  `Red`, `Green`, `Blue`, `White`, `Pink`.
- Encode each `(pc, r)` pair as a distinct positive key.
- Query the final coloring by comparing the representative of
  `key_of_loc pc r` against the representatives of the five color keys.
- Default to `Red` when a key is unconstrained or maps to no known color
  representative, matching the current OCaml fallback.

This avoids the array-density assumption entirely.

### State shape

Prefer a pure persistent state:

- `uf : U.t` for equivalence classes.
- small helper functions to union one location with another or with a
  color constant.
- no mutable arrays or hash tables.

The algorithm should remain a single pass over function parameters and
instructions, mirroring the current OCaml constraint generation.

## File layout decision

Use a Coq file named `backend/RTLinfercolor.v`.

Reason:

- it preserves the existing module name `RTLinfercolor`
- it lets the extracted module naturally replace the handwritten one
- it minimizes driver/extraction churn

Migration recommendation:

1. Add `backend/RTLinfercolor.v`.
2. Remove the `Extract Constant RTLcolorcheck.infer_coloring => ...`
   override.
3. Keep the old OCaml file around only until the extracted pipeline is
   building and benchmarked.
4. Delete `backend/RTLinfercolor.ml` once the new path is stable.

## Phase 1: Build a minimal Coq inference module

## Files

- `backend/RTLinfercolor.v` (new)

## Actions

1. Import the same RTL/color/liveness modules currently used by
   `RTLcolorcheck`.
2. Instantiate union-find:
   `Module U := UnionFind.UF(PTree)`.
3. Define a key encoding layer:
   - color keys
   - `(pc, reg)` keys
   - helper lemmas or comments documenting injectivity assumptions
4. Define color decoding from union-find representatives.
5. Expose:
   `infer_coloring : function -> PMap.t Regset.t -> option (node -> reg -> color)`.

## Exit criteria

- `backend/RTLinfercolor.v` typechecks in isolation.
- The extracted interface matches the current `RTLcolorcheck` parameter
  type exactly.

## Phase 2: Port the constraint-generation logic

## Files

- `backend/RTLinfercolor.v`

## Actions

1. Port the helper utilities from the OCaml implementation:
   - builtin arg/result register collection
   - function register collection if still useful for diagnostics
2. Re-express `instr_constraints` in Coq as a pure function
   `add_instr_constraints : live_out -> pc -> instruction -> U.t -> U.t`.
3. Mirror the current cases instruction-by-instruction:
   - `Inop`
   - `Iop`
   - `Iload`
   - `Istore`
   - `Icall`
   - `Itailcall`
   - `Ibuiltin`
   - `Icond`
   - `Ijumptable`
   - `Ireturn`
4. Handle function-entry parameter whitening exactly as the OCaml version
   does at the entrypoint.
5. Fold over `fn_code` with `PTree.fold` to build the final union-find
   structure.

## Notes

- Keep the implementation structurally close to
  `backend/RTLinfercolor.ml` for the first version.
- Avoid premature abstraction if it obscures parity with the existing
  algorithm.

## Exit criteria

- Every current OCaml constraint case has a direct Coq counterpart.
- No array indexing or dense-node assumption remains.

## Phase 3: Produce the exported coloring function

## Files

- `backend/RTLinfercolor.v`

## Actions

1. Define `color_of_repr : U.t -> positive -> color`.
2. Define `coloring_of_uf : U.t -> node -> reg -> color`.
3. Return `Some (coloring_of_uf uf)` from `infer_coloring`.
4. Preserve the current default behavior for unconstrained registers:
   return `Red`.

## Optional diagnostics

The current OCaml code prints instruction/register counts and elapsed
time. Do not carry this into the first Coq version unless it is easy to
express through extraction-safe hooks. Favor getting rid of custom
runtime support before reintroducing diagnostics.

## Exit criteria

- `check_function` can call the Coq-defined `infer_coloring` without any
  signature changes.

## Phase 4: Remove the extracted-constant hook

## Files

- `backend/RTLcolorcheck.v`
- `extraction/extraction.v`

## Actions

1. Replace the `Parameter infer_coloring` in `RTLcolorcheck.v` with an
   ordinary definition or direct reference to `RTLinfercolor.infer_coloring`.
2. Remove the line
   `Extract Constant RTLcolorcheck.infer_coloring => "RTLinfercolor.infer_coloring".`
3. Re-run extraction so `Separate Extraction` emits the Coq-defined
   `RTLinfercolor` module into `extraction/`.

## Design choice

Prefer eliminating the parameter entirely rather than keeping a parameter
plus extraction override. That makes the dependency explicit in Coq and
removes the last oracle-shaped interface.

## Exit criteria

- The extraction file no longer special-cases color inference.
- The generated extracted code contains a module for `RTLinfercolor`.

## Phase 5: Build integration and cleanup

## Files

- `backend/RTLinfercolor.ml` (delete after cutover)
- `README.md`
- `AGENTS.md`
- `doc/fault_tolerance.md`
- any notes/docs still describing the implementation as handwritten OCaml

## Actions

1. Update documentation to say color inference is implemented in Coq and
   extracted to OCaml.
2. Remove or archive references to the old handwritten oracle.
3. If useful, keep a short note that the algorithm is still unverified
   even though it now lives in Coq.

## Exit criteria

- No user-facing docs claim the oracle is handwritten OCaml.

## Phase 6: Validation

## Build checks

1. `make backend/RTLinfercolor.vo`
2. `make backend/RTLcolorcheck.vo`
3. `make extraction`
4. `make ccomp`

## Behavioral checks

1. Compile a representative TMR input with `./ccomp ... -tmr`.
2. Confirm the color checker still accepts known-good examples.
3. Confirm a deliberately malformed coloring example still fails through
   the checker path if such a test already exists.

## Performance checks

Run at least one moderate and one large example through the `-tmr`
 pipeline and compare checker/inference time against the current
 baseline.

This is the main practical risk because `lib/UnionFind` is persistent,
while the handwritten OCaml implementation is imperative and mutable.

## Phase 7: Optional follow-up cleanup

Once the Coq port is stable, consider follow-up refactors that are not
required for the initial migration:

1. Split constraint generation into small helpers per opcode family.
2. Factor repeated “preserve colors for live-out except these registers”
   patterns.
3. Add a narrow executable test harness for inference/checker behavior.
4. Revisit whether the algorithm should be restructured as one
   unification pass plus a smaller propagation layer, as hinted in
   existing notes.

## Risks and mitigations

## Risk 1: Extracted performance regresses too much

Mitigation:

- keep the first implementation simple and sparse
- benchmark before deleting the handwritten OCaml version
- if necessary, optimize the Coq data representation before changing the
  algorithm itself

## Risk 2: Key encoding becomes awkward or error-prone

Mitigation:

- isolate it behind a tiny helper layer
- keep the encoding obviously disjoint between color constants and
  `(pc, reg)` locations
- document the encoding invariants at the definition site

## Risk 3: Wiring churn around extraction is larger than expected

Mitigation:

- preserve the `RTLinfercolor` module name
- cut over in two steps: add Coq module first, then remove the extraction
  override

## Recommended implementation order

1. Add `backend/RTLinfercolor.v` with key encoding and minimal API.
2. Port the OCaml constraint cases one by one.
3. Hook `RTLcolorcheck` to the Coq implementation.
4. Remove the extraction override.
5. Rebuild extraction and `ccomp`.
6. Benchmark before deleting the old OCaml file.

## Deliverables

1. New `backend/RTLinfercolor.v` implementing executable color inference.
2. No extracted-constant override for color inference.
3. Successful `make extraction` and `make ccomp`.
4. Updated docs reflecting that the oracle now lives in Coq, while
   remaining unverified.
