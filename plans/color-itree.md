# Plan: Use `ITree` with Encoded Color-Location Keys for RTL Color Inference

## Goal

Implement RTL color inference in Coq using `ITree`/`PTree`-backed maps
over a custom key type, instead of:

- the current handwritten OCaml `Array<Hashtbl<...>>` representation, or
- a fresh-ID allocator for union-find elements.

The key idea is to represent union-find elements as a Coq datatype:

```coq
Inductive color_key :=
| KRed | KGreen | KBlue | KWhite | KPink
| KLoc (pc : positive) (r : positive).
```

and instantiate `ITree`/`UnionFind.UF` by providing an injective
`color_key -> positive` encoding.

## Why this design is interesting

- It removes the dense-node-numbering assumption entirely.
- It avoids an explicit allocator state for fresh union-find IDs.
- It keeps the key space close to the conceptual problem:
  colors and `(pc, reg)` locations.
- It reuses CompCert's existing `INDEXED_TYPE`, `ITree`, and `UnionFind`
  infrastructure instead of introducing a bespoke map.

## Main tradeoff

This design still needs an encoding from `(pc, reg)` pairs to
`positive`. The encoding is the main new proof/engineering work.

The performance risk is that encoded keys are larger than raw `positive`
nodes or registers, making `PTree` paths deeper in extracted code.
However, this is still likely simpler than building a true pair-key map
from scratch.

## Existing infrastructure

- `INDEXED_TYPE` in `lib/Maps.v`
- `ITree(X)` in `lib/Maps.v`
- `UnionFind.UF(M)` in `lib/UnionFind.v`

Recommended module structure:

1. define `IndexedColorKey <: INDEXED_TYPE`
2. define `ColorTree := ITree(IndexedColorKey)` if a tree is needed
3. define `ColorUF := UnionFind.UF(ITree(IndexedColorKey))`

## High-level design

## Element type

Use one union-find element type for both color constants and program
locations:

```coq
Inductive color_key :=
| KRed | KGreen | KBlue | KWhite | KPink
| KLoc (pc : positive) (r : positive).
```

This yields direct constraints such as:

- `KLoc pc r = KLoc succ r`
- `KLoc pc arg = KWhite`
- `KLoc succ res = KWhite`
- `KLoc pc arg = KLoc succ res`

## Encoding strategy

Use an injective `index : color_key -> positive` with two layers:

1. Reserve a few small odd keys for the five colors.
2. Encode all `KLoc pc r` keys as even positives containing a quoted
   encoding of `(pc, r)`.

This gives an immediate disjointness argument:

- colors are odd
- locations are even

## Recommended pair encoding

Use a self-delimiting quoted encoding of positives.

### Quote one positive

Encode one positive by mapping each original bit to two bits and ending
with a terminator:

- original `0` bit -> `00`
- original `1` bit -> `10`
- terminator -> `11`

Represent this as a structurally recursive function on `positive`,
preferably in accumulator style.

### Encode a pair

Encode `(pc, r)` by concatenating:

```text
quote(pc) ++ quote(r)
```

and then wrap with an outer even-location tag.

Recommended ordering:

- encode `pc` first
- then `r`

This should maximize common prefixes for keys belonging to the same RTL
node, which is favorable for `PTree` locality.

## Phase 1: Prototype the key encoding

## Files

- `backend/RTLinfercolor.v` or a temporary scratch module

## Actions

1. Define `color_key`.
2. Define decidable equality on `color_key`.
3. Define:
   - `quote_acc : positive -> positive -> positive`
   - `quote : positive -> positive`
4. Define `index : color_key -> positive`.
5. Pick explicit constants for:
   - `KRed`
   - `KGreen`
   - `KBlue`
   - `KWhite`
   - `KPink`

## Recommended indexing shape

Use something of the form:

```coq
Definition index (k : color_key) : positive :=
  match k with
  | KRed => ...
  | KGreen => ...
  | KBlue => ...
  | KWhite => ...
  | KPink => ...
  | KLoc pc r => xO (quote_acc pc (quote_acc r xH))
  end.
```

The exact odd constants for colors do not matter as long as they are
distinct and remain disjoint from the `xO ...` location form.

## Exit criteria

- The encoding compiles.
- The mixed-case disjointness story is obvious from the definitions.

## Phase 2: Prove the encoding injective

## Files

- `backend/RTLinfercolor.v`

## Actions

1. Define a decoder for one quoted positive:
   - enough to recover one encoded positive and the unconsumed suffix
2. Prove a lemma of the form:

```coq
decode_one (quote_acc p rest) = (p, rest).
```

3. Prove a location decoder lemma:

```coq
decode_loc_payload (quote_acc pc (quote_acc r xH)) = (pc, r).
```

4. Use these lemmas to prove:

```coq
index x = index y -> x = y.
```

## Proof structure

Split into cases:

1. color vs color: finite case analysis
2. color vs location: contradiction by parity/tag shape
3. location vs location: decode the payload twice

## Exit criteria

- `IndexedColorKey.index_inj` is proved.

## Phase 3: Instantiate `ITree` and `UnionFind`

## Files

- `backend/RTLinfercolor.v`

## Actions

1. Package the key type as:

```coq
Module IndexedColorKey <: INDEXED_TYPE.
```

2. Instantiate:

```coq
Module ColorTree := ITree(IndexedColorKey).
Module ColorUF := UnionFind.UF(ColorTree).
```

3. Add small helper constructors:

- `loc_key pc r := KLoc pc r`
- `union_loc_loc`
- `union_loc_color`
- `sameclass_color`

## Exit criteria

- The union-find instantiation typechecks.
- Basic helper functions are in place.

## Phase 4: Re-express color inference using `color_key`

## Files

- `backend/RTLinfercolor.v`

## Actions

1. Port the current OCaml constraint generation to Coq, using:
   - `KLoc pc r`
   - `KRed`, `KGreen`, `KBlue`, `KWhite`, `KPink`
2. Replace all per-node hash-table lookups with direct key construction.
3. Keep the overall instruction-by-instruction logic as close as possible
   to `backend/RTLinfercolor.ml`.
4. Define the exported coloring by comparing the representative of
   `KLoc pc r` against the representatives of the five color constants.

## Defaulting policy

Preserve the current behavior:

- unconstrained location -> default `Red`
- representative not matched to a color constant -> default `Red`

## Exit criteria

- `infer_coloring : function -> PMap.t Regset.t -> option (node -> reg -> color)`
  is implemented in Coq using `ColorUF`.

## Phase 5: Integrate with `RTLcolorcheck`

## Files

- `backend/RTLcolorcheck.v`
- `extraction/extraction.v`

## Actions

1. Replace the `Parameter infer_coloring` with a direct Coq definition or
   reference.
2. Remove the extraction override for `RTLcolorcheck.infer_coloring`.
3. Ensure `Separate Extraction` emits the Coq implementation.

## Exit criteria

- The checker path uses the Coq implementation with no handwritten OCaml
  oracle in the loop.

## Phase 6: Validation

## Checks

1. `make backend/RTLinfercolor.vo`
2. `make backend/RTLcolorcheck.vo`
3. `make extraction`
4. `make ccomp`

## Functional spot checks

1. Compile a representative file with `./ccomp -tmr`.
2. Confirm previously accepted well-colored programs are still accepted.
3. Confirm sparse node numbering is no longer a latent assumption of the
   implementation.

## Performance checks

Measure at least:

1. one moderate function
2. one large function

Compare inference/checker time against:

- the current OCaml implementation
- any per-node-state Coq prototype, if one exists

This comparison is important because the `ITree` route trades a simpler
logical model for potentially larger keys and deeper `PTree` traversals.

## Risks and mitigations

## Risk 1: Encoding proof takes longer than expected

Mitigation:

- keep the encoding self-delimiting and decoder-oriented
- avoid clever bit interleavings in the first version
- prove one decoder lemma and derive injectivity from it

## Risk 2: Extracted performance is disappointing

Mitigation:

- benchmark before deleting alternative implementations
- compare against a per-node-state Coq design
- optimize encoding only after measuring

## Risk 3: `ITree` path is underused in the current tree

Mitigation:

- keep the wrapper small and local
- avoid depending on fancy `ITree` properties beyond `get`/`set`
- fall back to per-node state plus fresh IDs if this route becomes too
  awkward

## Recommended implementation order

1. Prototype and prove `IndexedColorKey.index_inj`.
2. Instantiate `ColorUF`.
3. Port one or two easy instruction cases (`Inop`, `Iop`) first.
4. Complete the remaining instruction cases.
5. Hook into `RTLcolorcheck`.
6. Benchmark before removing alternatives.

## Deliverables

1. An `IndexedColorKey` module for color/location keys.
2. A Coq implementation of color inference using `ITree` + `UnionFind`.
3. No extraction override for color inference.
4. Build and benchmark data sufficient to decide whether this design is
   acceptable long-term.
