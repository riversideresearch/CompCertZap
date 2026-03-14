# Analysis of LTL Fault Tolerance Plan

## Overall Verdict

The plan is well-structured and technically sound. The proof chain, phasing, and identification of key challenges are all correct. No major structural flaws. Below are specific observations.

## What the plan gets right

**Proof chain is correct.** The composition:
```
C >=_bw RTL@Two >=_bw RTL@Three >=_bw RTL+TMR@Three >=_bw LTL@Three >=_bw faulty LTL@Two
```
Each link is either already proven or clearly achievable. The backward simulations compose to give the desired end-to-end theorem.

**LTL is the right target.** It's the cheapest post-regalloc IR — you get locations (mregs + stack slots) without the linearization/stacking complexity. The plan's motivation section is accurate.

**V1/V2 staging is well-motivated.** V1 (register-destination faults only) avoids the stack-slot overlap problem entirely. V2 adds `Lsetstack Local` faults, requiring overlap reasoning. This is a natural decomposition.

**Overlap treatment (Design Decision 6) is correct.** Pseudoregisters at RTL are always distinct; `Local` slots at LTL can alias. Requiring protected Local slots to be pairwise `Loc.diff` is the right solution.

**Oracle + verified checker architecture** is sound. The oracle can be as fragile as needed; only the checker matters for soundness.

## Issues worth noting

### 1. Phase 0 already exists

`transf_c_program_to_ltl` is already defined at `Compiler.v:312-316`, and `transf_rtl_program_to_ltl'` (which includes DMR/TMR + Renumber + Allocation) at lines 259-270. The plan could note this. What's missing is only the preservation theorem for this cut, analogous to `transf_c_program_to_rtl_correct`.

### 2. Per-instruction register destruction is under-discussed

At RTL, instructions don't implicitly destroy registers. At LTL, nearly every instruction has a `destroyed_by_*` list — `Lop` destroys `destroyed_by_op op`, `Lload` destroys `destroyed_by_load chunk addr`, `Lgetstack Incoming` destroys `temp_for_parent_frame`, etc. These Vundef writes happen at every step (see `LTL.v:211`, `:217`, `:221`, etc.).

The plan mentions function-entry destruction and caller-save destruction, but the **per-instruction** destruction is more pervasive and affects the color transfer function at every instruction. The color system must ensure that destroyed registers are either not live/tracked or are treated as becoming White. This is probably routine — just force destroyed locations to White in the transfer function — but it deserves explicit mention because it doesn't exist in the RTL color system at all.

### 3. Phase 6 (the hardest part) is the least detailed

The tolerant backward simulation is where all the novel proof work lives. The plan lists what the proof must "budget for" but doesn't sketch the match relation. For reference, RTLtolerant uses:

```coq
match_rs live col faulted rs1 rs2 :=
  if faulted then
    exists c, is_basic c /\ forall r, In r live -> col r <> c -> lessdef (rs1#r) (rs2#r)
  else
    forall r, lessdef (rs1#r) (rs2#r)
```

The LTL analogue would need to operate over `locset` (functions `loc -> val`) instead of `regset`, and the liveness/coloring would be per-instruction-in-block rather than per-node. The overlap constraint would add a well-formedness side condition. Sketching this match relation, even informally, would reduce risk.

### 4. The "witness" concept may be unnecessary

Phase 0.5 introduces "indexed continuation witnesses" and Phase 3 mentions "optionally `LTLwitness.v`". The plan itself says "the witness layer is still useful, but in this standalone plan it is a secondary artifact." Given that the RTL proof has no witness layer, and the plan explicitly disclaims Asm requirements, this seems like complexity imported from the Asm-facing plan. Consider deferring it entirely — it can always be added later if the Asm extension needs it.

### 5. Phase 2 (LTLabi) is vague

The plan introduces `LTLabi.v` for "allocation-produced structural facts" but never says what `wf_program` actually contains. What structural facts does the tolerant proof need that aren't already in the coloring? Candidates might include: well-typed stack slot usage, no overlapping live Local slots used for different purposes, parameter passing conformance. Making this concrete would help evaluate whether it's needed as a separate module.

### 6. Phase 1 should be nearly free

The plan says to "reuse `Allocproof.transf_program_correct`" for RTL+TMR@Three -> LTL@Three. Since both RTL and LTL semantics are parameterized by `VT: vote_type` (via `Section VOTE`), and `Allocproof` should already work for any vote type instantiation, this step should be a direct instantiation — no new proof work, just threading the vote-type parameter. The plan correctly identifies this as reuse but could be more explicit that this is essentially zero-cost.

### 7. Block-local points add real complexity

RTL has one instruction per CFG node, so a program point is just a `node`. LTL has basic blocks, so points become `(node, idx)` pairs. This means:
- Liveness must be computed per-instruction-in-block, not per-node
- The color checker must iterate within blocks
- The match relation must track position within a block

CompCert's existing LTL liveness analysis (used in `Allocation`) already handles this, so there's infrastructure to build on. But the plan should acknowledge this as a meaningful source of proof overhead throughout Phases 3-6, not just a one-time design problem in Phase 0.5.

## No major structural flaws

The proof chain composes correctly. The fault model is a natural lift of the RTL one. The checker architecture is sound. The phasing is reasonable. The technical challenges are all identified, even if some (destroyed regs, match relation shape) could be elaborated further.

The main risk is in Phase 6's proof complexity — but that's inherent to the problem, not a flaw in the plan.
