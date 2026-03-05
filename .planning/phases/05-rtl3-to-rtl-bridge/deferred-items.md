# Deferred Items: Phase 05 RTL3-to-RTL Bridge

## Pre-existing Issue: transf_c_program_to_rtl_preservation_faulty Admitted

**File:** `driver/Complements.v` line 555
**Status:** Admitted (pre-existing, not introduced by this plan)
**Root cause:** De-parameterization (splitting RTL/RTL3 into separate modules) broke the proof chain.

The original proof relied on DMR/TMR forward simulation being polymorphic over vote_type, allowing:
```
faulty(tp) -> RTL3(tp) -> RTL3(p') -> C(p)
```

After de-parameterization, DMR/TMR proofs (`RTLdmrproof.v`, `RTLtmrproof.v`) only cover `RTL.semantics`, not `RTL3.semantics`. The chain breaks at RTL3(tp) -> RTL3(p') because there is no `forward_simulation (RTL3.semantics p') (RTL3.semantics tp)` for the DMR/TMR pipeline.

**Fix requires:** Prove `forward_simulation (RTL3.semantics p') (RTL3.semantics tp)` for DMR/TMR+Renumber. The proof structure is identical to the existing RTL versions but uses `RTL3.step` instead of `RTL.step`. This is straightforward but involves duplicating ~3000 lines of proof across RTLdmrproof.v and RTLtmrproof.v (or refactoring them to be parametric).

**Workaround considered:** Going through RTL(tp) via `rtl3_rtl_forward_simulation` creates a diamond in `behavior_improves` that cannot be resolved by transitivity when both C and RTL3 independently go wrong.
