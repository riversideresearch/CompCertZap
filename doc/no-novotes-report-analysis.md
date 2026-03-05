# Analysis of `no-novotes-report.md`

## 1. Executive summary

The report is a useful engineering record, but its main conclusion ("Novotes can be removed cleanly while preserving the proof story") is not established at theorem level.

The core issue is not compilation or `Admitted`; it is proof meaning:

1. The composition gap introduced by removing the `no_votes` bridge is real.
2. The replacement bridge relies on axioms, not proved lemmas.
3. The key informal claim ("well-colored implies vote-argument equality") is stronger than what the color judgment states.

So the current result should be treated as a conditional architecture experiment, not a completed proof refactor.

## 2. What the report gets right

1. It correctly identifies that `RTL3 -> RTL` is the natural strict-to-lenient direction.
2. It correctly identifies a composition "diamond" problem when trying to use only an `RTL3 -> RTL` improvement relation together with `C -> RTL` and `RTL3 -> faulty`.
3. It provides a concrete implementation/proof refactor record and identifies exactly where assumptions were introduced.

## 3. Critical issues

## 3.1 Axioms replace the missing bridge

The report's replacement for Novotes depends on:

- `wc_step_identity`
- `wc_nostep_identity`

These are stated as axioms in `RTLagreement.v` (quoted in the report).

This means the final theorem is conditional on these assumptions. Therefore, "proof architecture is complete without Novotes" is not justified.

## 3.2 "Zero Admitted" is not equivalent to "proved"

The report emphasizes compilation and no admitted proofs, but this does not imply theorem soundness when axioms are present. The correct status is:

- mechanized derivation under additional assumptions.

## 3.3 Separation vs agreement conflation

The report's informal justification relies on "well-colored implies vote arguments are equal at reachable states."
That is not what `wc_instruction` directly states. The color system enforces separation/flow discipline (lane typing + preservation constraints), not direct runtime value equality.

Any equality claim needs additional dynamic invariants (typically derived from TMR construction correctness and reachability arguments), not color typing alone.

## 3.4 Risk asymmetry between the two axioms

1. `wc_step_identity` (reachable RTL3 step implies RTL step) is directionally plausible.
2. `wc_nostep_identity` (reachable RTL3 stuck implies RTL stuck) is significantly stronger and more fragile.

The second axiom is where unsoundness is most likely to hide if agreement preconditions are missing.

## 4. Directional sanity check (why this matters)

CompCert's behavior theorems give:

1. `forward_simulation L1 L2` => from `beh1` produce `beh2` with `behavior_improves beh1 beh2`.
2. `backward_simulation L1 L2` => from `beh2` produce `beh1` with `behavior_improves beh1 beh2`.

In both cases, `L2` refines `L1`.

Therefore, if composition requires an intermediate link of the shape `behavior_improves beh2 beh3`, you cannot substitute only `behavior_improves beh3 beh2` and expect transitivity to close.

The report acknowledges this composition shape problem, but resolves it via axiomatized behavior identity rather than a proved bridge.

## 5. Assessment of current status

Recommended status label for the no-Novotes effort:

1. **Prototype architecture validated operationally** (builds, runs).
2. **Proof direction clarified** (strict-to-lenient bridge is sound direction).
3. **Formal soundness incomplete** due to reliance on unproved axioms for the crucial identity/stuckness transfer.

## 6. Recommended follow-up actions

1. Reclassify the report claims:
   - replace "eliminates need for no_votes entirely" with "eliminates explicit no_votes pass under additional axioms."
2. Decide one of two sound paths:
   - restore a proved restricted bridge (Novotes/agreement cutpoint), or
   - prove the axiomized reachable-state identity properties from stronger invariants.
3. Keep `doc/simulation-short.md` as mandatory context for any proof composition edits.
4. Require all future composition sections to be written in quantified behavior form (not arrow shorthand) before transitivity steps are accepted.

## 7. Bottom line

The report is technically valuable, but its main claim is currently overstated. The refactor removed an explicit pass, but not the logical need for an agreement bridge; that need was moved into axioms.

