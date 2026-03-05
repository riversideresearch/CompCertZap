# CompCert Simulation Direction Cheat Sheet

Use this as a strict reference for proof direction.

## `behavior_improves`

`behavior_improves a b` means: `b` is at least as good as `a`.
- Either `a = b`
- Or `a = Goes_wrong t` and `t` is a prefix of `b`

So do **not** read it as "a improves b".

## Forward simulation

From `forward_simulation L1 L2`:

`program_behaves L1 beh1 -> exists beh2, program_behaves L2 beh2 /\ behavior_improves beh1 beh2`.

Interpretation: `L2` refines `L1`.

## Backward simulation

From `backward_simulation L1 L2`:

`program_behaves L2 beh2 -> exists beh1, program_behaves L1 beh1 /\ behavior_improves beh1 beh2`.

Interpretation: `L2` refines `L1`.

Mnemonic: `backward_simulation source target` implies **target refines source**.

## Composition rule

To compose via transitivity, directions must line up as:

`behavior_improves b1 b2` and `behavior_improves b2 b3`  
=> `behavior_improves b1 b3`.

Always write composition steps in quantified behavior form before using arrow shorthand.

