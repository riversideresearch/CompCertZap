# Simulation and Behavioral Refinement in CompCert

This note fixes terminology/direction for the notions used in CompCert proofs.

## 1. Behaviors and `behavior_improves`

`program_behavior` is one of:
- `Terminates t r`
- `Diverges t`
- `Reacts T`
- `Goes_wrong t`

(`common/Behaviors.v`:41-45)

`behavior_improves beh1 beh2` means:

```coq
beh1 = beh2 \/
exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2
```

(`common/Behaviors.v`:81-82)

Interpretation:
- `beh2` is at least as good as `beh1`.
- `beh1` may go wrong earlier; `beh2` may continue.

`behavior_improves` is transitive (`common/Behaviors.v`:90-100).

## 2. Forward simulation: direction

`forward_simulation L1 L2` has step matching from `L1` to `L2`
(`common/Smallstep.v`:593-619).

Behavior theorem:

```coq
forward_simulation L1 L2 ->
forall beh1, program_behaves L1 beh1 ->
exists beh2, program_behaves L2 beh2 /\ behavior_improves beh1 beh2.
```

(`common/Behaviors.v`:316-319)

So forward simulation gives:
- source behavior `beh1`
- target behavior `beh2`
- with `behavior_improves beh1 beh2`

In short: `L2` refines `L1`.

## 3. Backward simulation: direction

`backward_simulation L1 L2` is defined with simulation obligations stepping on `L2` and matching in `L1`
(`common/Smallstep.v`:1316-1350).

Behavior theorem:

```coq
backward_simulation L1 L2 ->
forall beh2, program_behaves L2 beh2 ->
exists beh1, program_behaves L1 beh1 /\ behavior_improves beh1 beh2.
```

(`common/Behaviors.v`:493-496)

So backward simulation also gives:
- target behavior `beh2`
- source witness `beh1`
- with `behavior_improves beh1 beh2`

Again: `L2` refines `L1`.

Key mnemonic:
- `backward_simulation source target` implies **target refines source**.

## 4. Converting forward to backward

CompCert provides:

```coq
forward_simulation L1 L2 -> receptive L1 -> determinate L2 ->
backward_simulation L1 L2
```

(`common/Smallstep.v`:1890-1893)

This does not change semantic direction; it only changes proof form.

## 5. Composition pattern used in proofs

If you have:

1. `program_behaves L3 beh3 -> exists beh2, program_behaves L2 beh2 /\ behavior_improves beh2 beh3`
2. `program_behaves L2 beh2 -> exists beh1, program_behaves L1 beh1 /\ behavior_improves beh1 beh2`

then by transitivity you get:

- `program_behaves L3 beh3 -> exists beh1, program_behaves L1 beh1 /\ behavior_improves beh1 beh3`.

This is the pattern used in `driver/Complements.v` with `behavior_improves_trans`.

## 6. Frequent pitfall

Do not read `behavior_improves a b` as “`a` is better than `b`”.
It is the opposite: `b` is at least as defined/safe as `a`.

That single inversion is the usual source of arrow-direction mistakes in plan documents.

