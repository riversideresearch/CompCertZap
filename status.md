# AArch64 Fault-Model Port Status

## Current State

The operation-classification part of `backend/FaultPolicy.v` has been
split out into target-specific files:

- `aarch64/FaultPolicyOps.v`
- `arm/FaultPolicyOps.v`
- `powerpc/FaultPolicyOps.v`
- `riscV/FaultPolicyOps.v`
- `x86/FaultPolicyOps.v`

`backend/FaultPolicy.v` now re-exports `FaultPolicyOps` and keeps only the
shared builtin-policy logic.

## Changes Made

- Added `FaultPolicyOps.v` to the target-dependent backend file list in `Makefile`.
- Moved `is_protected`, `is_protectedb`, and `is_protectedb_spec` out of
  `backend/FaultPolicy.v` into per-architecture `FaultPolicyOps.v` files.
- Added a target-local `builtin_can_replicate_platform` helper in the same
  `FaultPolicyOps.v` files so that `backend/FaultPolicy.v` no longer mentions
  x86-only platform builtins in shared code.
- Left the shared builtin classifications in `backend/FaultPolicy.v`.

## Verification

- `make depend` succeeds.
- `make backend/FaultPolicy.vo` succeeds under the current `aarch64` configuration.

## Current Blocker

The next aarch64-specific failure is downstream in `backend/RTLfault.v`:

- `make backend/RTLfault.vo` fails at `backend/RTLfault.v:525`
- Error: `The reference Op.eval_addressing32 was not found in the current environment.`

This confirms that `RTLfault.v` still contains x86-shaped assumptions about
the active `Op` module.

## Next Steps

1. Do for `RTLfault.v` what was done for `FaultPolicy.v`: move the
   platform-specific pieces behind target-local modules.

2. In particular, extract or rework the parts of `RTLfault.v` that assume
   x86-specific `Op` structure:

- `Op.eval_addressing32` / `Op.eval_addressing64`
- x86-shaped `destruct op`
- x86-shaped `destruct cond`

3. Revisit the condition classifiers in `backend/CompCertZapUtils.v`
   (`is_compu` / `is_complu`), since aarch64 has extra condition forms such as
   shifted unsigned comparisons.

4. After `backend/RTLfault.vo` builds, continue with downstream files such as
   `backend/RTLtolerant.vo`.
