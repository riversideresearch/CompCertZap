# AArch64 Fault-Model Port Status

## Current State

The AArch64 fault-model port currently builds end-to-end in this tree:

- `make -j1` succeeds

The target-specific fault-policy and RTL-fault proof hooks are now
factored out of the shared backend files, and the AArch64 path no longer
depends on x86-shaped proof code in `backend/RTLfault.v`.

## Changes Made

- Split target-specific operation classification out of
  `backend/FaultPolicy.v` into per-architecture `FaultPolicyOps.v` files.
  `backend/FaultPolicy.v` now keeps the shared builtin-policy logic and
  re-exports the target hook.
- Moved the shared `val_compat` / `rs_compat` infrastructure and the pure
  compatibility lemmas from `backend/RTLfault.v` into
  `backend/CompCertZapUtils.v`.
- Moved the AArch64-specific condition and operation compatibility lemmas
  used by `backend/RTLfault.v` into `aarch64/FaultPolicyOps.v`.
- Added the missing vote-polymorphic wrappers
  (`Section VOTE` / `Context {VT} {vsem}`) to:
  - `aarch64/SelectOpproof.v`
  - `aarch64/SelectLongproof.v`
  - `aarch64/Asm.v`
  - `aarch64/Asmgenproof.v`
- Updated `aarch64/Asmexpand.ml` to accept the same TMR shadow-move
  builtin names as x86:
  - `__builtin_smove_*_green`
  - `__builtin_smove_*_blue`
  The older unsuffixed `__builtin_smove_*` names are still accepted as
  aliases.
- Updated `backend/RTLinfercolor.ml` to open `FaultPolicyOps`, matching
  the extracted OCaml side where `is_protectedb` now lives.
- Removed the `Asmagreement` import from `driver/Complements.v`. At the
  moment only `x86/Asmagreement.v` exists, so the old unqualified import
  blocked the AArch64 build.

## Verification

- `make -j1 backend/CompCertZapUtils.vo`
- `make -j1 aarch64/FaultPolicyOps.vo`
- `make -j1 backend/RTLfault.vo`
- `make -j1 backend/RTLtolerant.vo`
- `make -j1 backend/SplitLongproof.vo`
- `make -j1 backend/Selectionproof.vo`
- `make -j1 aarch64/Asm.vo`
- `make -j1 aarch64/Asmgenproof.vo`
- `make -f Makefile.extr -j1 ccomp`
- `make -j1`

## Remaining Follow-Up

1. Decide whether the unsuffixed AArch64 `__builtin_smove_*` aliases in
   `aarch64/Asmexpand.ml` should remain for compatibility or be removed
   once all callers use the canonical green/blue names.

2. If `driver/Complements.v` needs an Asm-side agreement result on
   AArch64, add an AArch64 analogue of `x86/Asmagreement.v` rather than
   restoring the old unqualified import.
