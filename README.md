# CompCertZap

This branch was ported onto upstream CompCert `v3.17`.
The pre-port `master` tip was preserved as tag `pre-port-3.17-master`.
The old branch `rtl-liveness` also preserves the pre-port tree content
(without the final merge-wrapper commit that old `master` had).

## Overview

CompCertZap is a fork of CompCert that extends the compiler with
**formally verified software-based radiation hardening**. It implements
Triple Modular Redundancy (TMR) to protect programs against
single-event effects (SEEs) — upsets to registers caused by charged
particles — and includes a machine-checked proof that the protection
is correct.

The compiler inserts a TMR pass after RTL optimizations that
triplicates computations into independent "shadow" copies and adds
majority vote instructions to detect and remediate faults. The key
property we prove is *fault tolerance*: compiled programs behave
correctly even when run under a faulty semantics that can
nondeterministically corrupt the destination register of an
instruction (the single-fault model).

## Proof Architecture

The fault tolerance proof decomposes into two properties:

- **Agreement**: the arguments to every majority vote are equal (in
  fault-free execution). This is guaranteed by construction via the
  soundness proof of the TMR replication pass.
- **Separation**: redundant computations do not depend on one another,
  so a single fault can corrupt at most one of the three copies.
  Separation is not guaranteed to be preserved by later compiler
  passes (e.g., register allocation may coalesce shadow registers), so
  it is established *a posteriori* by a verified color-based type
  checker that assigns colors (Red, Green, Blue, White, Pink) to
  registers at each program point and checks that colors do not mix
  across computations or votes.

The main theorem (`transf_c_program_to_rtl_preservation_faulty` in
`driver/Complements.v`) is proved by composing four refinements:

1. **Standard compilation**: C refines to 2-voting RTL with no votes
   (standard CompCert backward simulation).
2. **Weak agreement**: 2-voting RTL refines to 3-voting RTL (trivial
   from the absence of votes).
3. **TMR soundness**: 3-voting RTL refines to 3-voting RTL+TMR
   (backward simulation for the replication pass).
4. **Faulty simulation**: 3-voting RTL+TMR refines to 2-voting faulty
   RTL+TMR (backward simulation, assuming well-coloredness).

## Current Status and Future Work

The current prototype proves fault tolerance at the RTL level using a
truncated compiler pipeline that stops before register allocation. The
color checker runs as a translation validator on the intermediate RTL
in the OCaml driver (`driver/Driver.ml`), using an unverified
union-find-based color inference oracle (`backend/RTLinfercolor.ml`)
whose output is validated by a verified Boolean checker
(`backend/RTLcolorcheck.v`).

Our goal is to extend fault tolerance to the RISC-V assembly level.
Agreement extends to assembly for free because weak agreement is
preserved by CompCert's existing behavioral refinement proofs.
Separation requires reimplementing the color system, color
inference/checker, fault semantics, and faulty simulation proof for
the RISC-V backend.

## Usage

```bash
# Compile with TMR fault tolerance
./ccomp -tmr -o output input.c

# Compile with DMR (dual modular redundancy)
./ccomp -dmr -o output input.c
```

## Key Files

| File | Description |
|------|-------------|
| `backend/RTLtmr.v` / `RTLtmrproof.v` | TMR replication pass and soundness proof |
| `backend/RTLdmr.v` / `RTLdmrproof.v` | DMR replication pass and soundness proof |
| `backend/RTLfault.v` | Faulty RTL semantics (single-fault model) |
| `backend/RTLtolerant.v` | Faulty backward simulation proof |
| `backend/RTLcolor.v` | Declarative color system specification |
| `backend/RTLcolorcheck.v` | Verified Boolean color checker |
| `backend/RTLinfercolor.ml` | Unverified color inference oracle |
| `backend/RTLagreement.v` | Weak agreement definition |
| `backend/Novotes.v` / `Novotesproof.v` | Pre-TMR vote absence checker |
| `backend/Builtins2.v` | Vote builtin definitions and `VoteSemantics` typeclass |
| `driver/Complements.v` | Main fault tolerance theorem |
| `driver/Compiler.v` | Compiler pipeline (includes `transf_c_program_to_rtl`) |

# CompCert
The formally-verified C compiler.

## Overview
The CompCert C verified compiler is a compiler for a large subset of the
C programming language that generates code for the PowerPC, ARM, x86 and
RISC-V processors.

The distinguishing feature of CompCert is that it has been formally
verified using the Coq proof assistant: the generated assembly code is
formally guaranteed to behave as prescribed by the semantics of the
source C code.

For more information on CompCert (supported platforms, supported C
features, installation instructions, using the compiler, etc), please
refer to the [Web site](https://compcert.org/) and especially
the [user's manual](https://compcert.org/man/).

## License
CompCert is not free software.  This non-commercial release can only
be used for evaluation, research, educational and personal purposes.
A commercial version of CompCert, without this restriction and with
professional support and extra features, can be purchased from
[AbsInt](https://www.absint.com).  See the file `LICENSE` for more
information.

## Copyright
The CompCert verified compiler is Copyright Institut National de
Recherche en Informatique et en Automatique (INRIA) and 
AbsInt Angewandte Informatik GmbH.


## Contact
General discussions on CompCert take place on the
[compcert-users@inria.fr](https://sympa.inria.fr/sympa/info/compcert-users)
mailing list.

For inquiries on the commercial version of CompCert, please contact
info@absint.com
