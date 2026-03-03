# Phase 2: Shared Module Introduction - Research

**Researched:** 2026-03-03
**Domain:** Coq module refactoring -- extracting duplicated Ltac tactics, type definitions, and boilerplate lemmas into shared modules
**Confidence:** HIGH

## Summary

Phase 2 creates two new Coq files (`RTLreplicateSpecCommon.v` and `RTLreplicateProofCommon.v`) by extracting content that is currently duplicated between the DMR and TMR spec/proof files. This is a move-only refactoring with zero semantic changes.

The DMR and TMR spec files (`RTLdmrspec.v`, `RTLtmrspec.v`) share 7 identical Ltac tactics, 2 identical type-level definitions (`comp_of_typ`, `is_actual_type`), and 2 identical utility definitions (`is_BR`, `is_BR_dec`). The DMR and TMR proof files (`RTLdmrproof.v`, `RTLtmrproof.v`) share at least 5 identical lemmas at the section/global scope: `genv_symb_add_globals`, `find_symbol_tge_ge`, `symbol_address_tge_ge`, `rs_map_ext`, and several register-utility lemmas. However, the proof file lemmas are inside `Section PRESERVATION` and depend on section variables (`prog`, `tprog`, `TRANSF`, `ge`, `tge`), which makes them non-trivially extractable -- they cannot simply be moved to a standalone file without either abstracting the section context or duplicating the section variables. Research recommends limiting `RTLreplicateProofCommon.v` to globally-scoped (outside any section) boilerplate lemmas only, keeping section-internal lemmas for Phase 4 de-duplication.

**Primary recommendation:** Extract 7 Ltac tactics + 4 type-level definitions into `RTLreplicateSpecCommon.v`, and globally-scoped boilerplate lemmas (those outside `Section VOTE`/`Section PRESERVATION`) into `RTLreplicateProofCommon.v`. Add both new files to `Makefile` `BACKEND` variable and run `make depend` before building.

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|-----------------|
| MOD-01 | `backend/RTLreplicateSpecCommon.v` created with shared spec tactics and definitions extracted from `RTLdmrspec.v` and `RTLtmrspec.v` | 7 Ltac tactics (lines 26-65 of both files) + `comp_of_typ`, `is_actual_type`, `is_BR`, `is_BR_dec` are byte-identical between both spec files |
| MOD-02 | `backend/RTLreplicateProofCommon.v` created with shared proof lemmas extracted from `RTLdmrproof.v` and `RTLtmrproof.v` | Globally-scoped boilerplate lemmas exist but most are inside `Section PRESERVATION`; only lemmas that do not depend on section variables can be extracted cleanly |
| MOD-03 | `RTLdmrspec.v` and `RTLtmrspec.v` import from `RTLreplicateSpecCommon.v` instead of duplicating | Replace duplicated lines with `Require Import RTLreplicateSpecCommon.` |
| MOD-04 | `RTLdmrproof.v` and `RTLtmrproof.v` import from `RTLreplicateProofCommon.v` instead of duplicating | Replace duplicated lemma bodies with `Require Import RTLreplicateProofCommon.` |
</phase_requirements>

## Architecture Patterns

### Coq Module Dependencies

The CompCert build uses `coqdep` to resolve transitive dependencies. New `.v` files must be:
1. Added to the `BACKEND` variable in `Makefile` (line ~166-167 area)
2. Registered via `make depend` which regenerates `.depend`
3. Placed in `backend/` to be resolved via the `-R backend compcert.backend` flag in `_CoqProject`

The dependency chain for the new files:

```
RTLreplicateSpecCommon.v
  imports: AST, Coqlib, Errors, Globalenvs, Integers, Linking, Maps,
           Memory, Op, Registers, RTLgen, RTLtyping, Smallstep, Values, RTL
  imported by: RTLdmrspec.v, RTLtmrspec.v

RTLreplicateProofCommon.v
  imports: (depends on what is extracted -- at minimum the same base as spec common)
  imported by: RTLdmrproof.v, RTLtmrproof.v
```

### Recommended File Structure

```
backend/
  RTLreplicateSpecCommon.v   # NEW: shared Ltac + type defs
  RTLreplicateProofCommon.v  # NEW: shared globally-scoped proof lemmas
  RTLdmrspec.v               # MODIFIED: imports SpecCommon, removes duplicates
  RTLtmrspec.v               # MODIFIED: imports SpecCommon, removes duplicates
  RTLdmrproof.v              # MODIFIED: imports ProofCommon, removes duplicates
  RTLtmrproof.v              # MODIFIED: imports ProofCommon, removes duplicates
```

### Pattern: Move-Only Refactoring in Coq

**What:** Extract identical definitions from two files into a shared module, then `Require Import` the shared module.

**When to use:** When two Coq files contain byte-identical definitions/tactics that should be maintained in one place.

**Critical rules:**
1. Extracted definitions MUST be byte-identical in both source files -- any difference, no matter how small, means the definition is not suitable for extraction in a move-only phase.
2. The `Require Import` must appear before any use of the extracted names.
3. Ltac tactics are NOT scoped -- they are globally visible once `Require Import`ed.
4. Coq `Definition`, `Inductive`, `Lemma` names are scoped by module -- `Require Import` brings them into scope unqualified.

### Anti-Patterns to Avoid

- **Extracting section-scoped definitions:** Lemmas inside `Section PRESERVATION` depend on `Variable prog`, `Variable tprog`, `Hypothesis TRANSF`, etc. Moving them to a standalone file requires either parametrizing them (changing their type signatures) or duplicating the section context in the new file. This changes proof obligations and violates Phase 2's "no proof obligations changed" constraint.
- **Forgetting to update the Makefile:** New `.v` files silently fail to compile if not in the `BACKEND` variable. The `make depend` step will not include them in `.depend`, so `make backend/RTLdmrspec.vo` would fail with "Cannot find a physical path bound to logical path RTLreplicateSpecCommon."
- **Extracting nearly-identical but not-quite-identical definitions:** DMR and TMR have many definitions that look similar but differ in arity (e.g., `rm_wf`, `rm_l`, `smoveR`, `match_instr`). These MUST NOT be extracted in this phase.

## Detailed Duplication Analysis

### Spec Files: Identical Content (RTLdmrspec.v vs RTLtmrspec.v)

**Byte-identical Ltac tactics (7 total, lines 26-65 in both files):**
1. `gen_contra` -- handles Error/OK contradiction
2. `gen_inv` -- inverts OK/OK equality
3. `gen_case H` -- destructs RTLgen match expressions
4. `egen_case` -- gen_case with fresh hypothesis
5. `lr_case` -- destructs left/right match expressions
6. `reserve_instr_inv` -- inverts reserve_instr results
7. `state_incr_inv` -- inverts state_incr hypothesis

**Byte-identical definitions (4 total):**
1. `comp_of_typ` (DMR lines 83-90, TMR lines 86-93) -- type-to-comparison mapping
2. `is_actual_type` (DMR lines 92-97, TMR lines 95-100) -- excludes Tany32/Tany64
3. `is_BR` (DMR lines 183-184, TMR lines 201-202) -- inductive for builtin_res
4. `is_BR_dec` (DMR lines 186-193, TMR lines 204-211) -- decidability for is_BR

**NOT extractable (differ by arity):**
- `rm_wf` -- DMR: `PMap.t reg`, TMR: `PMap.t (reg * reg)`
- `rm_l` -- DMR: 2-list, TMR: 3-list
- `smoveR` -- DMR: 4 args (src, dst), TMR: 5 args (src, dst1, dst2)
- `checkR`/`maj_voteR` -- DMR checks, TMR majority-votes
- `match_instr` -- structurally different per arity
- `reg_used_in_instr` -- byte-identical but deeply intertwined with non-extractable content

**Candidates for extraction but need verification:**

`reg_used_in_instr`, `reg_used_in_code`, `reg_used` (DMR lines 271-319, TMR lines 306-354) are byte-identical. However, they reference `instruction` from RTL.v (shared) and do not depend on DMR/TMR-specific definitions. They are good extraction candidates.

### Proof Files: Identical Content (RTLdmrproof.v vs RTLtmrproof.v)

**Section-internal identical lemmas (CANNOT extract in Phase 2):**
These lemmas are inside `Section PRESERVATION` and depend on section variables:
- `symbols_preserved` (DMR lines 119-121, TMR lines 120-122)
- `senv_preserved` (DMR lines 123-124, TMR lines 124-125)
- `functions_translated` (DMR lines 126-132, TMR lines 127-133)
- `function_ptr_translated` (DMR lines 134-140, TMR lines 135-141)
- `sig_function_translated` (DMR lines 142-150, TMR lines 143-151)
- `stacksize_translated` (DMR lines 152-158, TMR lines 153-159)
- `genv_symb_add_globals` (DMR lines 281-301, TMR lines 437-457) -- IDENTICAL
- `find_symbol_tge_ge` (DMR lines 303-315, TMR lines 459-471) -- IDENTICAL
- `symbol_address_tge_ge` (DMR lines 317-322, TMR lines 473-478) -- IDENTICAL
- `rs_map_ext` (DMR lines 324-331, TMR lines 480-487) -- IDENTICAL
- `match_regsets_eval_addressing` (DMR lines 333-343, TMR lines 489-499) -- IDENTICAL
- `not_in_regs_set` (DMR lines 380-386, TMR lines 576-?) -- needs arity check
- `pset_in_res_fold_right` (identical in both)
- `reg_used_in_code_in_elements_code_regs` (identical in both)
- `reg_used_in_code_in_all_regs_list` (identical in both)
- `in_code_regs_in_all_regs_list` (identical in both)
- `param_in_all_regs_list` (identical in both)

All of these are inside `Section PRESERVATION`, so extracting them would require abstracting `prog`, `tprog`, `TRANSF`, `ge`, `tge` as explicit parameters. This changes their type signatures and all call sites -- violating the "no proof obligations changed" constraint.

**Globally-scoped candidates (outside sections, CAN extract):**

Looking at the proof files, very little content exists outside the `Section VOTE` and `Section PRESERVATION` wrappers. The `match_regsets`, `match_stackframes`, `match_states` definitions are inside `Section VOTE` and differ by arity.

The only globally-scoped duplicate content between proof files is the `match_prog` definition and `transf_program_match` lemma, which are inside `Section VOTE` but outside `Section PRESERVATION`. However, these reference `transf_fundef` from the specific DMR/TMR pass and thus differ.

**Practical recommendation for MOD-02:** Since nearly all the identical proof lemmas are section-internal, `RTLreplicateProofCommon.v` should contain:
1. Re-exports or shared imports (the common `Require Import` header)
2. Any globally-scoped utility lemmas that are byte-identical
3. Possibly `in_list`, `not_in_list`, `nodup_false`, `not_nodup` Ltac tactics (DMR lines 160-179) -- but these only appear in the DMR file, not TMR. TMR uses different `rm_wf_*` lemma patterns instead.

After careful analysis, the DMR proof file has 4 NoDup-related Ltac tactics (`in_list`, `not_in_list`, `nodup_false`, `not_nodup`) at lines 160-179 inside `Section PRESERVATION`. The TMR proof file does NOT have these -- it uses direct lemmas instead. These are therefore NOT shared.

**Revised assessment:** The proof files have very few truly extractable shared items at the global scope. The shared content is almost entirely section-internal. For `RTLreplicateProofCommon.v`, reasonable candidates are:
- Shared `Require Import` preamble (reduces import duplication)
- If any standalone utility lemmas exist outside sections (to be identified during implementation)

The planner should set expectations that `RTLreplicateProofCommon.v` may be smaller than `RTLreplicateSpecCommon.v`.

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Coq dependency tracking | Manual `.depend` editing | `make depend` after adding files to `BACKEND` | `coqdep` handles transitive dependency resolution correctly |
| Finding identical lines | Manual line-by-line comparison | `diff --unified=0 file1 file2` | Mechanical diff is authoritative for byte-identity |
| Testing individual file compilation | Full `make proof` | `make backend/RTLreplicateSpecCommon.vo` | Targeted builds are 100x faster than full proof |

## Common Pitfalls

### Pitfall 1: Forgetting Makefile Registration
**What goes wrong:** New `.v` file compiles when invoked directly (`coqc -R ...`) but fails when built via `make backend/RTLdmrspec.vo` because the dependent module is not in `.depend`.
**Why it happens:** `make depend` runs `coqdep` only on files listed in `$(FILES)`, which is constructed from `$(BACKEND)` and other variables.
**How to avoid:** Add BOTH new files to the `BACKEND` variable in the Makefile, then run `make depend` before any `.vo` build.
**Warning signs:** "Cannot find a physical path bound to logical path compcert.backend.RTLreplicateSpecCommon" error.

### Pitfall 2: Extracting Section-Scoped Lemmas
**What goes wrong:** A lemma that worked inside `Section PRESERVATION` now requires explicit `prog tprog TRANSF ge tge` arguments. All call sites break.
**Why it happens:** Coq sections auto-generalize over section variables. Moving a lemma outside the section changes its type.
**How to avoid:** ONLY extract content that is at global scope (outside any Section/End pair). For Phase 2, this means primarily Ltac tactics and standalone definitions from the spec files.
**Warning signs:** Type mismatch errors at call sites after extraction.

### Pitfall 3: Import Order Sensitivity
**What goes wrong:** `Require Import RTLreplicateSpecCommon` must come before any use of the extracted names. If it appears after `Require Import RTLdmr`, and `RTLdmr.v` does not depend on `RTLreplicateSpecCommon.v`, things compile. But if a name from the common file shadows something in RTLdmr, behavior changes.
**How to avoid:** Place `Require Import RTLreplicateSpecCommon` early in the import block, after the standard CompCert imports but before the pass-specific `RTLdmr`/`RTLtmr` imports.
**Warning signs:** Name resolution errors or unexpected behavior.

### Pitfall 4: Ltac Scoping
**What goes wrong:** Ltac tactics are globally visible after `Require Import`. If `RTLreplicateSpecCommon.v` defines `gen_contra` and someone also defines `gen_contra` locally, the local definition wins.
**Why it happens:** Coq's Ltac namespace is last-definition-wins within a file.
**How to avoid:** After extraction, ensure the source files do NOT still have local definitions of the same tactics. The whole point is to remove the local copies.
**Warning signs:** Tactics silently using stale local versions.

### Pitfall 5: `check-admitted` False Positive from New Files
**What goes wrong:** If the new `.v` file accidentally contains the word "Admitted" in a comment, `make check-admitted` will flag it.
**Why it happens:** The check greps for `admit|Admitted|ADMITTED` across all `$(FILES)`.
**How to avoid:** Ensure new files do not contain "Admitted" in comments. This is not an issue for move-only extraction of existing clean content.
**Warning signs:** `make check-admitted` fails after adding new files.

## Code Examples

### Adding a New File to the Makefile

In `Makefile`, the `BACKEND` variable (line ~166-167):

```makefile
# Current:
  RTLdmr.v RTLdmrspec.v RTLdmrproof.v \
  RTLtmr.v RTLtmrspec.v RTLtmrproof.v Builtins2.v \

# After:
  RTLreplicateSpecCommon.v RTLreplicateProofCommon.v \
  RTLdmr.v RTLdmrspec.v RTLdmrproof.v \
  RTLtmr.v RTLtmrspec.v RTLtmrproof.v Builtins2.v \
```

Place the new common files BEFORE the files that import them, since `coqdep` handles ordering, but keeping them adjacent aids readability.

### RTLreplicateSpecCommon.v Structure

```coq
(** * Shared tactics and definitions for DMR/TMR replication specs. *)

Require Import
  AST
  Coqlib
  Errors
  Globalenvs
  Integers
  Linking
  Maps
  Memory
  Op
  Registers
  RTLgen
  RTLtyping
  Smallstep
  Values
.
Require Import RTL.
Require Import Errors.
Import ListNotations.

Local Open Scope positive_scope.

(** ** Shared Ltac tactics for RTLgen state monad reasoning. *)

Ltac gen_contra :=
  try match goal with
  | [H: RTLgen.Error _ = RTLgen.OK _ _ _ |- _ ] => inv H
  | [H: RTLgen.OK _ _ _ = RTLgen.Error _ |- _ ] => inv H
  end.

Ltac gen_inv :=
  match goal with
  | [H: RTLgen.OK _ _ _ = RTLgen.OK _ _ _ |- _ ] => inv H
  end.

Ltac gen_case H :=
  match goal with
  | [ _: match ?X with
         | RTLgen.Error _ => _
         | RTLgen.OK _ _ _ => _ end = _ |- _ ] =>
      destruct X eqn:H
  end; gen_contra; try gen_inv.

Ltac egen_case :=
  let H := fresh "H" in
  gen_case H.

Ltac lr_case :=
  match goal with
  | [ _: match ?X with
         | left _ => _
         | right _ => _ end = _ |- _ ] =>
      destruct X
  end; gen_contra; try gen_inv.

Ltac reserve_instr_inv :=
  match goal with
  | [ H: reserve_instr ?s = RTLgen.OK ?n ?s' ?pf |- _ ] => inv H
  end.

Ltac state_incr_inv :=
  match goal with
  | [ H: state_incr ?s1 ?s2 |- _ ] => inv H
  end.

(** ** Shared type definitions. *)

Definition comp_of_typ (ty : typ) : comparison -> condition :=
  match ty with
  | Tint => Ccompu
  | Tlong => Ccomplu
  | Tsingle => Ccompfs
  | Tfloat => Ccompf
  | _ => Ccomp
  end.

Definition is_actual_type (ty : typ) : Prop :=
  match ty with
  | Tany32 => False
  | Tany64 => False
  | _ => True
  end.

(** ** Shared builtin_res utilities. *)

Inductive is_BR {A: Type} : builtin_res A -> Prop :=
| is_br_BR : forall x, is_BR (BR x).

Definition is_BR_dec {A : Type} (br : builtin_res A)
  : { is_BR br } + { ~ is_BR br }.
Proof.
  destruct br.
  - left; constructor.
  - right; intro H; inv H.
  - right; intro H; inv H.
Qed.
```

### Importing the Shared Module in RTLdmrspec.v

```coq
(** * Relational specification of the DMR transformation. *)

Require Import
  AST Coqlib Errors Globalenvs Integers Linking Maps
  Memory Op Registers RTLgen RTLtyping Smallstep Values.
Require Import RTL.
Require Import RTLdmr.
Require Import RTLreplicateSpecCommon.  (* NEW: shared tactics + defs *)
Require Import Errors.
Import ListNotations.

Local Open Scope positive_scope.

(* gen_contra, gen_inv, gen_case, etc. now come from RTLreplicateSpecCommon *)
(* comp_of_typ, is_actual_type, is_BR, is_BR_dec likewise *)

Definition rm_wf (rm : PMap.t reg) ... (* DMR-specific, stays here *)
```

### Build Verification Sequence

```bash
# Step 1: Add files to Makefile BACKEND variable
# Step 2: Regenerate dependencies
make depend

# Step 3: Build new common files independently
make backend/RTLreplicateSpecCommon.vo
make backend/RTLreplicateProofCommon.vo

# Step 4: Build dependent files
make backend/RTLdmrspec.vo backend/RTLtmrspec.vo
make backend/RTLdmrproof.vo backend/RTLtmrproof.vo

# Step 5: Verify no admitted proofs
make check-admitted
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| Copy-paste between DMR/TMR spec files | Extract shared content to common module | Phase 2 (now) | Single maintenance point for 7 tactics + 4 definitions |
| No common proof module | Shared proof boilerplate module | Phase 2 (now) | Prepares for Phase 4 de-duplication |

## Open Questions

1. **Exact contents of RTLreplicateProofCommon.v**
   - What we know: Most identical proof lemmas are section-internal and cannot be extracted without changing signatures.
   - What's unclear: Whether there are any globally-scoped utility lemmas worth extracting. The `reg_used_in_instr`, `reg_used_in_code`, `reg_used` definitions in the spec files are byte-identical and could be candidates, but they are currently in the spec files not the proof files.
   - Recommendation: During implementation, examine whether `reg_used_in_instr`/`reg_used_in_code`/`reg_used` should go in SpecCommon (they are spec-level definitions used by both spec and proof files). For ProofCommon, it may end up being just a shared import header or a small set of utilities. The planner should allow for ProofCommon to be minimal and still satisfy MOD-02 ("shared proof lemmas" can be a small set).

2. **Whether `reg_used_in_instr` and friends belong in SpecCommon**
   - What we know: `reg_used_in_instr` (inductive, ~40 lines), `reg_used_in_code`, and `reg_used` are byte-identical between both spec files.
   - What's unclear: These are semantically "spec" definitions, but they are used extensively in the proof files too. Moving them to SpecCommon means proof files gain them transitively through their spec file imports.
   - Recommendation: Include them in `RTLreplicateSpecCommon.v`. They are standalone (no DMR/TMR-specific dependencies) and removing their duplication is directly within MOD-01's scope.

## Validation Architecture

### Test Framework
| Property | Value |
|----------|-------|
| Framework | Coq proof checker (coqc) + grep-based check-admitted |
| Config file | Makefile (coqdep-based dependency resolution) |
| Quick run command | `make backend/RTLreplicateSpecCommon.vo` |
| Full suite command | `make check-admitted && make backend/RTLdmrspec.vo backend/RTLtmrspec.vo backend/RTLdmrproof.vo backend/RTLtmrproof.vo` |

### Phase Requirements to Test Map
| Req ID | Behavior | Test Type | Automated Command | File Exists? |
|--------|----------|-----------|-------------------|-------------|
| MOD-01 | SpecCommon compiles with shared tactics/defs | build | `make backend/RTLreplicateSpecCommon.vo` | Wave 0 |
| MOD-02 | ProofCommon compiles with shared proof lemmas | build | `make backend/RTLreplicateProofCommon.vo` | Wave 0 |
| MOD-03 | DMR/TMR spec files compile with import | build | `make backend/RTLdmrspec.vo backend/RTLtmrspec.vo` | Existing |
| MOD-04 | DMR/TMR proof files compile with import | build | `make backend/RTLdmrproof.vo backend/RTLtmrproof.vo` | Existing |
| ALL | No admitted proofs | grep | `make check-admitted` | Existing |

### Sampling Rate
- **Per task commit:** `make backend/RTLreplicateSpecCommon.vo && make backend/RTLdmrspec.vo backend/RTLtmrspec.vo`
- **Per wave merge:** Full suite command above
- **Phase gate:** `make check-admitted` green before verify

### Wave 0 Gaps
- [ ] `backend/RTLreplicateSpecCommon.v` -- new file, does not exist yet
- [ ] `backend/RTLreplicateProofCommon.v` -- new file, does not exist yet
- [ ] Makefile `BACKEND` variable update -- `RTLreplicateSpecCommon.v RTLreplicateProofCommon.v` added
- [ ] `make depend` -- regenerate `.depend` with new files

## Sources

### Primary (HIGH confidence)
- Direct `diff` analysis of `backend/RTLdmrspec.v` vs `backend/RTLtmrspec.v` (byte-level comparison)
- Direct `diff` analysis of `backend/RTLdmrproof.v` vs `backend/RTLtmrproof.v`
- `Makefile` lines 159-192 (BACKEND variable), lines 380-384 (depend target)
- `_CoqProject` (module path flags)
- `CLAUDE.md` (build commands and architecture)

### Secondary (MEDIUM confidence)
- STATE.md pitfall note about Makefile registration (Phase 2 pitfall already identified by prior research)

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH - this is pure Coq module refactoring, well-understood mechanics
- Architecture: HIGH - direct file analysis confirms exactly what is duplicated and extractable
- Pitfalls: HIGH - Makefile registration pitfall already documented in STATE.md; section-scoping pitfall verified by examining actual file structure

**Research date:** 2026-03-03
**Valid until:** indefinite (this is project-specific structural analysis, not library-version-dependent)
