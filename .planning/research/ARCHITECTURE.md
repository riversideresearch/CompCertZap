# Architecture Patterns: Coq Proof Cleanup and Reorganization

**Domain:** Large Coq proof base reorganization — compiler verification (CompCert fork)
**Researched:** 2026-03-03
**Focus:** Module dependency structure, safe file splitting, DMR/TMR unification

---

## Current Module Dependency Graph

The fault-tolerance extension consists of the following layers, from most foundational
to most derived. All build dependencies are strict (Coq requires a `.vo` before any
file that `Require Import`s it can compile).

```
Layer 0: Foundations (unchanged CompCert core)
  RTL.v, RTLgen.v, RTLtyping.v, Globalenvs, Maps, Memory, Smallstep, Values

Layer 1: Domain definitions
  Builtins2.v        -- vote_type typeclass, replicate_builtin table
  RTLcolor.v         -- color type (Red/Green/Blue/White/Pink), is_basic
  RTLfault.v         -- fstate, maybe_zap, faulty RTL semantics
  Novotes.v          -- no_votes_code / no_votes (proposition)

Layer 2: Transformation passes (implementations)
  RTLdmr.v           -- DMR transformation (add one shadow register per reg)
  RTLtmr.v           -- TMR transformation (add two shadow registers per reg)

Layer 3: Relational specifications for transformations
  RTLdmrspec.v       -- match_code, rm_wf (DMR), copy_allR, checkR, smoveR
  RTLtmrspec.v       -- match_code, rm_wf (TMR), copy_allR, maj_voteR, smoveR

Layer 4: Color verification
  RTLcolorcheck.v    -- check_col_instr, check_program (verified Boolean checker)

Layer 5: Match relation helpers / weak agreement
  RTLagreement.v     -- rtl_weak_agreement (Two vs Three vote semantics)

Layer 6: Simulation proofs
  RTLdmrproof.v      -- Forward sim: RTL >= RTL+DMR  [imports RTLdmrspec]
  RTLtmrproof.v      -- Forward sim: RTL >= RTL+TMR  [imports RTLtmrspec]
  RTLtolerant.v      -- Backward sim: TMR+faulty <= TMR+non-faulty
                        [imports RTLtmrspec, RTLcolor, RTLfault]
  Novotesproof.v     -- Soundness: no_votes => weak_agreement
                        [imports Novotes, RTLagreement]
  CSEproof.v         -- Standard CSE preservation proof (imports Novotesproof)

Layer 7: Pipeline integration
  driver/Compiler.v  -- References RTLdmrproof.match_prog, RTLtmrproof.match_prog
  driver/Complements.v -- Composes all four backward simulation refinements
```

**Key observation:** The proof files (Layer 6) are the heaviest and most duplicated.
The spec files (Layer 3) are the second-largest source of duplication.
The proposed `RTLreplicateSpecCommon.v` and `RTLreplicateProofCommon.v` sit between
Layers 2-3 and 3-6 respectively.

---

## Component Boundaries

| Component | Responsibility | Communicates With (imports) |
|-----------|---------------|----------------------------|
| `Builtins2.v` | Vote type definition, builtin name table | (Layer 0 only) |
| `RTLcolor.v` | Color algebra, `is_basic`, color scope notation | (Layer 0 only) |
| `RTLfault.v` | Faulty step relation, `maybe_zap`, `fstate` | RTL.v |
| `Novotes.v` | `no_votes` proposition definition only | RTL.v |
| `RTLdmr.v` / `RTLtmr.v` | Transformation pass implementations | RTLgen.v, RTLtyping.v |
| `RTLdmrspec.v` / `RTLtmrspec.v` | Relational specs, `rm_wf` definitions | RTLdmr/RTLtmr.v |
| `RTLcolorcheck.v` | Boolean color checker + soundness | RTLcolor.v, RTL.v |
| `RTLagreement.v` | `rtl_weak_agreement` (currently mostly commented) | RTL.v, Builtins2.v |
| `RTLdmrproof.v` / `RTLtmrproof.v` | Forward simulation proofs | RTLdmrspec/RTLtmrspec.v |
| `RTLtolerant.v` | Backward sim: faulty <= non-faulty | RTLtmrspec.v, RTLcolor.v, RTLfault.v |
| `Novotesproof.v` | Proves `no_votes` => `external_call` Three-compatible | Novotes.v, RTLagreement.v |
| `driver/Complements.v` | Top-level fault tolerance theorem | All of Layer 6 |

---

## Duplicated Machinery: What Needs a Common Home

### In RTLdmrspec.v and RTLtmrspec.v (identical code)

Both files begin with an exact copy of the same six Ltac tactics:
- `gen_contra`, `gen_inv`, `gen_case`, `egen_case`, `lr_case`, `reserve_instr_inv`

Both define:
- `comp_of_typ : typ -> comparison -> condition` (identical definition)
- `is_actual_type : typ -> Prop` (identical definition)
- `copy_allR` inductive (same constructor structure, different arities)
- `copy_to_shadows_smoveR` (same shape, different extra args)
- `copy_all_to_shadows_copy_allR` (same proof strategy)
- `replication_map_wf_aux` lemma (both have TODO noting it is a mess)
- `copy_allR_monotone` (same statement shape, same proof)
- `transf_function_code_matches` (same statement shape, same proof)

The critical difference between DMR and TMR in specs:
- DMR: `rm : PMap.t reg` (one shadow register per register)
- TMR: `rm : PMap.t (reg * reg)` (two shadow registers per register)

This means the shared tactics/definitions are candidates for `RTLreplicateSpecCommon.v`,
but the `rm_wf` definition and anything indexed by `rm` type CANNOT be shared directly
without a typeclass or functor.

### In RTLdmrproof.v and RTLtmrproof.v (parallel structure)

Both files have nearly identical structure:
1. `match_prog` definition (identical form)
2. `match_regsets` definition (differs by rm arity: 1 vs 2 shadows)
3. `match_stackframes` inductive (same structure, extra `res2`/`res3` in TMR)
4. `match_states` inductive (identical structure)
5. Section PRESERVATION with identical boilerplate:
   - `symbols_preserved`, `senv_preserved`, `functions_translated`,
     `function_ptr_translated`, `sig_function_translated`, `stacksize_translated`
6. `rm_wf_neq_*` lemma family:
   - DMR has 4 lemmas (2 registers per entry)
   - TMR has 12 lemmas (6 cross-product pairs for 3 registers per entry)
7. `match_regsets_get*` family (DMR: 2 lemmas; TMR: 4 lemmas)
8. `match_regsets_eval_addressing`, `match_regsets_storev` (identical in both)
9. `genv_symb_add_globals`, `find_symbol_tge_ge`, `symbol_address_tge_ge` (identical)
10. `rs_map_ext` (identical)
11. `pset_in_res_fold_right` (identical)
12. `reg_used_in_code_in_elements_code_regs`, `reg_used_in_code_in_all_regs_list`,
    `param_in_all_regs_list` (identical)

**Genuinely different (cannot be unified):**
- Vote step lemmas: `checkR_step` (DMR) vs `maj_voteR_step` (TMR)
- Argument lookup: DMR has 1-register args, TMR has 3-register args
- `match_regsets_update` has different register-set update semantics
- `copy_allR_star_step` differs in internal proof structure

---

## Proposed Target Architecture

### New File: backend/RTLreplicateSpecCommon.v

**Purpose:** Shared tactics and type-agnostic definitions that are literally identical
in both spec files.

**Contents:**
```
(* Shared Ltac tactics *)
Ltac gen_contra := ...
Ltac gen_inv := ...
Ltac gen_case H := ...
Ltac egen_case := ...
Ltac lr_case := ...
Ltac reserve_instr_inv := ...
Ltac state_incr_inv := ...

(* Shared type definitions *)
Definition comp_of_typ (ty : typ) : comparison -> condition := ...
Definition is_actual_type (ty : typ) : Prop := ...
```

**Does NOT contain:** `rm_wf`, `rm_l`, `smoveR`, `copy_allR` — these differ between
DMR and TMR because they are indexed by the replication map type.

**Import chain:** RTLreplicateSpecCommon has no dependency on RTLdmr or RTLtmr.
Both RTLdmrspec.v and RTLtmrspec.v import it.

### New File: backend/RTLreplicateProofCommon.v

**Purpose:** Globally-quantified lemmas about RTL infrastructure that appear verbatim
in both proof files, and are not parameterized by the replication map type.

**Contents:**
```
(* Global env lemmas — proof-by-apply (Genv.find_symbol_match etc.) *)
Lemma genv_symb_add_globals ...
Lemma find_symbol_tge_ge ...
Lemma symbol_address_tge_ge ...
Lemma rs_map_ext ...

(* Code register tracking lemmas *)
Lemma pset_in_res_fold_right ...
Lemma reg_used_in_code_in_elements_code_regs ...
Lemma reg_used_in_code_in_all_regs_list ...
Lemma param_in_all_regs_list ...

(* Utility *)
Lemma list_norepet_nodup ...
Lemma has_type_list_length ...
Lemma lessdef_list_refl ...
Lemma rs_in_singleton ...
Lemma rs_in_l_2 ...
```

**Does NOT contain:** Anything inside `Section PRESERVATION` that references `match_prog`,
`transf_fundef`, `match_function`, or `match_regsets` — those vary between DMR and TMR.

**Constraint:** These lemmas must be stated globally (not in a `Section`) to be reusable
without re-opening a section. This matches how CompCert's existing shared lemmas work
(e.g., in `Smallstep.v`, `Globalenvs.v`).

**Import chain:** RTLreplicateProofCommon imports RTL.v and standard CompCert libraries,
but NOT RTLdmr, RTLtmr, RTLdmrspec, or RTLtmrspec. Both proof files import it.

### Revised File Dependency Graph After Reorganization

```
Layer 0: RTL.v, RTLgen.v, RTLtyping.v, Maps, Memory, Smallstep, etc.

Layer 1: Builtins2.v, RTLcolor.v, RTLfault.v, Novotes.v

Layer 2: RTLdmr.v, RTLtmr.v

Layer 2.5 (NEW): RTLreplicateSpecCommon.v  [depends on Layer 0 only]

Layer 3:
  RTLdmrspec.v  [imports RTLreplicateSpecCommon, RTLdmr]
  RTLtmrspec.v  [imports RTLreplicateSpecCommon, RTLtmr]

Layer 3.5 (NEW): RTLreplicateProofCommon.v  [depends on Layer 0+1]

Layer 4: RTLcolorcheck.v

Layer 5: RTLagreement.v

Layer 6:
  RTLdmrproof.v   [imports RTLreplicateProofCommon, RTLdmrspec]
  RTLtmrproof.v   [imports RTLreplicateProofCommon, RTLtmrspec]
  RTLtolerant.v   [imports RTLtmrspec, RTLcolor, RTLfault]
  Novotesproof.v  [imports Novotes, RTLagreement]

Layer 7: driver/Compiler.v, driver/Complements.v
```

---

## Patterns to Follow

### Pattern 1: Global-scope lemmas in shared files

**What:** Lemmas that are exported from a common module must live at the top level
(not inside a `Section`), because section-local variables become universally quantified
on section close — making the signature correct but requiring the importer to provide
all arguments explicitly at each call site.

**Why this matters here:** The boilerplate lemmas in RTLdmrproof/RTLtmrproof
(`genv_symb_add_globals`, `find_symbol_tge_ge`, etc.) are already at the global
scope of their respective `Section PRESERVATION`. Moving them to `RTLreplicateProofCommon.v`
at global scope is safe; their proofs are `apply (Genv.find_symbol_match TRANSF)` which
takes `TRANSF` as an explicit argument anyway.

**Verification:** After moving, `make backend/RTLdmrproof.vo` must still pass.

### Pattern 2: Ltac shared via a common file, not copy-pasted

**What:** Ltac tactics are file-scoped in Coq; there is no "import a tactic from a module".
The conventional solution is to `Require Import` the file containing the tactic definitions.

**When:** `gen_contra`, `gen_inv`, `gen_case`, `eager_case`, `lr_case`,
`reserve_instr_inv`, `state_incr_inv` are copied verbatim in both spec files.
Moving them to `RTLreplicateSpecCommon.v` and having both spec files do
`Require Import RTLreplicateSpecCommon` eliminates the duplication.

**Build order implication:** RTLreplicateSpecCommon.vo must be compiled before
RTLdmrspec.vo and RTLtmrspec.vo. The Makefile uses `coqdep` to derive this
automatically from `Require Import` lines, so no Makefile edit is needed.

### Pattern 3: One commit per logical move type

**What:** Keep three classes of commits strictly separate:
1. **Move-only commits** — copy code verbatim to new file, add `Require Import`, remove from
   source. Proof obligations are unchanged; the commit shows no `Proof.`/`Qed.` diffs.
2. **Extraction commits** — extract a helper lemma from inside a proof, state it separately.
   These can change proof obligations.
3. **Statement change commits** — modify a theorem's type signature. These must update
   ALL call sites in the same commit.

**Why:** Mix-type commits make bisect-based debugging of broken builds very hard.
In CompCert, a single `.vo` failure can block the full `make proof` from completing.

### Pattern 4: Section-local vs. file-local scope for match relations

**What:** The simulation match relations (`match_regsets`, `match_stackframes`,
`match_states`) must remain inside `Section PRESERVATION` because they reference
`prog`, `tprog`, `TRANSF`, `ge`, `tge` as section variables. Moving them out would
require threading these as explicit arguments through every lemma.

**Implication:** These are not candidates for `RTLreplicateProofCommon.v`.
The shared file should only contain lemmas with fully explicit arguments.

### Pattern 5: `smoveR_inv` and inversion tactics stay with their inductive

**What:** Each spec file defines a custom `smoveR_inv` Ltac tactic that destructs its
local `smoveR` inductive. Since `smoveR` has different arities in DMR (5 args) vs
TMR (6 args), these tactics cannot be shared and must remain in their respective files.

**General rule:** When sharing a tactic requires sharing the inductive it destructs,
and that inductive differs, do not share — keep symmetric but separate copies.

---

## Anti-Patterns to Avoid

### Anti-Pattern 1: Moving lemmas inside a Section to a shared file naively

**What goes wrong:** A lemma stated inside `Section PRESERVATION` in `RTLtmrproof.v`
references `prog`, `tprog`, `ge`, `tge`, `TRANSF` as section variables. If you copy
it verbatim to `RTLreplicateProofCommon.v` (which has no section), Coq will not compile
because those identifiers are unbound.

**Instead:** Either (a) keep the lemma in its original file, or (b) add the required
variables as explicit arguments and update all call sites in the same commit.

### Anti-Pattern 2: Introducing a typeclass functor for `rm_wf`

**What goes wrong:** The DMR and TMR `rm_wf` definitions have different types for `rm`
(`PMap.t reg` vs `PMap.t (reg * reg)`). A tempting unification is to parameterize over
the shadow type via a typeclass. However:
- The proof strategies for `rm_wf_neq_*` lemmas differ structurally (2-element NoDup
  vs 6-element NoDup); a single proof cannot serve both.
- The `match_regsets` definition differs in the number of quantified register variables.
- A typeclass approach would add abstraction overhead with minimal elimination of proof
  duplication, since the proofs themselves do not share structure.

**Instead:** Accept that `rm_wf` and its consequence lemmas remain parallel-but-separate
in DMR and TMR. Unify only the genuinely identical boilerplate (tactics, type utilities,
global env lemmas).

### Anti-Pattern 3: Deleting backup files before verifying no external reference

**What goes wrong:** `backend/Replicate3proof.v` references `Replicate` and `Replicatespec`
(now renamed to `RTLtmr`/`RTLtmrspec`). Deleting it without checking could fail if it
is somehow still in the coqdep graph. The untracked backup `.v` files are not in `FILES`
in the Makefile and not in `_CoqProject`, so they do not affect the build. But verify
with `rg 'Require.*Replicate3\|Require.*AdvSem'` before deletion.

**Instead:** Verify with `grep -rn` or `rg` that nothing currently compiling imports
the file, then delete in a dedicated cleanup commit.

### Anti-Pattern 4: Changing `no_votes` policy piecemeal

**What goes wrong:** `RTLagreement.v` (the TODO at line 139), `CSEproof.v` (TODO at
line 1574), and `driver/Complements.v` each carry a comment about how `no_votes`
should be handled. If these are addressed in separate commits without agreeing on
a single policy, you end up with a hybrid state where some files use the checker
and others use an explicit hypothesis.

**Instead:** Decide on one policy (Option A: explicit hypothesis everywhere, or
Option B: checker soundness discharges it), then implement it as a single commit
that touches all three files simultaneously.

---

## Reorganization Order (Dependency-Aware)

The key insight from the cleanup plan's suggested execution order (0, 1, 3, 2, 4, 5)
is that specification cleanup (Phase 3) must precede proof de-duplication (Phase 2),
because Phase 2 de-duplication relies on the relational spec being available to replace
monolithic proofs.

### Stage 1: File system cleanup (no proof changes)

1. Delete untracked backup files: `backend/backup_RTLinfercolor*.ml`,
   `backend/backup_Constpropproof.v`, `backend/DMRproof_backup*.v`,
   `backend/RTLfault_backup.v`, `backend/RTLAgreement_backup.v`,
   `driver/backup_Compiler.v`.
   - Verification: `make backend/RTLtmrproof.vo` — these files are not in
     the Makefile's `FILES` variable, so deletion cannot break the build.

2. Delete `backend/AdvSem.v` and `backend/Replicate3proof.v` — both are untracked
   (`git status` shows them as `??`) and not in `FILES`. Zero external references
   confirmed by `rg 'AdvSem\|Replicate3'`.

### Stage 2: Introduce RTLreplicateSpecCommon.v (move-only)

**Build order impact:** Must be added to the Makefile BACKEND variable between
RTLgen.v and RTLdmrspec.v (i.e., added to the list before RTLdmr.v so coqdep
can find it).

Moves:
- 6 Ltac tactics from RTLdmrspec.v / RTLtmrspec.v (verbatim, identical)
- `comp_of_typ` definition
- `is_actual_type` definition

Add `Require Import RTLreplicateSpecCommon` to both spec files.
Replace moved content with the `Require Import`.

Verification: `make backend/RTLdmrspec.vo backend/RTLtmrspec.vo`

### Stage 3: Introduce RTLreplicateProofCommon.v (move-only)

**Build order impact:** Must be added to BACKEND between RTLtyping.v and RTLdmrproof.v.

Moves:
- `genv_symb_add_globals`, `find_symbol_tge_ge`, `symbol_address_tge_ge`
- `pset_in_res_fold_right`
- `reg_used_in_code_in_elements_code_regs`
- `reg_used_in_code_in_all_regs_list`
- `param_in_all_regs_list`
- `list_norepet_nodup`, `has_type_list_length`, `lessdef_list_refl`
- `rs_in_singleton`, `rs_in_l_2`, `rs_map_ext`

**Constraint:** Move these OUT of `Section PRESERVATION` in the source files first
(if they are section-local), then move to the common file. If their proofs reference
section variables, make those variables explicit arguments.

Verification: `make backend/RTLdmrproof.vo backend/RTLtmrproof.vo`

### Stage 4: Relational spec for replication map (RTLdmrspec, RTLtmrspec)

Add to each spec file:
- A relational inductive `replication_map_rel` describing what the foldM algorithm
  produces.
- Prove: `replication_map_satisfies_rel` (implementation => relational spec).
- Prove: `rel_implies_rm_wf` (relational spec => `rm_wf`).
- Replace the monolithic `replication_map_wf_aux` with composition of these two lemmas.

This is the only stage where the spec file's theorem content changes. All downstream
proof files import `rm_wf` consequences, not `replication_map_wf_aux` directly, so
there is no downstream breakage if the lemma is preserved under the same name.

Verification: `make backend/RTLdmrspec.vo backend/RTLtmrspec.vo backend/RTLdmrproof.vo backend/RTLtmrproof.vo`

### Stage 5: Proof de-duplication within RTLtmrproof.v

Target: `maj_voteR_step` (lines 748-854) — the four-type-case duplication.
Extract a parametric helper:
```coq
Lemma maj_voteR_step_of_type (ty : typ) ...
```
and reduce each type-specific case to a single `apply maj_voteR_step_of_type`.

Target: `external_call_vote_lessdef` in RTLtolerant.v (line 1373) — four-type-case
duplication. Extract `vote_lessdef_of_type` parametric lemma.

Target: `no_votes_external_call` in Novotesproof.v (line 53) — 8-repeat structure.
Extract a `lookup_builtin_not_vote` helper.

Verification after each extraction: `make backend/RTLtmrproof.vo backend/RTLtolerant.vo backend/Novotesproof.vo`

### Stage 6: RTLtolerant.v structural split

Current structure (2849 lines, three logical concerns mixed together):
1. Match relations: `match_rs`, `match_rs_upto`, `match_stackframes`, `match_states`
2. Helper lemmas: `external_call_Three_Two`, `external_call_Three_Two'`,
   `external_call_vote_lessdef`, `builtin_or_external_sem_Three_Two*`
3. Main backward simulation theorem and the step lemma

The match relations are already partially isolated in `Section match_states`.
The split does NOT require a new file — it only requires reorganizing the current file
into clearly delimited sections with explanatory comments. A new file would add a
dependency layer without much benefit (all three sections reference each other).

**If a new file IS created** (e.g., `RTLtolerantMatch.v`), it would contain
only the match relation definitions and must precede `RTLtolerant.v` in the Makefile.

### Stage 7: no_votes policy alignment

Both files that need alignment:
- `backend/CSEproof.v` (line 1574): Add `Novotes.no_votes prog` as explicit hypothesis
  to `transf_program_correct`, and update `driver/Compiler.v`'s call site.
- `backend/RTLagreement.v` (line 139): Decide on the approach and clean out the
  extensive block of commented design notes.
- `driver/Complements.v`: Adjust `transf_c_program_to_rtl_preservation_faulty` if
  the hypothesis changes.

This stage must be done as one multi-file commit.

### Stage 8: Comment and dead code removal

Remove large commented-out proof blocks from:
- `backend/RTLagreement.v` (lines 18-207 are almost entirely comments)
- `backend/RTLtolerant.v` (scattered throughout)
- `backend/RTLtmr.v`, `backend/Novotes.v`, `backend/RTLfault.v`,
  `backend/RTLcolorcheck.v`, `driver/Complements.v`

Do NOT remove comments that explain design rationale (like the `no_votes` discussion
in RTLagreement.v). Do remove commented-out `Admitted` proof attempts and superseded
proof strategies.

---

## Build Order Implications

### Makefile BACKEND variable — required additions

The Makefile currently lists (relevant section):
```
RTLgen.v RTLgenspec.v RTLgenproof.v \
RTLdmr.v RTLdmrspec.v RTLdmrproof.v \
RTLtmr.v RTLtmrspec.v RTLtmrproof.v Builtins2.v \
RTLagreement.v RTLfault.v RTLtolerant.v \
RTLcolor.v RTLcolorcheck.v \
Novotes.v Novotesproof.v \
```

After introducing the two new files, it becomes:
```
RTLgen.v RTLgenspec.v RTLgenproof.v \
RTLreplicateSpecCommon.v \           <- NEW (before dmr/tmr)
RTLdmr.v RTLdmrspec.v RTLdmrproof.v \
RTLtmr.v RTLtmrspec.v RTLtmrproof.v Builtins2.v \
RTLreplicateProofCommon.v \          <- NEW (after spec, before proof)
RTLagreement.v RTLfault.v RTLtolerant.v \
RTLcolor.v RTLcolorcheck.v \
Novotes.v Novotesproof.v \
```

`coqdep` derives the fine-grained dependency order from `Require Import` lines, so the
Makefile list order only matters for ensuring the file is included in `FILES` at all.
Position it approximately correctly to avoid confusion.

### Critical path for parallel builds

`make proof -j$(nproc)` will correctly parallelize based on the coqdep graph.
The new common files become bottlenecks on the critical path: every job that previously
could compile independently must wait for `RTLreplicateSpecCommon.vo` and
`RTLreplicateProofCommon.vo`. In practice these files are small (compile in seconds),
so this is not a build time concern.

---

## Confidence Assessment

| Area | Confidence | Notes |
|------|------------|-------|
| Current module structure | HIGH | Directly read from source files |
| Shared tactic identification | HIGH | Verified verbatim identity in both spec files |
| Shared proof lemma identification | HIGH | Verified by reading lemma bodies |
| Genuinely unshared content (rm_wf family) | HIGH | Structural difference confirmed |
| Makefile integration pattern | HIGH | Pattern matches existing CompCert structure |
| Anti-Pattern: typeclass for rm | MEDIUM | Claim based on proof structure analysis; could be revisited |
| no_votes policy recommendation | MEDIUM | Multiple valid options exist; confirmed both are feasible |
| Build time impact of new bottleneck files | HIGH | These files will be small |

---

## Sources

- Direct inspection of `/home/alex/source/compcert/backend/RTLdmrspec.v` (1294 lines)
- Direct inspection of `/home/alex/source/compcert/backend/RTLtmrspec.v` (1450 lines)
- Direct inspection of `/home/alex/source/compcert/backend/RTLdmrproof.v` (1681 lines)
- Direct inspection of `/home/alex/source/compcert/backend/RTLtmrproof.v` (2633 lines)
- Direct inspection of `/home/alex/source/compcert/backend/RTLtolerant.v` (2849 lines)
- Direct inspection of `/home/alex/source/compcert/backend/RTLagreement.v` (207 lines)
- Direct inspection of `/home/alex/source/compcert/backend/Novotesproof.v` (380 lines)
- Direct inspection of `/home/alex/source/compcert/Makefile` BACKEND variable
- Coq Require/Import tutorial: [Basic library files and modules management](https://coq.inria.fr/platform-docs/RequireImportTutorial.html)
- Coq section mechanism: [Section mechanism documentation](https://rocq-prover.org/doc/v8.14/refman/language/core/sections.html)
- [coqdep man page](https://www.mankier.com/1/coqdep) — dependency analysis tool
- [Module best practices discussion](https://coq-club.inria.narkive.com/ux8RG4m7/module-best-practices)
