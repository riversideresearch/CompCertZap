# Technology Stack: Coq Proof Refactoring and Cleanup

**Project:** CompCert Fault-Tolerance Proof Cleanup
**Researched:** 2026-03-03
**Coq version in use:** 8.20.0 (OCaml 4.14.2)

---

## Executive Summary

This codebase has ~11,000 lines of Coq across the fault-tolerance extension. The core cleanup problems are:
- **Literal duplication**: 57/70 lemma names in RTLdmrproof.v appear identically in RTLtmrproof.v; 32/44 spec-level lemmas are shared between RTLdmrspec.v and RTLtmrspec.v.
- **Duplicated Ltac blocks**: `in_list`, `not_in_list`, `nodup_false`, `not_nodup`, `reg_used1`, `reg_used2` appear identically in both DMR and TMR proof files. No shared tactic file exists.
- **Dead commented code**: RTLagreement.v is 133/208 lines comment (64%); RTLtolerant.v has 244 commented lines out of 2850.
- **Monolithic spec proofs**: Both `RTLdmrspec.v` and `RTLtmrspec.v` contain a `replication_map_wf_aux` lemma with a known-messy inductive proof that should be split into relational spec + implementation + consequence.

The tools and techniques below are organized by what actually helps for this specific cleanup, not a survey of all Coq tooling.

---

## Recommended Stack

### Core Build Tooling (Already In Place)

| Tool | Version | Purpose | Status |
|------|---------|---------|--------|
| `coqc` | 8.20.0 | Compile `.v` to `.vo` | In use |
| `coqdep` | 8.20.0 | Dependency tracking for incremental builds | In use via Makefile |
| `coqwc` | 8.20.0 | Line count: spec/proof/comment breakdown | Available at `~/.opam/4.14.2/bin/coqwc` |
| `make backend/<file>.vo` | — | Fast targeted rebuild of one file | Primary workflow |
| `make proof -j$(nproc)` | — | Full proof integration check | Gate for each phase |
| `make check-admitted` | — | Grep for `Admitted`/`admit` in all source | Gate for commits |

**Why coqwc:** It separates spec lines, proof lines, and comment lines — directly useful for tracking cleanup progress. RTLtolerant.v is 524 spec / 1915 proof / 269 comments; after cleanup, proof lines should drop measurably. Run it before and after each phase.

### Analysis Tools (New, Worthwhile)

| Tool | Install | Purpose | Confidence |
|------|---------|---------|------------|
| `coq-dpdgraph` | `opam install coq-dpdgraph` | Find unused definitions; visualize what references what | MEDIUM |
| `ripgrep` (`rg`) | Already present | Cross-file reference checks before deletion | HIGH |
| `coq-tools` (JasonGross) | `pip install coq-tools` or clone | `minimize-requires.py` removes unused imports; `find-bug.py` isolates failures | MEDIUM |

**Why coq-dpdgraph:** The `dpdusage` command reports definitions with zero or few callers — directly answers "can I delete AdvSem.v and Replicate3proof.v?" without manual grep archaeology. Install once, run targeted queries on the files being cleaned.

**Why coq-tools `minimize-requires.py`:** After moving lemmas into shared modules, import lists in DMR/TMR files will need cleanup. This automates what would otherwise be trial-and-error manual removal.

**Why rg before dpdgraph:** For backup file deletion (Phase 1), `rg` is faster and sufficient: `rg 'AdvSem\|Replicate3proof' --include='*.v'` over the whole repo confirms there are no surviving references before deletion.

### Editor / Interactive Workflow

| Tool | Purpose | Confidence |
|------|---------|------------|
| Proof General (Emacs) | Step through proofs interactively when refactoring | HIGH — standard for CompCert-style development |
| coq-lsp + VSCode | Alternative: faster incremental checking, better hover info | MEDIUM — available (`coq-lsp` packages exist for 8.19/8.20), not installed in this repo's OPAM switch |
| VsCoq2 | VSCode alternative to coq-lsp | LOW — less mature |

**Recommendation:** Stay with Proof General if already set up. coq-lsp is worth installing if VSCode is the primary editor — its per-sentence timing hover helps identify which lemmas are slow to check. Do not switch editors mid-cleanup.

---

## Ltac Patterns for This Codebase

### What's Already Working (Keep)

The codebase uses standard CompCert Ltac conventions correctly. These are fine and should not be changed:

- `monadInv H` — invert monadic computation results. Used correctly throughout.
- `inv H` — inversion shorthand. Correct usage.
- `Section VOTE. Context {VT: vote_type} {vsem: VoteSemantics VT}.` — correct parameterization pattern for vote-polymorphic lemmas.
- Local `Ltac` blocks inside `Section` — appropriate for tactics that are file-specific.

### Pattern 1: Extract Shared Ltac to a Common File

**Problem:** `in_list`, `not_in_list`, `nodup_false`, `not_nodup` are defined identically in `RTLdmrproof.v` (lines 160-178) and should also exist for `RTLtmrproof.v` (which uses `NoDup` proofs without these helpers). `reg_used1` and `reg_used2` are identical in both files (RTLdmrproof.v lines 891-901, RTLtmrproof.v lines 1756-1765).

**Fix:** Create `backend/RTLreplicateProofCommon.v` and place shared Ltac definitions at the top level of a `Section` or directly at module scope. Then `Require Import RTLreplicateProofCommon` in both proof files.

```coq
(* backend/RTLreplicateProofCommon.v *)
Require Import Coqlib.

(* Tactic for proving membership in concrete lists. *)
Ltac in_list :=
  match goal with
  | [ |- In ?x (?x :: _) ] => left; reflexivity
  | [ |- In ?x (?y :: ?ys) ] => right; in_list
  end.

Ltac not_in_list :=
  match goal with
  | [ H: ~ In ?x (?y :: ?ys) |- _ ] => exfalso; apply H; in_list
  end.

Ltac nodup_false :=
  match goal with
  | [ H : NoDup (?x :: ?xs) |- _ ] => inv H; try not_in_list; nodup_false
  end.

Ltac not_nodup :=
  match goal with
  | [ |- ~ NoDup (?x :: ?xs) ] => intro HC; nodup_false
  end.
```

**Confidence:** HIGH — identical text in both files, mechanical extraction.

### Pattern 2: Parameterize the Four-Case Vote-Type Duplication

**Problem:** `maj_voteR_step` in `RTLtmrproof.v` (line 772 TODO) has four cases — one per vote type (int/float/long/single) — that are structurally identical except for which `vote_sem_*_ok` lemma and which value pattern match applies.

**Fix:** Introduce a lemma parameterized by a type tag and a proof that `vote_sem_*_ok` applies. The four cases then reduce to `destruct ty; apply vote_case_helper; auto`.

```coq
(* Hypothetical helper pattern *)
Lemma maj_voteR_case_helper ty r1 r2 r3 rs ... :
  (* hypothesis: vote_sem_ok applies for this ty *)
  vote_sem_ok ty (rs # r1) (rs # r2) (rs # r3) ->
  (* conclusion: step exists and register update is identity *)
  exists rs', ... /\ (forall r, rs # r = rs' # r).
```

**When to apply:** After the shared module exists. Extract once, call four times with the appropriate vote-type witness.

**Confidence:** MEDIUM — the four cases have the same skeleton but differ in `Archi.ptr64` handling for pointer types. Verify that all four cases can actually share one proof body before committing.

### Pattern 3: Break `check_col_instr_sound` into Per-Instruction Lemmas

**Problem:** `RTLcolorcheck.v` `check_col_instr_sound` is a single proof with one `destruct instr` branch per instruction type. Each branch is a self-contained proof of 10-30 lines. When any branch breaks, the whole proof must be debugged as a unit.

**Fix:** Extract one lemma per instruction case:
```coq
Lemma check_col_Iop_protected_sound pc op args res succ :
  check_col_instr pc (Iop op args res succ) = true ->
  is_protected op = true ->
  wc_instruction (fun n r => (col n) ! r) pc (Iop op args res succ).

Lemma check_col_Iop_safe_sound pc op args res succ :
  check_col_instr pc (Iop op args res succ) = true ->
  is_protected op = false ->
  wc_instruction (fun n r => (col n) ! r) pc (Iop op args res succ).
```

The top-level `check_col_instr_sound` then becomes `destruct instr; [apply check_col_Iop_protected_sound | ...]; auto`.

**Confidence:** HIGH — standard decomposition pattern, zero risk to theorem statements.

### Pattern 4: Relational Spec Decomposition for `replication_map_wf_aux`

**Problem:** Both `RTLdmrspec.v` (line 926 TODO) and `RTLtmrspec.v` (line 1043 TODO) contain a monolithic inductive proof of `replication_map_wf_aux` that the authors themselves mark as "a mess." The proof mixes: (a) showing the implementation satisfies an invariant, and (b) showing that invariant implies `rm_wf`.

**Fix (three-step):**

1. Define a relational specification of what `foldM new_reg` produces:
```coq
(* In RTLreplicateSpecCommon.v *)
Inductive rm_rel (s : state) : list reg -> PMap.t reg -> state -> Prop :=
| rm_rel_nil : rm_rel s [] (PMap.init xH) s
| rm_rel_cons : forall r r' regs rm s' s'',
    new_reg s = OK r' s' _ ->
    rm_rel s' regs rm s'' ->
    rm_rel s (r :: regs) (PMap.set r r' rm) s''.
```

2. Prove: `foldM ... = OK rm s' _` implies `rm_rel s regs rm s'`.

3. Prove: `rm_rel s regs rm s'` implies `rm_wf rm regs`.

**Why:** This is the standard technique for untangling "algorithm + invariant" monolithic inductive proofs. It also gives DMR and TMR parallel structure, since the relational spec differs only in arity (DMR: one copy reg, TMR: two copy regs).

**Confidence:** MEDIUM — the approach is standard but requires careful threading of the state monad's ordering invariants. Budget time for this. Verify the DMR version first, then port to TMR.

### Pattern 5: Replace Redundant Lemma (`external_call_Three_Two` in RTLtolerant.v)

**Problem:** `RTLtolerant.v` line 1164 has `external_call_Three_Two` (TODO: remove) and `external_call_Three_Two'` (stronger version with `Val.lessdef`). All callers should use the stronger version.

**Fix:** Search callers of `external_call_Three_Two`, migrate each to `external_call_Three_Two'`, delete the weaker lemma. This is a mechanical multi-site edit, not a proof rewrite.

**Confidence:** HIGH — straightforward once callers are enumerated with `rg`.

### What NOT to Do

**Do NOT introduce Ltac2** for this cleanup. The existing proof scripts work in Ltac1. Ltac2 provides better error messages and static typing, but migrating existing working proofs to Ltac2 introduces risk without benefit for a cleanup project. Ltac2 is appropriate for new automation in new proofs, not for refactoring existing Ltac1.

**Do NOT use `omega` or `lia` as a replacement** for manual integer reasoning that the existing proofs already handle correctly — the substitution may silently change proof structure in ways that break downstream lemmas.

**Do NOT use module functors** to share the DMR/TMR lemma infrastructure. The Coq module functor system has a well-known pitfall: instantiating a functor twice with the same module argument creates two distinct inductive types. For this codebase, sharing via `Require Import` of a common file with `Section`-parameterized lemmas is simpler and safer than functors.

**Do NOT add `Proof using` annotations** to existing proofs during cleanup. It is out of scope (the PROJECT.md says "not optimizing build times"). Adding them introduces noise in diffs without cleanup value.

---

## Verification Workflow Per Phase

```
Phase 1 (file deletion, new modules):
  rg 'AdvSem\|Replicate3proof' backend/ driver/ --include='*.v'  # confirm no refs
  git rm backend/AdvSem.v backend/Replicate3proof.v
  make backend/RTLreplicateProofCommon.vo                          # new file compiles
  make backend/RTLdmrproof.vo backend/RTLtmrproof.vo              # dependents still pass

Phase 2 (de-duplication):
  make backend/<changed-file>.vo                                   # after each logical chunk
  make check-admitted                                              # no new holes

Phase 3 (spec relational decomposition):
  make backend/RTLdmrspec.vo                                       # DMR spec passes first
  make backend/RTLtmrspec.vo                                       # then TMR
  make backend/RTLdmrproof.vo backend/RTLtmrproof.vo              # proof files still pass

Phase 4 (no_votes unification):
  make backend/CSEproof.vo backend/RTLagreement.vo
  make driver/Complements.vo                                       # top-level theorem intact

Phase 5 (hygiene):
  make proof -j$(nproc)                                            # full integration
  make check-admitted
  coqwc backend/RTLtolerant.v backend/RTLtmrproof.v               # verify reduction
```

**Commit discipline:** Separate commits by type. A commit that only moves lemmas (identical text, new file) must not mix in any proof changes. A commit that changes a lemma statement must migrate all call sites in the same commit. This prevents git bisect confusion when a future build breaks.

---

## Alternatives Considered

| Category | Recommended | Alternative | Why Not |
|----------|-------------|-------------|---------|
| Tactic language | Ltac1 (keep) | Ltac2 | Migration risk, no cleanup benefit |
| Code sharing | Common `.v` file with Require Import | Module functors | Functor instantiation creates distinct types |
| Spec decomposition | Relational spec + two lemmas | Keep monolithic | Monolithic proofs are the stated problem |
| Reference analysis | coq-dpdgraph | Manual grep | coq-dpdgraph is semantic, grep is syntactic; both useful |
| Build verification | `make <file>.vo` per change | Full `make proof` per change | Full build is 20+ min; targeted rebuild is seconds |

---

## Sources

- Coq 8.20.0 release notes and Ltac2 documentation: [Ltac2 reference](https://rocq-prover.org/doc/V8.20.0/refman/proof-engine/ltac2.html)
- coq-dpdgraph (unused definition finder): [GitHub rocq-community/coq-dpdgraph](https://github.com/rocq-community/coq-dpdgraph)
- coq-tools (import minimizer, bug minimizer): [GitHub JasonGross/coq-tools](https://github.com/JasonGross/coq-tools)
- awesome-coq tool list: [GitHub rocq-community/awesome-coq](https://github.com/rocq-community/awesome-coq)
- Asynchronous Proof Processing (Proof using): [Coq 8.20 docs](https://coq.inria.fr/refman/addendum/parallel-proof-processing.html)
- QED at Large (proof engineering survey): [verse-lab.org/papers/qed-at-large.pdf](https://verse-lab.org/papers/qed-at-large.pdf)
- Automatic Goal Clone Detection (2025): [ECOOP 2025 paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol333-ecoop2025/LIPIcs.ECOOP.2025.12/LIPIcs.ECOOP.2025.12.pdf)

---

## Codebase Measurements (Baseline)

Run before cleanup begins, re-run after each phase to track progress.

```
coqwc output (current):
     spec    proof comments
      524     1915      269  backend/RTLtolerant.v
      646     1838       45  backend/RTLtmrproof.v
      463     1095       39  backend/RTLdmrproof.v
       91      263        6  backend/Novotesproof.v
      473      709       28  backend/RTLdmrspec.v
      504      832       31  backend/RTLtmrspec.v
      195      240       74  backend/RTLcolorcheck.v
       25        0      152  backend/RTLagreement.v
     2921     6892      644  total (in-scope files)

Duplication metrics (current):
  - 57 of 70 lemma names in RTLdmrproof.v also appear in RTLtmrproof.v
  - 32 of 44 spec lemma names shared between RTLdmrspec.v and RTLtmrspec.v
  - 4 identical Ltac definitions duplicated across DMR/TMR proof files
  - RTLagreement.v: 133/208 lines (64%) are commented-out abandoned proof drafts
  - RTLtolerant.v: ~244 lines of commented-out abandoned proof drafts
```
