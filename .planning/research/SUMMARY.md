# Project Research Summary

**Project:** Improved Builtin Treatment for TMR (Triple Modular Redundancy)
**Domain:** Coq proof engineering — fault-tolerance extension for CompCert
**Researched:** 2026-03-14
**Confidence:** HIGH

## Executive Summary

This project extends a formally verified fault-tolerant CompCert fork to give `Ibuiltin` instructions the same first-class treatment that `Iop` instructions already receive. Currently, all non-protocol builtins are conservatively treated as White-only, non-faultable, and non-replicable — identical to `is_protected` operations. The research confirms that a well-defined subset of standard and platform builtins (those built with total `_t` constructors) are semantically safe to replicate under the fault model's `val_compat` relation, and that the required changes are localized, well-scoped, and follow existing patterns closely.

The recommended approach is a five-phase build ordered by dependency and risk. The central technical innovation is a new Boolean predicate `builtin_can_replicate` (defined once in `common/Builtins.v`) that classifies builtins by totality and purity. This predicate becomes the single source of truth consumed by the TMR pass, faulty RTL semantics (`zap_allowed`), color specification, color checker, and OCaml oracle. The `_t` vs `_p` constructor distinction in `Builtins0.v` is the structural boundary: total builtins (`mkbuiltin_nNt`, `mkbuiltin_vNt`) never return `None` on well-typed inputs and remain total under `val_compat`-corrupted inputs; partial builtins (`mkbuiltin_nNp`, `mkbuiltin_vNp`) can return `None` on faulted inputs and must stay excluded.

The primary risk is the gap between `Val.lessdef` (used by the existing `builtin_function_sem_lessdef` lemma) and `val_compat` (used by the fault model). This must be resolved before any other work begins, by proving a new `builtin_sem_val_compat` lemma that covers all 16 first-cut safe builtins. If any builtin fails this property check, it must be removed from the whitelist before TMR/coloring machinery is built on top of it. Doing the semantic validation first (Phase 1) retires the highest risk at minimum cost.

## Key Findings

### Recommended Stack

The project uses no new external tools or languages. All work is within the existing Coq/OCaml codebase. The representation choice is Boolean function (not inductive predicate) because the checker and TMR pass need a computable decision, not propositional reasoning. The existing `is_protectedb`/`is_protected`/`is_protectedb_spec` triple demonstrates the standard pattern: Boolean primary, propositional form derived on demand, reflection lemma proved by `destruct b; simpl; ...`. This same pattern appears in at least five places in the backend.

**Core technologies:**
- `Boolean function on builtin_function` (`builtin_can_replicate_bf`): primary classification — directly computable, extracted to OCaml, amenable to reflection; follows existing `is_protectedb` pattern (HIGH confidence)
- `reflect` lemma: bridges Bool/Prop for proof scripts — standard codebase idiom, proven via `destruct b; simpl` (HIGH confidence)
- New `builtin_sem_val_compat` lemma in `backend/RTLfault.v`: `val_compat` monotonicity for safe builtins — required because the existing `builtin_function_sem_lessdef` speaks only about `Val.lessdef`, which is strictly stronger than `val_compat` (MEDIUM confidence — proof strategy is clear, per-case verification not yet done)
- `external_function` wrapper (`builtin_can_replicate`): bridge from `Ibuiltin ef` to the `builtin_function`-level classifier — required because instructions carry `external_function`, not `builtin_function` directly (HIGH confidence)

**Critical version requirement:** No new dependencies. The project uses the codebase's existing Coq, OCaml, and Menhir setup.

### Expected Features

**Must have (table stakes — first-cut whitelist of 16 builtins):**
- `builtin_can_replicate` single predicate in `common/Builtins.v` — everything else depends on it
- Pure numerical total builtins safe: `BI_fabs`, `BI_fabsf`, `BI_fsqrt`, `BI_negl`, `BI_i16_bswap`, `BI_i32_bswap`, `BI_i64_bswap`, `BI_i64_umulh`, `BI_i64_smulh`, `BI_i64_stod`, `BI_i64_utod`, `BI_i64_stof`, `BI_i64_utof` — all `mkbuiltin_nNt`, total on same-constructor inputs
- x86 platform builtins safe: `BI_fmin`, `BI_fmax` — both `mkbuiltin_n2t`, total
- `zap_allowed (Ibuiltin ef _ _ _) = builtin_can_fault ef` — one-line relaxation to enable faults on safe builtins
- TMR pass replicates safe builtins: new match arm in `transf_instr` emitting per-color copies analogous to safe `Iop` path
- `wc_Ibuiltin_safe` rule in `RTLcolor.v` — analogous to `wc_Iop_safe`, gated on `builtin_can_replicate`, requires `is_basic` result color
- Color checker and oracle updated to accept and infer basic colors for safe builtins
- Tolerant proof new case: `wc_Ibuiltin_safe` in faulted backward simulation

**Should have (second-cut whitelist, 6 more builtins):**
- `BI_mull` safe — `mkbuiltin_v2t` with `Val.mull'`, needs slightly different proof pattern than `mkbuiltin_nNt`
- `BI_addl` safe (unconditional) — pointer-involving but total under `val_compat`; both `Vptr` and `Vlong` cases stay within constructor
- `BI_subl` safe (conditional on `Archi.ptr64 = false`) — mirrors `is_protected_Osubl` logic
- `BI_i64_shl`, `BI_i64_shr`, `BI_i64_sar` safe — `mkbuiltin_v2t` shifts; need generalized `val_compat` lemma (both args faulted, not just value with fixed immediate)

**Defer (v2+ / out of scope):**
- Partial builtins (`BI_select`, `BI_unreachable`, `BI_i64_sdiv`, `BI_i64_udiv`, `BI_i64_smod`, `BI_i64_umod`, `BI_i64_dtos`, `BI_i64_dtou`) — excluded by construction; `_p` constructors can return `None` on faulted inputs
- Protocol builtins (`smove`, `vote`, `check`) — already have dedicated coloring/TMR treatment; excluding from generic classification is the correct architecture
- `BR_splitlong` result support — requires separate `maybe_zap` extension
- Load instruction fault treatment — fundamentally different memory-address fault model; explicitly out of scope per PROJECT.md

### Architecture Approach

The fault-tolerance extension has six components that must be updated consistently: TMR pass, faulty semantics, color specification, color checker, color oracle, and the tolerant proof. All six currently treat non-protocol builtins uniformly (conservative White-only). The new classification threads through all six via a single Boolean function defined in `common/Builtins.v` and imported by all consumers. The tolerant proof (`RTLtolerant.v`) is the integration point that consumes all other components and is built last.

**Major components:**
1. `common/Builtins.v` — classification definition (`builtin_can_replicate`, `builtin_can_fault`) and semantic property lemma (`builtin_sem_val_compat`); single source of truth
2. `backend/RTLtmr.v` + `RTLtmrspec.v` + `RTLtmrproof.v` — TMR pass with new `match_Ibuiltin_safe` case; uses `map_builtin_arg` for register renaming (NOT flat list like `Iop`)
3. `backend/RTLfault.v` — `zap_allowed` relaxation; `builtin_sem_val_compat` lemma lives here (not in `common/` due to import direction)
4. `backend/RTLcolor.v` + `RTLcolorcheck.v` + `RTLinfercolor.ml` — color spec/checker/oracle with new `wc_Ibuiltin_safe` constructor and corresponding Boolean check
5. `backend/RTLtolerant.v` — new case in `exec_Ibuiltin` faulted path; three-way split (vote / safe / generic), uses semantic lemma and `is_basic` discharge

### Critical Pitfalls

1. **`val_compat` vs `Val.lessdef` gap** — `builtin_function_sem_lessdef` is insufficient for the fault model; prove `builtin_sem_val_compat` as the very first step before any other file changes; if any builtin fails this check, remove it from the whitelist immediately (addresses Phase 1 risk)

2. **Inconsistency across five consumers** — TMR pass, `zap_allowed`, color spec, checker, and oracle must all use exactly the same `builtin_can_replicate` boolean; define it once in `common/Builtins.v` and import everywhere; never reimplement the classification locally

3. **`maybe_zap_preserves_match_states` breaks on new `wc_instruction` constructor** — adding `wc_Ibuiltin_safe` creates a new case in the `inv_wc` inversion; must include `is_basic (col succ res)` as a premise in the rule so the existing tactic can extract it; test `RTLtolerant.vo` rebuild immediately after modifying `RTLcolor.v`

4. **`builtin_arg` encoding differs from `Iop` argument encoding** — `Ibuiltin` uses `list (builtin_arg reg)` trees, not flat `list reg`; the TMR proof must use `map_builtin_arg` and `eval_builtin_arg_proper`, not the flat-list lemmas used for `Iop`; do not assume the `Iop` proof pattern transfers directly

5. **Protocol builtin leakage into safe class** — replicate builtins (`smove`, `vote`, `check`) must be explicitly excluded; the `BI_replicate` branch of `builtin_can_replicate_bf` must return `false`; add a lemma confirming this so the tolerant proof can eliminate protocol cases by contradiction

## Implications for Roadmap

Based on combined research, the five-phase structure from ARCHITECTURE.md is the correct build order. Dependencies are strict: classification before everything, semantic validation before TMR/coloring, tolerant proof last.

### Phase 1: Classification and Semantic Validation

**Rationale:** Highest risk, lowest effort. The `val_compat` gap (Pitfall 1) is the single most dangerous unknown. If the semantic property cannot be proved for a candidate builtin, the entire design changes. Find this out at zero sunk cost, not after Phases 2-4 are built.

**Delivers:** `builtin_can_replicate` and `builtin_can_fault` in `common/Builtins.v`; `builtin_sem_val_compat` and `builtin_sem_val_compat_total` lemmas in `backend/RTLfault.v`; optionally, migration of protocol recognizers from `backend/RTL.v` to `common/Builtins.v`.

**Addresses:** First-cut whitelist of 16 builtins (table stakes from FEATURES.md); architectural requirement for single classification source (ARCHITECTURE.md)

**Avoids:** Pitfall 1 (val_compat gap), Pitfall 2 (inconsistency), Pitfall 7 (protocol builtin leakage)

### Phase 2: Faulty Semantics (`zap_allowed` Relaxation)

**Rationale:** Self-contained one-line change to `RTLfault.v`. Does not touch TMR or coloring. Safe to land early and independently. Validates that the fault model can express builtin faults at all.

**Delivers:** `zap_allowed (Ibuiltin ef _ _ _) = builtin_can_fault ef`; confirms `Ibuiltin` fault events can be constructed and reasoned about

**Uses:** Phase 1 classification (direct import)

**Avoids:** Pitfall 5 (`BR_splitlong` — restrict to `BR r` results in `zap_allowed` guard)

### Phase 3: Color System (Spec, Checker, Oracle)

**Rationale:** Can proceed in parallel with Phase 2 after Phase 1 completes. Color components (`RTLcolor.v`, `RTLcolorcheck.v`, `RTLinfercolor.ml`) do not depend on `zap_allowed` or the TMR pass. Building the color spec first makes the tolerant proof's `inv_wc` inversion well-defined.

**Delivers:** `wc_Ibuiltin_safe` constructor in `RTLcolor.v`; updated `check_col_instr` with soundness lemma in `RTLcolorcheck.v`; updated `instr_constraints` in `RTLinfercolor.ml`

**Implements:** Color specification component (ARCHITECTURE.md)

**Avoids:** Pitfall 3 (`maybe_zap_preserves_match_states` — test `RTLtolerant.vo` rebuild immediately after `RTLcolor.v` change); Pitfall 8 (color preservation `Regset.For_all` obligation — model `wc_Ibuiltin_safe` directly on `wc_Iop_safe`)

### Phase 4: TMR Pass, Spec, and Proof

**Rationale:** Can also proceed in parallel with Phase 2-3 after Phase 1. The TMR pass does not reference colors. The proof (`RTLtmrproof.v`) depends on `RTLtmrspec.v` and the classification but not on the color system.

**Delivers:** New `transf_instr` match arm for safe builtins in `RTLtmr.v`; `match_Ibuiltin_safe` constructor in `RTLtmrspec.v`; corresponding proof case in `RTLtmrproof.v`

**Implements:** TMR transformation component (ARCHITECTURE.md)

**Avoids:** Pitfall 4 (`builtin_arg` encoding — use `map_builtin_arg` not flat list; restrict to `BA`-only arguments for first cut); Pitfall 10 (dedup interaction — add safe-builtin path as distinct match branch, never route through `maj_vote_regs`)

### Phase 5: Tolerant Proof Integration

**Rationale:** Must come last. `RTLtolerant.v` is the integration point that consumes all outputs from Phases 1-4 simultaneously. The new `exec_Ibuiltin` case requires the match relation (Phase 4), color spec (Phase 3), fault semantics (Phase 2), and semantic lemma (Phase 1) all to be in place and consistent.

**Delivers:** New `exec_Ibuiltin` case in faulted backward simulation; three-way case split (vote / safe / generic); complete end-to-end proof that safe builtins are correctly handled under the single-fault model

**Uses:** All stack elements — `builtin_sem_val_compat`, `wc_Ibuiltin_safe`, `match_Ibuiltin_safe`, `zap_allowed` relaxation

**Avoids:** Pitfall 9 (White assumption leakage — explicit three-way split, do not modify the existing two-way split in-place); Pitfall 11 (tactic brittleness — audit all `inv_wc` usage, re-run full tolerant proof after each change); Pitfall 12 (memory effects — lemma confirming `builtin_can_replicate ef = true` implies successful `lookup_builtin_function`)

### Phase Ordering Rationale

- Phase 1 first because it is the risk gate: semantic validation determines whether the entire approach is viable. No sunk cost if the approach must change.
- Phases 2, 3, 4 can be parallelized: they all depend only on Phase 1's classification, and the three components (`zap_allowed`, color system, TMR pass) are independent of each other.
- Phase 5 last because `RTLtolerant.v` is the only file that must synthesize all three components simultaneously. Starting it before any of Phases 2-4 is complete creates a moving target.
- The second-cut whitelist (6 additional builtins including `BI_addl`, `BI_subl`, shifts) should be deferred until after Phase 5 closes the first-cut whitelist, to avoid reworking the tolerant proof twice.

### Research Flags

Phases requiring attention during implementation (not additional research, but proof-specific validation):

- **Phase 1:** The `val_compat` monotonicity lemma for `mkbuiltin_vNt` builtins (`BI_addl`, `BI_subl`, `BI_mull`, shifts) requires per-case analysis of the wrapped `Val.*` functions. This is tractable but has not been done. Validate before committing these to the whitelist.
- **Phase 5:** The `inv_wc` tactic in `RTLtolerant.v` is fragile under constructor additions. Plan for explicit hypothesis naming in the new case rather than relying on positional matching.

Phases with well-documented standard patterns (low uncertainty):

- **Phase 2:** `zap_allowed` change is a one-line edit with a clear model (`Iop` path).
- **Phase 3 (checker/oracle):** Directly mirrors the existing `Iop` split. The OCaml oracle change is unverified and low-risk.
- **Phase 4 (TMR pass, `transf_instr`):** Structurally parallel to safe `Iop` path; only novelty is `map_builtin_arg` vs flat list.

## Confidence Assessment

| Area | Confidence | Notes |
|------|------------|-------|
| Stack | HIGH | All findings grounded in direct codebase inspection; patterns are established and repeated 5+ times |
| Features | HIGH | Complete builtin inventory verified against `Builtins0.v`, `Builtins1.v`, `Builtins2.v`; `_t`/`_p` boundary is structural, not inferred |
| Architecture | HIGH | Component boundaries and data flow verified by reading all six affected files; build order derives from hard import dependencies |
| Pitfalls | HIGH | Each pitfall is grounded in specific line numbers in the existing code; the `val_compat` gap and `inv_wc` brittleness are concrete, documented failure modes |

**Overall confidence:** HIGH

### Gaps to Address

- **`val_compat` proof for `mkbuiltin_vNt` builtins** — the analysis in STACK.md is sound but the actual Coq proofs have not been written. Validate `BI_mull`, `BI_addl`, `BI_subl` (conditional), and the three 64-bit shifts before including them in the whitelist. These are second-cut builtins; the first-cut 16 (`mkbuiltin_nNt` only) have a cleaner proof path.

- **Protocol recognizer migration** — STACK.md and ARCHITECTURE.md both recommend moving `is_vote_builtin`, `is_green_smove_builtin`, `is_blue_smove_builtin` from `backend/RTL.v` to `common/Builtins.v`. This is an optional refactor that improves organization but is not required for correctness. Decide during Phase 1 planning whether to include it in the same commit.

- **`BR_splitlong` restriction documentation** — The restriction to `BR r` results for safe builtins should be documented explicitly in the `builtin_can_replicate` definition as a comment, so future contributors know to extend `maybe_zap` before adding `BR_splitlong`-result builtins to the whitelist.

## Sources

### Primary (HIGH confidence — direct codebase inspection)

- `common/Builtins.v` — `builtin_function` type, `lookup_builtin_function`, `builtin_function_sem_lessdef`
- `common/Builtins0.v` — `standard_builtin_sem`, `mkbuiltin_*` constructors, `_t`/`_p` naming convention
- `common/Events.v` — `known_builtin_sem`, `builtin_or_external_sem`, `extcall_properties`
- `backend/Builtins2.v` — `replicate_builtin` type, vote/smove/check semantics
- `backend/RTL.v` — `is_protected`/`is_protectedb`, protocol recognizers
- `backend/RTLcolor.v` — `wc_instruction` constructors (lines 114-204)
- `backend/RTLcolorcheck.v` — `check_col_instr` for builtins (lines 81-220)
- `backend/RTLinfercolor.ml` — `instr_constraints` for builtins (lines 276-324)
- `backend/RTLfault.v` — `val_compat`, `zap_allowed`, `maybe_zap`, existing `val_compat_*` lemmas
- `backend/RTLtolerant.v` — `maybe_zap_preserves_match_states`, `exec_Ibuiltin` faulted case (lines 904-1818)
- `backend/RTLtmr.v` — `transf_instr` (lines 179-223)
- `backend/RTLtmrspec.v` — `match_Iop_safe`, `match_Ibuiltin_2` (lines 156-210)
- `backend/RTLtmrproof.v` — `eval_builtin_arg_proper` (lines 1195-1222)
- `x86/Builtins1.v` — platform builtins `BI_fmin`/`BI_fmax`
- `riscV/Builtins1.v`, `aarch64/Builtins1.v` — empty platform builtin types
- `plans/builtin-treatment-plan.md` — detailed implementation plan (project-internal)
- `.planning/PROJECT.md` — project requirements and constraints

---
*Research completed: 2026-03-14*
*Ready for roadmap: yes*
