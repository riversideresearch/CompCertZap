# Improved Builtin Treatment in TMR

## What This Is

Relaxing CompCert's fault-tolerance extension so that pure, total builtins (e.g. `BI_fabs`, `BI_addl`, `BI_i64_bswap`) participate in Triple Modular Redundancy the same way safe `Iop` instructions do, while effectful, protocol-level, or semantically fragile builtins remain on the conservative White-only path. This touches the TMR pass, faulty RTL semantics, color system (spec/checker/oracle), and the tolerant proof.

## Core Value

A single shared builtin classification — consumed by TMR, faulty semantics, coloring spec, checker, and oracle — that correctly distinguishes replicable/faultable builtins from White-only builtins, with all proofs rebuilding.

## Requirements

### Validated

- ✓ TMR/DMR replication of `Iop` instructions — existing
- ✓ Color system (Red/Green/Blue/White/Pink) with spec, checker, oracle — existing
- ✓ Faulty RTL semantics with `maybe_zap` single-fault model — existing
- ✓ Tolerant backward simulation (3-voting TMR >= 2-voting faulty) — existing
- ✓ Protocol builtins (`smove`, `vote`) have dedicated coloring/TMR handling — existing
- ✓ All builtins conservatively White-only and non-faultable — existing (to be relaxed)

### Active

- [ ] Shared builtin classification defined in `common/Builtins.v`
- [ ] `builtin_can_replicate` and `builtin_can_fault` predicates with reflection lemmas
- [ ] Protocol-builtin recognizers (`smove`, `vote`, `check`) moved from `backend/RTL.v` to `common/Builtins.v`
- [ ] Semantic property validated: `builtin_function_sem_lessdef` sufficient for `val_compat`-based fault model
- [ ] TMR pass replicates safe builtins (emit per-color copies like `Iop`)
- [ ] TMR spec updated with `match_Ibuiltin_safe` case
- [ ] TMR proof generalized from `Iop` pattern for safe builtins
- [ ] Color spec has `wc_Ibuiltin_safe` rule analogous to `wc_Iop_safe`
- [ ] Color checker accepts replicated safe builtins
- [ ] Color oracle assigns basic colors to safe builtins
- [ ] `zap_allowed` relaxed for safe builtins in `RTLfault.v`
- [ ] Tolerant proof handles faulted safe-builtin case in `RTLtolerant.v`
- [ ] Classification accommodates x86, RISC-V, and aarch64 platform builtins

### Out of Scope

- Load instructions — similar issue but interact with memory directly, separate design needed
- Refactoring `is_protected` — follow-up cleanup, not part of this semantic change
- DMR+TMR mixed usage — plan assumes TMR-only theorem path
- `check` builtin as a replicable builtin — DMR-specific, kept conservative

## Context

- The existing `builtin_function_sem_lessdef` lemma in `common/Builtins.v` and its `known_builtin_sem` wrapper in `common/Events.v` provide semantic support, but must be validated against the `val_compat`-based fault model
- The `_t` vs `_p` helper split in `Builtins0.v` approximates the safe/unsafe boundary: `_t` helpers are total, `_p` helpers can return `None`
- Recognized builtins route through `known_builtin_sem` in `common/Events.v`, giving `E0` trace and unchanged memory — the right semantics for replication
- The detailed implementation plan is in `plans/builtin-treatment-plan.md`

## Constraints

- **Proof soundness**: All changes must preserve the main fault-tolerance theorem (`transf_c_program_to_rtl_preservation_faulty`)
- **Consistency**: TMR pass, faulty semantics, color spec, checker, and oracle must all agree on the classification
- **Architecture**: Classification must accommodate x86, RISC-V, and aarch64 platform builtins
- **Protocol builtins**: `smove`, `vote`, `check` retain their existing dedicated treatment

## Key Decisions

| Decision | Rationale | Outcome |
|----------|-----------|---------|
| Define classification in `common/Builtins.v` | Classification is about `builtin_function` and `lookup_builtin_function`, which live there | — Pending |
| Validate semantic property before TMR/coloring work | Main proof risk; retiring it early avoids wasted effort | — Pending |
| Keep `builtin_can_fault` aligned with `builtin_can_replicate` | Simplifies first implementation; can diverge later if needed | — Pending |
| Move protocol recognizers to `common/Builtins.v` | They belong with builtin definitions, not in `backend/RTL.v` | — Pending |
| Do not fold into `is_protected` | `is_protected` is about `operation`, not `external_function`; semantically different | — Pending |

---
*Last updated: 2026-03-14 after initialization*
