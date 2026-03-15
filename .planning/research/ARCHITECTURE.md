# Architecture Patterns

**Domain:** Builtin classification integration into CompCert fault-tolerance extension
**Researched:** 2026-03-14

## Current Architecture: How Builtins Flow Through the System

### Component Map

The fault-tolerance extension has six components that handle builtins. Today they all treat non-protocol builtins identically (conservatively White-only, non-faultable, non-replicated). The new classification must thread through all six in a consistent way.

```
                      +------------------------+
                      |  common/Builtins.v     |
                      |  (builtin_function,    |
                      |   lookup, sem, lessdef)|
                      +----------+-------------+
                                 |
              +------------------+------------------+
              |                  |                   |
    +---------v------+  +-------v--------+  +-------v--------+
    | common/Events.v|  | common/        |  | backend/       |
    | (external_call,|  | Builtins0.v    |  | Builtins2.v    |
    |  known_builtin |  | (standard_     |  | (replicate_    |
    |  _sem)         |  |  builtin_sem)  |  |  builtin: vote,|
    +--------+-------+  +--------+-------+  |  smove, check) |
             |                   |          +-------+--------+
             |                   |                  |
    +--------v-------------------v------------------v--------+
    |                    backend/RTL.v                        |
    |  (Ibuiltin instruction, protocol recognizers:           |
    |   is_green_smove_builtin, is_blue_smove_builtin,       |
    |   is_vote_builtin -- all defined here today)            |
    +----+----------+----------+-----------+-----------+-----+
         |          |          |           |           |
    +----v---+ +----v---+ +---v----+ +----v----+ +----v----+
    | RTLtmr | | RTL-   | | RTL-   | | RTL-    | | RTL-    |
    | .v     | | fault  | | color  | | color-  | | infer-  |
    | (TMR   | | .v     | | .v     | | check.v | | color   |
    |  pass) | | (zap)  | | (spec) | | (check) | | .ml     |
    +----+---+ +---+----+ +---+----+ +----+----+ | (oracle)|
         |         |          |           |       +----+----+
         |         |          |           |            |
    +----v---------v----------v-----------v------------v----+
    |                backend/RTLtolerant.v                   |
    |  (backward simulation: 3-voting TMR >= 2-voting faulty|
    |   consumes ALL of the above)                           |
    +-------------------------------------------------------+
```

### Component Boundaries

| Component | Responsibility | Consumes | Produces |
|-----------|---------------|----------|----------|
| `common/Builtins.v` | Builtin function type, lookup, `builtin_function_sem_lessdef` | `Builtins0.v`, `Builtins1.v`, `Builtins2.v` | `builtin_function`, `lookup_builtin_function`, semantic lemmas |
| `common/Events.v` | `external_call` dispatch, `known_builtin_sem`, `builtin_or_external_sem` | `Builtins.v` | Semantic properties used by all proofs |
| `backend/RTL.v` | RTL instruction type, protocol recognizers (`is_green_smove_builtin`, etc.) | `Builtins2.v`, `AST.v` | `instruction`, `is_*_builtin` predicates + Boolean + reflect |
| `backend/RTLtmr.v` | TMR transformation pass | `RTL.v`, `Builtins2.v` | Transformed `program` |
| `backend/RTLfault.v` | Faulty semantics with `maybe_zap` | `RTL.v`, `Builtins2.v` | `fstep`, `zap_allowed`, `val_compat` lemmas |
| `backend/RTLcolor.v` | Declarative color spec | `RTL.v`, `Events.v` | `wc_instruction`, `wc_function`, `wc_program` |
| `backend/RTLcolorcheck.v` | Verified Boolean checker | `RTLcolor.v` | `check_program`, `check_program_sound` |
| `backend/RTLinfercolor.ml` | Unverified OCaml oracle | (extracted types) | `infer_coloring` function |
| `backend/RTLtolerant.v` | Main backward simulation proof | All of the above | `transf_c_program_to_rtl_preservation_faulty` |

## Detailed Current Behavior Per Component

### 1. TMR Pass (`RTLtmr.v`)

`transf_instr` dispatches on the instruction constructor:

- **`Iop` with `~is_protected op`**: Triplicates the instruction (one per color world: Green, Blue, Red). Emits three copies operating on shadow registers.
- **`Iop` with `is_protected op`**: Majority-votes arguments, executes once in Red/White, copies result to shadows via `copy_to_shadows`.
- **`Ibuiltin` (ALL)**: Falls through to the wildcard `_ =>` case. Majority-votes all arguments, executes once, copies result to shadows. There is NO `Ibuiltin`-specific replication path.

The commented-out code at lines 161-170 and 225-279 shows the *intended* design: a `can_replicate_instr` function that would return true for some builtins. This was never implemented.

**Integration point for classification**: `transf_instr` needs a new match arm for `Ibuiltin ef bargs bres succ` that checks `builtin_can_replicate ef` and, when true, emits per-color copies analogous to the `Iop` safe path.

### 2. TMR Spec (`RTLtmrspec.v`)

`match_instr` has two `Ibuiltin` cases:

- **`match_Ibuiltin_1`**: No result register (`~ is_BR bres`). Votes args, then executes the builtin.
- **`match_Ibuiltin_2`**: Has result register (`BR res`). Votes args, executes builtin, copies result to shadows.

Neither case handles replicated builtins. A new **`match_Ibuiltin_safe`** constructor is needed, paralleling `match_Iop_safe`: three copies of the builtin on per-color registers, no voting, no shadow copy.

### 3. Faulty Semantics (`RTLfault.v`)

`zap_allowed` currently returns `False` for ALL `Ibuiltin`:

```coq
| Ibuiltin _ _ _ _ => False
```

This means no fault can ever target a builtin instruction's result register. To allow faults on safe builtins, the guard must become:

```coq
| Ibuiltin ef _ _ _ => builtin_can_fault ef
```

**Semantic requirement**: When a register is zapped to a `val_compat` value, the builtin must still execute (return `Some`). The existing `builtin_function_sem_lessdef` lemma in `Builtins.v` gives us `Val.lessdef` input -> `Some` output. But `val_compat` is weaker than `Val.lessdef` (it allows `Vint i -> Vint j` with `i <> j`). So the actual proof obligation is: for safe builtins, `val_compat`-corrupted inputs still yield `Some` output.

For `_t` (total) builtins built with `mkbuiltin_n1t`/`mkbuiltin_n2t`/`mkbuiltin_n3t`, this holds by construction: `proj_num` returns `Vundef` on type mismatch, but `val_compat` preserves the type tag, so the correct `proj_num` branch is taken and the function returns `Some (inj_num ...)`. This is the core semantic property that must be validated.

For `_p` (partial) builtins (`BI_i64_sdiv`, `BI_i64_udiv`, etc.), the function can return `None`, so these must remain non-faultable.

### 4. Color Spec (`RTLcolor.v`)

`wc_instruction` has four `Ibuiltin` cases:

1. **`wc_Ibuiltin_smove_green`**: Green smove protocol coloring (White -> Pink for arg, Green for res).
2. **`wc_Ibuiltin_smove_blue`**: Blue smove protocol coloring (Pink -> Red for arg, Blue for res).
3. **`wc_Ibuiltin_vote`**: Vote protocol coloring (Red/Green/Blue args -> White result).
4. **`wc_Ibuiltin`**: Generic catch-all. Guards: `~ is_green_smove`, `~ is_blue_smove`, `~ is_vote`. Forces all arg regs White, all result regs White.

A new **`wc_Ibuiltin_safe`** constructor is needed, analogous to `wc_Iop_safe`:
- `builtin_can_replicate ef = true`
- `is_basic (col succ res)` (Red, Green, or Blue)
- All args have same color as result: `col pc arg = col succ res`
- Non-arg, non-res live registers preserve color across the edge

### 5. Color Checker (`RTLcolorcheck.v`)

`check_col_instr` for `Ibuiltin` dispatches on protocol predicates:

1. `is_green_smove_builtinb ef` -> checks green smove coloring
2. `is_blue_smove_builtinb ef` -> checks blue smove coloring
3. `is_vote_builtinb ef` -> checks vote coloring
4. `else` -> checks all args/res White, generic liveness preservation

The `else` branch needs a new sub-dispatch:

```
if builtin_can_replicate_ef ef then
  check safe-builtin coloring (basic result, same-color args)
else
  existing White-only check
```

The soundness lemma `check_col_instr_sound` must be extended to prove the new Boolean check implies `wc_Ibuiltin_safe`.

### 6. Color Oracle (`RTLinfercolor.ml`)

`instr_constraints` for `Ibuiltin'` dispatches:

1. Green smove -> constrain arg=White, succ_arg=Pink, succ_res=Green
2. Blue smove -> constrain arg=Pink, succ_arg=Red, succ_res=Blue
3. Vote -> constrain args=Red/Green/Blue, res=White
4. `else` -> constrain all arg regs=White, all res regs=White, liveness preservation

The `else` branch needs a new sub-dispatch for safe builtins: instead of constraining to White, union arg colors with result color (like the safe `Iop` path), letting the union-find assign a basic color.

### 7. Tolerant Proof (`RTLtolerant.v`)

The backward simulation's `exec_Ibuiltin` case splits on:

**Non-faulted path (lines 904-1011)**:
1. Is it a vote? -> Special vote handling with `list_lessdef_mod_1`
2. Otherwise -> `eval_builtin_args_lessdef'` + `external_call_mem_extends` + `external_call_Three_Two'`

**Faulted path (lines 1503-1800+)**:
1. `inv_wc` dispatches into green smove / blue smove / vote / generic cases
2. Each case proves that the Two-semantics target can simulate the Three-semantics source step
3. For generic builtins, it uses `match_rs` (which says faulted register = lessdef except one color column) to prove arguments are lessdef, then uses `external_call_mem_extends`

**A new case** must be added for safe builtins in the faulted path. The structure parallels `wc_Iop_safe` in `RTLtolerant.v`: when the instruction has basic color `c`, the faulted register is in a different color column, so we get exact equality for two of the three copies, and a `val_compat` value for the faulted one. After voting, the result is correct. But safe builtins are replicated (not voted), so the argument is different: the faulted copy produces a val_compat result, and the two non-faulted copies produce the correct result; the majority vote at the next use recovers the correct value.

## Data Flow: How Classification Propagates

```
                    common/Builtins.v
                    +---------------------------------+
                    | builtin_can_replicate : ef -> bool
                    | builtin_can_fault : ef -> bool  |
                    | (+ Prop versions + reflect)     |
                    | (+ semantic lemma:              |
                    |   builtin_val_compat_safe)      |
                    +---------+-----------+-----------+
                              |           |
           +------------------+     +-----+----------+
           |                        |                |
  +--------v--------+    +---------v------+   +-----v----------+
  | RTLtmr.v        |    | RTLfault.v     |   | RTLcolor.v     |
  | transf_instr:   |    | zap_allowed:   |   | wc_Ibuiltin_   |
  |  if can_repli-  |    |  if can_fault  |   |  safe:         |
  |  cate ef then   |    |  ef then True  |   |  if can_repli- |
  |  triplicate     |    |  else False    |   |  cate ef then  |
  |  else vote+exec |    +-------+--------+   |  basic color   |
  +--------+--------+            |            +-----+----------+
           |                     |                  |
  +--------v--------+           |            +-----v----------+
  | RTLtmrspec.v    |           |            | RTLcolorcheck.v|
  | match_Ibuiltin_ |           |            |  check safe-   |
  |  safe            |           |            |  builtin color |
  +--------+--------+           |            +-----+----------+
           |                     |                  |
           |                     |            +-----v----------+
           |                     |            | RTLinfercolor  |
           |                     |            |  .ml: safe     |
           |                     |            |  builtins get  |
           |                     |            |  basic color   |
           |                     |            +-----+----------+
           |                     |                  |
  +--------v---------------------v------------------v----------+
  | RTLtolerant.v                                              |
  | New case: wc_Ibuiltin_safe in faulted backward sim         |
  | Uses: can_replicate for match_instr dispatch               |
  |        can_fault for zap_allowed discharge                 |
  |        semantic lemma for val_compat safety                |
  +------------------------------------------------------------+
```

### Classification Must Be Importable From `common/`

All consumers sit in `backend/`, but the classification lives in `common/Builtins.v` because:

1. `builtin_function` and `lookup_builtin_function` are defined there
2. The classification is about the `builtin_function` type itself
3. `common/Events.v` (which provides `external_call`) depends on `Builtins.v`, not vice versa
4. No backend dependencies are needed -- the classification depends only on the builtin's identity and signature, not on RTL or operations

### Protocol Recognizer Migration

The protocol recognizers (`is_green_smove_builtin`, `is_blue_smove_builtin`, `is_vote_builtin`) currently live in `backend/RTL.v` because they match on `external_function` constructors with specific names/signatures. They are about `EF_builtin name sig`, which is an `AST.v` type, not an `RTL.v` type.

**Recommendation**: Move them to `common/Builtins.v` alongside the new classification. This provides:
- A single location for "what kind of builtin is this?"
- Cleaner imports for the color spec/checker (currently imports all of `RTL.v` just for these predicates)
- The new `builtin_can_replicate` can explicitly exclude protocol builtins:
  ```coq
  Definition builtin_can_replicate (ef : external_function) : bool :=
    match ef with
    | EF_builtin name sg =>
        match lookup_builtin_function name sg with
        | Some (BI_standard b) => negb (standard_builtin_is_partial b)
        | Some (BI_platform b) => platform_builtin_can_replicate b
        | Some (BI_replicate _) => false  (* protocol builtins *)
        | None => false                   (* unrecognized *)
        end
    | _ => false  (* EF_external, EF_malloc, EF_free, etc. *)
    end.
  ```

## Patterns to Follow

### Pattern 1: The `is_protected` / `is_protectedb` / `is_protectedb_spec` Triple

Every semantic predicate in this codebase follows the pattern:

```coq
(* Propositional version *)
Inductive is_foo : T -> Prop := ...

(* Boolean decision procedure *)
Definition is_foob (x : T) : bool := ...

(* Reflection lemma connecting them *)
Lemma is_foob_spec (x : T) : reflect (is_foo x) (is_foob x).
```

The new classification should follow this exactly:

```coq
(* In common/Builtins.v *)
Definition builtin_can_replicate (ef : external_function) : bool := ...

(* Prop version derived from Boolean *)
Definition builtin_can_replicate_prop (ef : external_function) : Prop :=
  builtin_can_replicate ef = true.
```

Or, since the Boolean version is the primary one (checked at compile time), the Prop version can simply be `= true`.

### Pattern 2: Color Spec Constructor Per Instruction Category

Each "kind" of instruction behavior gets its own `wc_instruction` constructor:
- `wc_Iop_safe` vs `wc_Iop_protected`
- `wc_Ibuiltin_smove_green` vs `wc_Ibuiltin_smove_blue` vs `wc_Ibuiltin_vote` vs `wc_Ibuiltin`

Add `wc_Ibuiltin_safe` with the same structure as `wc_Iop_safe`:

```coq
| wc_Ibuiltin_safe : forall ef bargs res succ,
    builtin_can_replicate ef = true ->
    is_basic (col succ res) ->
    Forall (builtin_arg_forall (fun arg => col pc arg = col succ res)) bargs ->
    Regset.For_all (fun r => ...) (live !! pc) ->
    wc_instruction pc (Ibuiltin ef bargs (BR res) succ)
```

### Pattern 3: TMR Spec Two-Case Split

`match_Ibuiltin_1` (no result) and `match_Ibuiltin_2` (has result) split on `is_BR bres`. The new safe case only applies to `BR res` results (you need a result to replicate). Add:

```coq
| match_Ibuiltin_safe :
    forall ef bargs1 bargs2 bargs3 res1 res2 res3 n1 n2 succ
    (SAFE : builtin_can_replicate ef = true)
    (ARGS : rm_l_bargs rm bargs1 bargs2 bargs3)
    (RM_RES : rm !! res1 = (res2, res3))
    (PC : c ! pc = Some (Ibuiltin ef bargs2 (BR res2) n1))
    (N1 : c ! n1 = Some (Ibuiltin ef bargs3 (BR res3) n2))
    (N2 : c ! n2 = Some (Ibuiltin ef bargs1 (BR res1) succ)),
    match_instr re rm c pc (Ibuiltin ef bargs1 (BR res1) succ)
```

Note: `rm_l_bargs` needs to be defined to lift `rm_l` over `builtin_arg` lists, or the bargs can be restricted to `[BA r1; ...]` form. The first-cut restriction to `BA`-only args (no `BA_splitlong`, `BA_addptr`, etc.) is acceptable for the initial implementation.

## Anti-Patterns to Avoid

### Anti-Pattern 1: Scattering the Classification Across Files
**What:** Defining `builtin_can_replicate` in RTLtmr.v, a separate `builtin_can_fault` in RTLfault.v, etc.
**Why bad:** Inconsistency risk. If the predicates diverge, the tolerant proof breaks in subtle ways.
**Instead:** Single definition in `common/Builtins.v`, imported everywhere.

### Anti-Pattern 2: Deep Matching on Builtin Names
**What:** Pattern-matching on `"__builtin_fabs"`, `"__builtin_bswap"`, etc. in the classification.
**Why bad:** Fragile, verbose, must be updated for every new builtin.
**Instead:** Match on `builtin_function` constructors (`BI_standard b`) and use structural properties of the `standard_builtin_sem` definition (total vs partial) to determine safety.

### Anti-Pattern 3: Trying to Handle `builtin_arg` Combinators in Round 1
**What:** Supporting `BA_splitlong (BA hi, BA lo)` or `BA_addptr` in safe builtin replication from day one.
**Why bad:** `rm_l_bargs` over arbitrary `builtin_arg` trees is complex. The TMR pass would need to substitute shadow registers inside nested `builtin_arg` constructors.
**Instead:** First cut: only `Ibuiltin ef [BA r1; ...; BA rN] (BR res) succ` with all-`BA` arguments qualifies as safe. This covers all standard total builtins on 64-bit targets. Extend later if needed.

### Anti-Pattern 4: Validating Semantics After Architecture
**What:** Building all TMR/coloring machinery before confirming that `val_compat` inputs actually yield `Some` output for the chosen builtins.
**Why bad:** If the semantic property fails, everything built on top must be reworked.
**Instead:** Validate the semantic lemma first (Phase 1), before any TMR/coloring changes.

## Suggested Build Order (Dependencies)

```
Phase 1: Classification + Semantic Validation
  common/Builtins.v
    |-- builtin_can_replicate, builtin_can_fault
    |-- builtin_val_compat_safe lemma
    |-- (optional) protocol recognizer migration
  No other file changes needed. Validate builds.

Phase 2: Faulty Semantics
  backend/RTLfault.v
    |-- zap_allowed uses builtin_can_fault
  Depends on: Phase 1
  Self-contained change; does not affect TMR pass or coloring.

Phase 3: Color System (spec, checker, oracle)
  backend/RTLcolor.v        -- add wc_Ibuiltin_safe
  backend/RTLcolorcheck.v   -- add safe-builtin check branch + soundness
  backend/RTLinfercolor.ml  -- add safe-builtin constraint generation
  Depends on: Phase 1
  Can proceed in parallel with Phase 2.

Phase 4: TMR Pass + Spec
  backend/RTLtmr.v          -- add safe-builtin replication
  backend/RTLtmrspec.v      -- add match_Ibuiltin_safe
  backend/RTLtmrproof.v     -- prove match for new case
  Depends on: Phase 1 (for classification)
  Can proceed in parallel with Phases 2-3.

Phase 5: Tolerant Proof
  backend/RTLtolerant.v     -- new exec_Ibuiltin case for safe builtins
  Depends on: ALL of Phases 1-4
  This is the integration point that consumes everything.
```

### Why This Order

1. **Phase 1 first** because it is the highest-risk, lowest-effort validation. If `val_compat` safety cannot be proved for the chosen builtins, the entire design must change. Finding this out after building Phases 2-4 wastes effort.

2. **Phases 2, 3, 4 can be parallelized** because they consume Phase 1's classification but do not depend on each other. `zap_allowed` does not reference colors. Colors do not reference `transf_instr`. The TMR pass does not reference colors.

3. **Phase 5 last** because `RTLtolerant.v` is the integration point that must dispatch on all the new cases from Phases 2-4 simultaneously. It cannot be started until the match relation, color spec, and fault semantics all exist.

## Scalability Considerations

| Concern | Current (0 safe builtins) | Target (standard_total safe) | Future (platform builtins safe) |
|---------|--------------------------|------------------------------|--------------------------------|
| Classification | N/A | ~15 builtins safe | Add per-platform `platform_builtin_can_replicate` |
| TMR code size | 1 Ibuiltin path | 2 Ibuiltin paths | Same 2 paths (classification decides) |
| Color spec | 4 constructors for Ibuiltin | 5 constructors | Same 5 (classification decides) |
| Tolerant proof | ~300 lines for Ibuiltin | ~500 lines (new case) | Same structure, no growth |
| Oracle (OCaml) | 4-way dispatch | 5-way dispatch | Same 5-way (classification decides) |

The design scales well because the classification is a Boolean function: adding new safe builtins only changes `builtin_can_replicate`, not the structure of any proof.

## Sources

- All findings are HIGH confidence: derived from direct reading of the CompCert fork's source files
- `common/Builtins.v` (lines 1-98): builtin_function type, lookup, sem_lessdef
- `common/Builtins0.v` (lines 48-584): standard_builtin type, _t vs _p helpers
- `backend/Builtins2.v` (lines 1-417): replicate_builtin type, vote/smove/check semantics
- `backend/RTLtmr.v` (lines 179-223): transf_instr wildcard case for builtins
- `backend/RTLtmrspec.v` (lines 198-210): match_Ibuiltin_1, match_Ibuiltin_2
- `backend/RTLfault.v` (lines 52-61): zap_allowed returns False for Ibuiltin
- `backend/RTLcolor.v` (lines 114-204): wc_instruction constructors for builtins
- `backend/RTLcolorcheck.v` (lines 81-220): check_col_instr for builtins
- `backend/RTLinfercolor.ml` (lines 276-324): instr_constraints for builtins
- `backend/RTLtolerant.v` (lines 904-1800+): exec_Ibuiltin cases in backward sim
- `backend/RTL.v` (lines 1063-1265): protocol recognizer definitions
- `plans/builtin-treatment-plan.md`: existing design document
