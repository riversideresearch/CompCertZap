# Plan: Extending Fault Tolerance to RISC-V Assembly

## Goal

Prove an Asm-level analogue of `transf_c_program_to_rtl_preservation_faulty`:

```coq
Theorem transf_c_program_preservation_faulty:
  forall p tp col_tree beh,
    transf_c_program p = OK tp ->
    Asmcolorcheck.check_program tp = Some col_tree ->
    let col := coloring_of_tree (Genv.globalenv tp) col_tree in
    program_behaves (asm_faulty_semantics col tp) beh ->
    exists beh', program_behaves (Csem.semantics p) beh'
              /\ behavior_improves beh' beh.
```

This says: if a C program compiles successfully, the Asm output passes the color checker (which produces a coloring tree `col_tree` keyed by function identifier), and the Asm program exhibits some behavior under faulty execution (with faults determined by the coloring), then there exists a corresponding C-level behavior that is at least as good. Note that `check_program` returns `option (PTree.t asm_coloring)` rather than `bool`, since the coloring is needed to parameterize the fault semantics. The `coloring_of_tree` function converts from the `ident`-keyed tree (produced by the checker, which operates on the program AST) to the `block`-keyed `asm_program_coloring` (needed by the fault semantics), using the global environment to map identifiers to blocks.

## Overview of the Proof Strategy

The RTL-level proof composes four refinements:

```
C >=2 RTL(no votes) >=3 RTL(no votes) >=3 RTL+TMR >=2,faulty RTL+TMR
 (1) standard       (2) weak agree    (3) TMR sim  (4) faulty sim
```

The Asm-level proof extends this to:

```
C >=2 RTL(no votes) >=3 RTL(no votes) >=3 RTL+TMR >=3 Asm >=2,faulty Asm
 (1) standard       (2) weak agree    (3) TMR sim  (4) backend (5) faulty sim
```

Steps (1)-(3) are unchanged from the RTL proof -- weak agreement is established at the RTL level via `no_votes_weak_agreement'` (as in `Complements.v:475`), not at Asm level. Step (4) is a backward simulation from RTL+TMR@Three to Asm@Three, obtained by composing the existing backend pass-by-pass forward simulations at the 3-voting instantiation and converting via `forward_to_backward_simulation`. Step (5) is the new Asm-level faulty backward simulation, analogous to the RTL-level `faulty_backward_simulation` but for RISC-V Asm.

**No Asm-level weak agreement is needed.** The existing proof structure in `Complements.v` bundles weak agreement inside `transf_c_program_to_rtl'_preservation'`, which transitions from 3-voting RTL to C-level behavior. This is reused as-is; we only need to bridge from Asm back to RTL@Three, then compose with the existing RTL-level chain.

## Detailed Phased Plan

---

### Phase 0: Parameterize RISC-V Asm by vote_type

**Motivation.** The x86 `Asm.v` already wraps its semantics in `Section VOTE. Context {VT: vote_type} {vsem: VoteSemantics VT}.` The RISC-V `riscV/Asm.v` does not. This parameterization is needed because the Asm-level faulty simulation targets 2-voting while the source uses 3-voting, just as in the RTL proof.

**Files to modify:**
- `riscV/Asm.v` - wrap `Section RELSEM` through `semantics` in `Section VOTE`

**Actions:**
1. Add `Section VOTE. Context {VT: Builtins2.vote_type} {vsem: Builtins2.VoteSemantics VT}.` around the semantics section, following the x86 pattern.
2. Verify that `Pbuiltin` semantics uses the vote_type-parameterized external_call (it should, since external_call for vote builtins dispatches through `VoteSemantics`).
3. Generalize `semantics_determinate` to work for the parameterized `semantics` (it currently proves determinacy for the un-parameterized version at `riscV/Asm.v:1152`). The faulty backward simulation (Phase 6) needs determinacy of `Asm.semantics@Three`.
4. Update downstream files that reference `Asm.semantics`, `Asm.step`, `Asm.state`, etc. This includes:
   - `riscV/Asmgenproof.v` — does NOT currently have `Section VOTE`; needs parameterization
   - `riscV/Asmgenproof1.v` — does NOT currently have `Section VOTE`; needs parameterization
   - `riscV/SelectOpproof.v` — does NOT currently have `Section VOTE`; its x86 counterpart does
   - `riscV/SelectLongproof.v` — does NOT currently have `Section VOTE`; its x86 counterpart does
   - `driver/Complements.v`
   Note: **No** RISC-V file currently has `Section VOTE` (unlike x86, where `Asm.v`, `Asmgenproof.v`, `SelectOpproof.v`, and `SelectLongproof.v` all do). All RISC-V-specific proof files that are counterparts to x86 files with `Section VOTE` must be updated.
5. Note: `backend/Asmgenproof0.v` already has VOTE parameterization (line 787) and should not need changes.
6. The generalization of `semantics_determinate` to the vote-parameterized version is non-trivial: it requires showing that vote builtins are deterministic under both `Two` and `Three` instantiations. The key insight: `Three`-voting is a deterministic partial function (if all three inputs are equal, return that value; otherwise return `Vundef`), so `external_call` for vote builtins under `Three` is deterministic (same inputs always produce the same output). Similarly, `Two`-voting is deterministic (if both inputs are equal, return that value; otherwise return `Vundef`). This makes the `sd_determ` obligation discharge cleanly for vote builtin steps.
7. Since the semantics was previously un-parameterized, all existing uses implicitly work at `Two`/`VoteSemantics_Two`. Wrap or instantiate them accordingly.

**Exit criteria:** `make proof` succeeds with RISC-V Asm parameterized by vote_type, targeting the `riscv-linux` configuration. Note: CompCert's build system compiles only one architecture at a time, so this requires `./configure riscv-linux` and a clean rebuild. During development, periodically switch back to `x86_64-linux` to verify the x86 build is not broken by shared-file changes.

**Risk:** Wide ripple. Mitigate by preserving backward compatibility: provide `Definition semantics_Two p := @semantics Two VoteSemantics_Two p` or a default instance so that most call sites need only minor updates.

**Important:** The current build configuration is `x86_64-linux`, meaning the RISC-V backend files have never been compiled with the fault tolerance extensions. Before starting Phase 0, configure and build for `riscv-linux` to surface any latent issues in the RISC-V instantiations of backend pass proofs (`Allocproof`, `Tunnelingproof`, `Linearizeproof`, `CleanupLabelsproof`, `Debugvarproof`, `Stackingproof`) when parameterized by `vote_type`. The intermediate backend languages (LTL, Linear, Mach) are architecture-independent and should already be correctly parameterized from the x86 work, but RISC-V-specific files may have issues that only manifest at build time.

---

### Phase 1: Asm-Level Fault Semantics (`riscV/Asmfault.v`)

**Motivation.** Define a faulty RISC-V Asm semantics analogous to `RTLfault.v`.

**New file:** `riscV/Asmfault.v`

**Design decisions:**

*State:* Wrap `Asm.state` with a fault bit, exactly as RTL:
```coq
Record fstate := mkfstate { fs_state : Asm.state ; fault : bool }.
```

*Initial and final states:* Define `initial_fstate` and `final_fstate` to construct the `Semantics` record for `asm_faulty_semantics`, following the pattern in `RTLfault.v:98-104`:
```coq
Inductive initial_fstate (p: program) : fstate -> Prop :=
| initial_fstate_intro : forall s,
    Asm.initial_state p s ->
    initial_fstate p (mkfstate s false).

Definition final_fstate (s : fstate) (r : int) : Prop :=
  Asm.final_state s.(fs_state) r.
```

Note: unlike a naive design that restricts final states to `fault = false`, the correct approach (matching `RTLfault.v:103-104`) ignores the fault bit entirely. A program that experiences and tolerates a fault should still be able to reach a final state; restricting to `fault = false` would make the theorem vacuously true for the most interesting case.

*Fault model:* A single fault that zaps the destination register of one instruction.

*What can be zapped — coloring-dependent classification:* At RTL level, `zap_allowed` is determined statically by the operation constructor (`~ is_protected op`). **At Asm level, a static per-opcode classification is insufficient** because the same Asm instruction constructor can arise from both protected and unprotected RTL operations. The key example: `Onegl` (NOT protected) compiles to `Psubl rd X0 rs`, while `Osubl` (protected when `Archi.ptr64 = true`, which is the case on 64-bit RISC-V) compiles to `Psubl rd rs1 rs2`. Neither classifying `Psubl` as always-faultable nor always-protected works — the first rejects `Osubl`-derived White results, the second rejects `Onegl`-derived basic-colored results.

Similarly, multi-instruction expansions of protected operations can include Asm instructions that are also used by unprotected operations. For example, `Ocmp (Ccomplu Cle)` (protected) expands to `Psltul; Pxoriw`, where `Pxoriw` is also generated for unprotected `Oxorimm`.

**Solution:** Make `asm_zap_allowed` depend on the coloring rather than solely on the instruction opcode. Since some instructions modify multiple data registers (e.g., `Pallocframe` modifies X30 and SP), we use `dests_of_instr : instruction -> list preg` that returns all data register destinations:
- `dests_of_instr (Pallocframe _ _) = [X30; SP]`
- `dests_of_instr (Pfreeframe _ _) = [SP]`
- For single-destination instructions: `dests_of_instr i = [r]` or `[]`

Then `asm_zap_allowed` checks whether any destination is basic-colored:
```coq
Definition asm_zap_allowed (col: asm_coloring) (pos: Z) (i: instruction) : Prop :=
  exists r, In r (dests_of_instr i) /\ is_basic (col (pos + 1) r).
```
An instruction is zappable iff *some* destination register is basic-colored (Red, Green, or Blue) at the successor position. When `Psubl` produces a White result (from `Osubl`), it is not zappable. When it produces a basic-colored result (from `Onegl`), it is. This naturally handles all dual-use instructions and multi-instruction expansion intermediates.

**Interaction with `asm_maybe_zap`:** The `asm_maybe_zap` relation zaps exactly ONE destination register `r` from `dests_of_instr i` (matching the single-fault model). `asm_zap_allowed` requires `exists r` with `is_basic`; `asm_maybe_zap` chooses a specific `r`. So an instruction is zappable if ANY destination is basic-colored, but only ONE destination is actually zapped per fault. For multi-destination instructions like `Pallocframe` where all destinations are White, `asm_zap_allowed` is `False` (since `is_basic White = false`), so they are never zapped.

**Note on `pos + 1` for non-fall-through instructions:** The definition uses `col (pos + 1) r` to look up the destination's color at the fall-through position. For branches and jumps, `pos + 1` is not the actual successor — but this is harmless because these instructions have no data register destination (`dests_of_instr` returns `[]` for branches/jumps), so `asm_zap_allowed` is vacuously `False` and the `col (pos + 1)` lookup is never reached. The one exception is `Pbtbl` (jump table), which clobbers X5 (a data register). We handle this by including X5 in `dests_of_instr (Pbtbl _ _)`; since X5 must be White at all positions (it's clobbered to `Vundef`), `is_basic White = false` makes `asm_zap_allowed` False regardless of which position is looked up.

The remaining classification of instructions that **never** have a destination register (and thus are never zappable regardless of coloring) is:
- **Store instructions**: no destination register.
- **Branches/jumps**: control flow only (set PC, which is not a data register).
- **Pbuiltin (all)**: votes and other builtins handled separately (builtins DO have destination registers via `res`, but are never zappable because `asm_fstep_builtin` bypasses `asm_maybe_zap`).
- **Labels, nops, debug directives** (Plabel, Pnop, Pcfi_rel_offset, Pcfi_adjust): no data register modification.
- **Function calls/returns**: handled specially.

Note: some pseudo-instructions that appear to be "framework" instructions DO modify data registers and must have their destinations listed by `dests_of_instr` (with White coloring):
- **Pallocframe**: modifies X30 (old SP) and SP — both are data registers. Also clobbers X31 (set to `Vundef`), but X31 is not a data register per `data_preg`, so it is not in `dests_of_instr`. `dests_of_instr (Pallocframe _ _) = [X30; SP]`. The `NON_DATA` invariant (`rs1 r = rs2 r` for non-data registers) is maintained because X31 is `Vundef` on both sides.
- **Pfreeframe**: modifies SP (restored from saved value) — SP is a data register. Also clobbers X31 (set to `Vundef`), same note as `Pallocframe`. `dests_of_instr (Pfreeframe _ _) = [SP]`.
- **Ploadsymbol, Ploadsymbol_high**: write to destination register `rd`. Do NOT clobber X31. `dests_of_instr (Ploadsymbol rd _ _) = [rd]`.
- **Ploadli, Ploadfi, Ploadsi**: write to destination register `rd` and clobber X31 (set to `Vundef`). Since X31 is not a data register, `dests_of_instr` returns only `[rd]`, not `[rd; X31]`. The X31 clobber is handled by the `NON_DATA` invariant (both sides set X31 to `Vundef`).
- **Pjal_s, Pjal_r**: write to RA (X1), which is not a data register per `data_preg`, so no color concern.

All of these should have White destinations. Since `Pallocframe`/`Pfreeframe` have all-White destinations, `is_basic White = false` means `asm_zap_allowed` is always `False` for them.

*val_compat:* Reuse the same `val_compat` from `RTLfault.v` (or factor it into a shared file).

*maybe_zap for Asm:* Needs to identify the destination preg(s) of each instruction. Define `dests_of_instr : instruction -> list preg` (see above). The `asm_maybe_zap` takes the coloring as a parameter and zaps exactly one destination register:
```coq
Inductive asm_maybe_zap (col: asm_coloring) (f: function) (pos: Z) :
  Asm.state -> bool -> Asm.state -> bool -> Prop :=
| asm_maybe_zap_refl : forall s b, asm_maybe_zap col f pos s b s b
| asm_maybe_zap_reg : forall rs m i r v,
    val_compat (rs r) v ->
    find_instr pos (fn_code f) = Some i ->
    In r (dests_of_instr i) ->
    is_basic (col (pos + 1) r) ->
    asm_maybe_zap col f pos
      (State rs m) false
      (State (rs # r <- v) m) true.
```

Note that this means `asm_faulty_semantics` is parameterized by the coloring (obtained from the color checker). The top-level theorem asserts that `check_program` succeeds, which provides the coloring used by the fault semantics.

*Step relation:* Wraps `@Asm.step Two VoteSemantics_Two` (hardcoded to 2-voting, matching the RTL-level pattern in `RTLfault.v:86-95`), applying `asm_maybe_zap` after each internal step (not builtins, not external calls). The step relation is parameterized by the coloring:
```coq
Inductive asm_fstep (col: asm_coloring) : fstate -> trace -> fstate -> Prop :=
| asm_fstep_internal : forall blk ofs f i rs m rs' m' s'' b b',
    rs PC = Vptr blk ofs ->
    Genv.find_funct_ptr ge blk = Some (Internal f) ->
    find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
    @exec_instr Two VoteSemantics_Two ge f i rs m = Next rs' m' ->
    asm_maybe_zap col f (Ptrofs.unsigned ofs) (State rs' m') b s'' b' ->
    asm_fstep col (mkfstate (State rs m) b) E0 (mkfstate s'' b')
| asm_fstep_builtin : forall b ofs f ef args res rs m vargs t vres rs' m' b',
    rs PC = Vptr b ofs ->
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some (Pbuiltin ef args res) ->
    eval_builtin_args ge rs (rs SP) m args vargs ->
    @external_call Two VoteSemantics_Two ef ge vargs m t vres m' ->
    rs' = nextinstr (set_res res vres (undef_regs (map preg_of (Machregs.destroyed_by_builtin ef)) (rs #X1 <- Vundef #X31 <- Vundef))) ->
    (* No zap; fault bit preserved unchanged *)
    asm_fstep col (mkfstate (State rs m) b') t (mkfstate (State rs' m') b')
| asm_fstep_external : forall b ef args res rs m t rs' m' b',
    rs PC = Vptr b Ptrofs.zero ->
    Genv.find_funct_ptr ge b = Some (External ef) ->
    @external_call Two VoteSemantics_Two ef ge args m t res m' ->
    extcall_arguments rs m (ef_sig ef) args ->
    rs' = (set_pair (loc_external_result (ef_sig ef)) res
             (undef_caller_save_regs rs)) #PC <- (rs RA) ->
    (* No zap; fault bit preserved unchanged *)
    asm_fstep col (mkfstate (State rs m) b') t (mkfstate (State rs' m') b').
```

Note that `asm_fstep_external` follows `RTLfault.v:93-96`'s `fstep_step_other` pattern: external function steps have no zap and preserve the fault bit. The match relation uses `asm_match_state_external` before this step and transitions back to `asm_match_state_internal` afterward (since `rs' PC = rs RA` points back to an internal function in the caller).

**Note on `Pbuiltin` and `asm_fstep_internal`:** The `asm_fstep_internal` constructor does not explicitly exclude `Pbuiltin` instructions. Instead, it relies on the fact that `exec_instr` returns `Stuck` for `Pbuiltin` (see `riscV/Asm.v:975-976`), making the `= Next rs' m'` premise unsatisfiable. Builtins are handled by the separate `asm_fstep_builtin` constructor. This implicit exclusion mirrors the standard `exec_step_internal` in RISC-V CompCert.

**Fault bit monotonicity:** The fault bit is monotonic: once `true`, it stays `true`. This follows from `asm_maybe_zap`: the `asm_maybe_zap_refl` constructor preserves the fault bit, while `asm_maybe_zap_reg` only fires when the input fault bit is `false` (transitioning to `true`). Consequently, in the `asm_match_rs` invariant, once a basic color `c` is excluded, it is excluded for all subsequent states. The excluded color's registers are never required to satisfy `Val.lessdef` again — correctness is maintained by the color system ensuring those registers' corrupted values are not read in contexts that could cause observable misbehavior (votes use majority voting to produce the correct result from the 2 non-excluded copies).

The faulty semantics is `asm_faulty_semantics col tp`, which wraps `@Asm.step Two VoteSemantics_Two`. The goal theorem's target is thus 2-voting faulty Asm, while the source is 3-voting non-faulty Asm.

**Subtlety: PC and nextinstr.** When zapping, we must not zap PC. The `dest_of_instr` function should never return PC (and instructions that set PC, like branches, should have `asm_zap_allowed = False`). Since `exec_instr` typically does `nextinstr (rs#d <- v)`, which updates both `d` and PC, the zap replaces only `d`'s value, not PC.

Actually, more precisely: `exec_instr` returns `Next rs' m'` where `rs'` already has PC updated. The zap then replaces `rs' r` with `v` for the destination register `r`. Since `r <> PC` (ensured by `asm_zap_allowed`), PC is preserved. This works cleanly.

**Exit criteria:** `riscV/Asmfault.v` compiles standalone.

---

### Phase 2: Asm-Level Color System (`riscV/Asmcolor.v`)

**Motivation.** Define what "well-colored" means for a RISC-V Asm program.

**New file:** `riscV/Asmcolor.v`

**Key design difference from RTL:** At RTL level, colors are assigned per (node, reg) pair because RTL has a CFG with named nodes and an unbounded set of pseudoregisters. At Asm level, instructions are in a linear list (code = list instruction) indexed by position, and there are finitely many physical registers (29 integer + 32 float = 61 data registers, as defined by `data_preg` in `riscV/Asm.v:1190`, which excludes X1/RA, X31/temp, and PC). Note: X0/zero is excluded by the *type system*, not by `data_preg` — the `preg` type uses `IR ireg` where `ireg = X1..X31`; X0 exists only in the `ireg0` type (used as source operands), so `IR X0` is not a valid `preg`.

**Target architecture:** This plan targets 64-bit RISC-V (`Archi.ptr64 = true`). Several instruction classifications (e.g., `Osubl` is protected only when `Archi.ptr64 = true`) and pointer comparison expansions depend on this. This assumption should be propagated throughout: either add `Archi.ptr64 = true` as a hypothesis to the top-level theorem, or (more likely, since `./configure riscv-linux` sets `Archi.ptr64 = true` globally) verify that the proofs in Phase 3 (checker soundness) and Phase 6 (faulty simulation) correctly case-split on `Archi.ptr64` where needed (e.g., `Osubl`-derived `Psubl`, pointer comparison expansions). Extending to 32-bit RISC-V would require revisiting these classifications.

The per-function coloring is a map from position (Z, the instruction offset) and register (preg) to color:
```coq
Definition asm_coloring := Z -> preg -> color.
```

The program-level coloring maps function blocks to per-function colorings:
```coq
Definition asm_program_coloring := block -> asm_coloring.
```

When execution transitions between functions (via call/return), the match relation looks up the new function's coloring from the program-level coloring using the target block. This is analogous to `RTLtolerant.v`'s `find_funct_ptr_wc_fundef`, which retrieves well-coloredness for the called function from the program-level hypothesis.

**Which registers get colored:** All data registers as defined by `data_preg`: integer X2-X30 and float F0-F31 (61 registers total). X1/RA and X31 are excluded by `data_preg` and treated as non-data. PC is never colored (it's always implicitly "White" or uncolored). X0 (zero register) is always 0 and cannot be written, so it doesn't need coloring either but can be treated as White.

**Liveness decision: quantify over all data registers (no Asm-level liveness analysis needed).**

At RTL level, `wc_function` requires `ProofLiveness.analyze f = Some live` and `wc_instruction`/`match_rs` quantify over `live !! pc` / `Regset.In r live`. At Asm level, we make a different and simpler choice: **quantify color consistency constraints over all data registers**, not just live ones. This is feasible because:
- There are only 61 data registers, so the constraint set is bounded and small at every program point.
- No Asm-level liveness analysis (`AsmProofLiveness.v`) is needed -- neither for the declarative spec, the checker, nor the faulty simulation proof.
- The `asm_match_rs` invariant in Phase 6 will quantify over `data_preg r = true` rather than a live set, which is simpler and still sufficient since dead registers can have any color (White by default).

The main consequence is that the color consistency rule ("for all registers not modified by the instruction, their color at the current position equals their color at the successor position") applies to all 61 data registers, not just live ones. This is a stronger but easily satisfiable constraint -- the color inference oracle simply assigns stable colors to all registers.

**Color rules:** Analogous to RTL's `wc_instruction`, but for each Asm instruction kind. Because `asm_zap_allowed` is coloring-dependent (see Phase 1), the color rules use a **unified approach** for arithmetic instructions — the same instruction constructor can be colored either with basic-colored (faultable) or White (protected) results, and the checker validates consistency. The key principles:

1. **Arithmetic (rd := op(rs1, rs2)), basic-colored result:** All sources must have the same basic color `c`, and the destination gets color `c` at the successor. The instruction is zappable.
2. **Arithmetic (rd := op(rs1, rs2)), White result:** Sources must be White and destination is White at the successor. The instruction is NOT zappable. This applies when the same instruction opcode is used for a protected RTL operation.
3. **Move (Pmv rd rs):** Destination gets color of source at successor.
4. **Load (rd := Mem[addr]):** Sources (address register) must be White, destination is White.
5. **Store:** Source and address register must be White.
6. **Branch (conditional):** Condition registers must be White. Color consistency must hold at **both** successors: the fall-through (pos+1) and the branch target (label position). This mirrors `wc_Icond` in `RTLcolor.v:192-196`, which requires `col pc r = col ifso r /\ col pc r = col ifnot r` for all non-argument registers.
7. **Unconditional jump (`Pj_l lbl`):** Color consistency must hold at the jump target (label position). There is no fall-through successor.
8. **Jump table (`Pbtbl rd tbl`):** The argument register must be White. Color consistency must hold at **all** target labels in the table, mirroring `wc_Ijumptable` in `RTLcolor.v:197-201`.
9. **Pbuiltin (vote):** Three argument registers must be Red, Green, Blue respectively. Result is White.
10. **Pbuiltin (smove):** Follows the White->Pink->Red and Green/Blue pattern from RTL.
11. **Pbuiltin (other):** Arguments White, result White.
12. **Call/return:** Argument registers White, result White, callee-save preserved.
13. **Consistency along control-flow edges:** For all data registers not modified by the instruction, their color at the current position equals their color at **every** successor position. For most instructions, the only successor is pos+1 (fall-through). For conditional branches, there are two successors (fall-through and branch target). For unconditional jumps, the successor is the target. For jump tables, the successors are all table entries. This is the Asm analogue of the per-successor consistency constraints in `wc_instruction`.

**No static `asm_is_protected` classification is needed.** Unlike RTL where `is_protected` is defined per operation constructor, at Asm level the protection status is determined by the coloring: an instruction is "protected" iff its destination is White, and "faultable" iff its destination is basic-colored. The color checker validates that the coloring is internally consistent (e.g., if an instruction's destination is basic-colored, all its sources have that same basic color). The color inference oracle, which has access to the compilation context, assigns colors that match the RTL-level `is_protected` through the compilation chain.

**Consistency through compilation:** The correctness of this approach relies on the color inference oracle producing colorings that are consistent with the RTL-level `is_protected` classification. For example, if `Iop Osubl` (protected) compiles to `Psubl`, the oracle assigns White to that `Psubl`'s destination; if `Iop Onegl` (not protected) compiles to `Psubl`, the oracle assigns a basic color. The verified checker then validates the coloring, and the faulty simulation proof uses the validated coloring to determine which instructions can be faulted.

**Tradeoffs of coloring-dependent fault model.** This design represents a significant departure from RTL's approach, where `zap_allowed` is a fixed property of the instruction opcode independent of any analysis. At Asm level, the set of faults covered by the theorem depends on the coloring produced by the checker. The theorem says "this program tolerates single faults to basic-colored-destination instructions per this specific coloring," not "this program tolerates arbitrary single faults to all arithmetic instructions." If the color inference oracle assigns White to an instruction that *could* have been basic-colored, that instruction is excluded from fault coverage — the theorem is still sound but covers fewer faults. In practice, the oracle assigns basic colors to exactly those instructions that originate from TMR-replicated unprotected RTL operations, so the coverage should be equivalent to the RTL-level coverage for a correctly-functioning oracle. An alternative approach would be to use compilation metadata (e.g., annotations from the TMR pass) to statically classify Asm instructions by their RTL origin, avoiding the dependence on the coloring. However, this would require threading metadata through the entire backend compilation chain, which is significantly more invasive. The coloring-dependent approach is simpler and sufficient: soundness is guaranteed by the verified checker regardless of which coloring the oracle produces, and coverage depends only on oracle quality.

**Exit criteria:** `riscV/Asmcolor.v` compiles standalone with the declarative spec.

---

### Phase 3: Asm-Level Color Checker (`riscV/Asmcolorcheck.v`)

**Motivation.** A verified Boolean checker for the Asm color system, analogous to `RTLcolorcheck.v`.

**New file:** `riscV/Asmcolorcheck.v`

**Structure:**
```coq
Axiom infer_coloring : Asm.function -> option asm_coloring.

Definition check_function (f: Asm.function) : option asm_coloring :=
  match infer_coloring f with
  | None => None
  | Some col => if check_col_function col f then Some col else None
  end.

Definition check_program (p: Asm.program) : option (PTree.t asm_coloring) :=
  (* collect per-function colorings into a PTree keyed by function ident *)
  ...

Lemma check_program_sound (p : Asm.program) (col_tree: PTree.t asm_coloring) :
  check_program p = Some col_tree ->
  forall b f, Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal f) ->
              asm_wc_function (coloring_of_tree (Genv.globalenv p) col_tree b) f.
```

The checker returns `option (PTree.t asm_coloring)` — a tree keyed by function identifier (`ident`), not by runtime memory block. This is because `check_program` is a pure function operating on the program AST and has no access to the global environment needed to map identifiers to blocks. The coloring is needed (not just a `bool`) because the fault semantics depends on it (since `asm_zap_allowed` is coloring-dependent).

**Constructing the program-level coloring:** `check_program` iterates over `AST.prog_defs`, checking each internal function definition and collecting per-function colorings into the `PTree.t asm_coloring`. The conversion from `ident`-keyed tree to `block`-keyed `asm_program_coloring` is done by `coloring_of_tree`:
```coq
Definition asm_program_coloring := block -> asm_coloring.

Definition coloring_of_tree (ge: Genv.t) (tree: PTree.t asm_coloring) : asm_program_coloring :=
  fun b => match Genv.invert_symbol ge b with
           | Some id => match tree ! id with Some col => col | None => default_coloring end
           | None => default_coloring
           end.
```

The soundness lemma `check_program_sound` proves that the converted coloring makes each internal function well-colored. This covers only internal functions. External functions are trivially well-formed — they have no code to check and no color constraints. This parallels `RTLtolerant.v:528-538` where `find_funct_ptr_wc_fundef` destructs on `fd` and handles `External` with `try constructor`. In the faulty simulation proof (Phase 6), `asm_wc_function` is only needed for internal functions (where the coloring is used); the `asm_match_state_external` constructor handles external functions without any well-coloredness requirement.

The resulting `asm_program_coloring := block -> asm_coloring` is consumed by the match relation (Phase 6), which looks up `col b` using the block from `rs PC = Vptr b ofs`. This approach parallels the RTL-level `wc_program` / `find_funct_ptr_wc_fundef` pattern.

`check_col_function` walks the instruction list, checking each instruction against the color rules. Since Asm code is a flat list (not a CFG), iteration is straightforward:
```coq
Fixpoint check_col_code (col: asm_coloring) (pos: Z) (c: code) : bool :=
  match c with
  | nil => true
  | i :: c' => check_col_instr col pos i && check_col_code col (pos + 1) c'
  end.
```

The checker must handle all 168 instruction constructors, but most cases follow a small number of patterns (register-register arithmetic, register-immediate arithmetic, load, store, branch, etc.). For branch and jump instructions, `check_col_instr` must resolve the label target position (via `label_pos`) and verify color consistency at the target, not just at pos+1. This is analogous to how `RTLcolorcheck` checks consistency along both successors of `Icond`.

**Exit criteria:** `riscV/Asmcolorcheck.v` compiles. `check_program_sound` is proved.

---

### Phase 4: Asm-Level Color Inference Oracle (`riscV/Asminfercolor.ml`)

**Motivation.** An unverified OCaml function that attempts to infer a coloring for a given Asm function.

**New file:** `riscV/Asminfercolor.ml`

**Design:** Follow the same union-find approach as `RTLinfercolor.ml`:
1. Create representative singletons for Red, Green, Blue, White, Pink.
2. Assign a singleton to each (position, register) pair. Since there are only 61 data registers, the table is `|instructions| * 61` entries, which is linear in function size (not quadratic as in RTL). **The liveness optimization is therefore unnecessary.**
3. Walk the instruction list, unioning registers based on constraints from the color rules. For branch and jump instructions, union registers at the current position with their counterparts at the branch target position (resolved via `label_pos`), not just at pos+1.
4. After unification, check that no two representative colors are in the same set. If they are, the function is not colorable (return None).
5. Read off the coloring from the union-find representatives.

**Differences from RTL oracle:**
- The "program points" are positions in the instruction list (Z), not CFG nodes.
- There are 61 data registers instead of an unbounded number of pseudoregisters.
- Successors must be computed from the instruction: fall-through is position+1, branches have label targets (resolved via `label_pos`).
- The instruction set is larger and more varied (many constructors), but structurally simpler (no SSA, no CFG).

**Exit criteria:** `Asminfercolor.ml` compiles. Manual testing on sample TMR-compiled programs shows it produces valid colorings.

---

### Phase 5: Wire Extraction and Driver

**Motivation.** Connect the Asm color checker and inference oracle into the compilation pipeline.

**Files to modify:**
- `extraction/extraction.v` - add extraction directive for `Asmcolorcheck.infer_coloring := Asminfercolor.infer_coloring`
- `driver/Driver.ml` - run Asm color checker on the final Asm output (in addition to or instead of the RTL checker)
- `Makefile.extr` or build system - ensure `Asminfercolor.ml` is compiled

**Actions:**
1. In `extraction/extraction.v`, declare:
   ```coq
   Extract Constant Asmcolorcheck.infer_coloring => "Asminfercolor.infer_coloring".
   ```
2. In `Driver.ml`, after assembly generation, call `Asmcolorcheck.check_program` on the Asm output. If it fails, report an error (the program may still be correct, just unverifiable for fault tolerance).
3. The RTL-level check can be kept as a diagnostic but is no longer the trust boundary.

**Exit criteria:** `make ccomp` succeeds. Compiling a test program with `-tmr` runs the Asm color checker.

---

### Phase 6: Asm-Level Faulty Backward Simulation (`riscV/Asmtolerant.v`)

**Motivation.** This is the core of the extension: prove that for well-colored Asm programs, the 3-voting non-faulty Asm semantics is simulated backward by the 2-voting faulty Asm semantics.

**New file:** `riscV/Asmtolerant.v`

**Theorem:**
```coq
Theorem asm_faulty_backward_simulation :
  forall col,
  asm_wc_program col prog ->
  backward_simulation
    (@Asm.semantics Three VoteSemantics_Three prog)
    (asm_faulty_semantics col prog).
```

Note that both `asm_wc_program` and `asm_faulty_semantics` are parameterized by the coloring `col`. The coloring determines which instructions can be faulted (those with basic-colored destinations).

**Match relation:** Analogous to RTL's `match_rs` but for Asm register sets (Pregmap). The coloring is position-dependent (`asm_coloring = Z -> preg -> color`), so the match relation is parameterized by the coloring instantiated at the current PC position. Since Asm state embeds PC in the register set (unlike RTL which has PC as a separate field), the current position is extracted via `rs PC`:
```coq
Definition asm_match_rs (col: preg -> color) (faulted: bool) (rs1 rs2: regset) : Prop :=
  if faulted then
    exists c, is_basic c /\
      forall r, data_preg r = true -> col r <> c -> Val.lessdef (rs1 r) (rs2 r)
  else
    forall r, data_preg r = true -> Val.lessdef (rs1 r) (rs2 r).
```

Here `col` is `coloring(current_pos)` -- the coloring instantiated at the PC-derived position. The full match state relation must extract the PC from the register set to look up the position-dependent coloring. **Crucially, the match relation needs two constructors** — one for when PC points to an internal function (the common case), and one for when PC points to an external function (which occurs transiently after `Pjal_s`/`Pjal_r` to an external function, before `exec_step_external` fires):
```coq
Inductive asm_match_state (coloring: asm_program_coloring) : Asm.state -> fstate -> Prop :=
| asm_match_state_internal : forall rs1 m1 rs2 m2 faulted b ofs f,
    rs1 PC = Vptr b ofs ->
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    asm_wc_function (coloring b) f ->
    asm_match_rs (coloring b (Ptrofs.unsigned ofs)) faulted rs1 rs2 ->
    (forall r, data_preg r = false -> r <> PC -> rs1 r = rs2 r) ->
    rs_compat rs1 rs2 ->
    rs1 PC = rs2 PC ->
    Mem.extends m1 m2 ->
    asm_match_state coloring (State rs1 m1) (mkfstate (State rs2 m2) faulted)
| asm_match_state_external : forall rs1 m1 rs2 m2 faulted b ef caller_col,
    rs1 PC = Vptr b Ptrofs.zero ->
    Genv.find_funct_ptr ge b = Some (External ef) ->
    asm_match_rs caller_col faulted rs1 rs2 ->
    (forall r, data_preg r = false -> r <> PC -> rs1 r = rs2 r) ->
    rs_compat rs1 rs2 ->
    rs1 PC = rs2 PC ->
    Mem.extends m1 m2 ->
    asm_match_state coloring (State rs1 m1) (mkfstate (State rs2 m2) faulted).
```

**Note on `asm_match_state_external` and fault-awareness:** The external constructor uses `asm_match_rs caller_col faulted rs1 rs2`, parameterized by `caller_col` — a snapshot of the caller's coloring at the call site (`coloring b_caller (Ptrofs.unsigned ofs_call)`). This snapshot is saved when `Pjal_s`/`Pjal_r` transitions from an internal function to an external function. The `caller_col` provides the color assignment needed by `asm_match_rs` to know which registers are excluded in the faulted case (those with the faulted color `c`), even though the external function itself has no coloring.

When the external call returns and PC goes back to the caller at `pos_call + 1`, the internal constructor is re-established using `coloring b_caller (Ptrofs.unsigned ofs_call + 1)`. The color consistency constraint ensures that for callee-save registers, `col(pos_call, r) = col(pos_call+1, r)`, so the saved coloring transfers. Caller-save registers become `Vundef` on both sides via `undef_caller_save_regs` (trivially `Val.lessdef`).

This mirrors the RTL proof's approach where `match_stackframes b` carries the fault bit and the return-site context through call/return transitions. At Asm level, `asm_match_state_external` plays the role of `match_states_Callstate`, and the saved coloring plays the role of `match_stackframes`.

The internal constructor is re-established at the return point because: (a) caller-save registers are set to `Vundef` on both sides (trivially `Val.lessdef`); (b) callee-save registers are unchanged, and color consistency across the call ensures their colors at `pos+1` match their colors at `pos`, so the `asm_match_rs` invariant transfers; (c) PC is set to `rs RA`, which is equal on both sides (RA is a non-data register); (d) the caller's `wc_function` is obtained from `asm_wc_program` via the new block.

Note: at RTL level, this is handled by separate state types (`Callstate`, `Returnstate`) with distinct match constructors (`RTLtolerant.v:510-524`). At Asm level, there is only `State rs m`, so the two-constructor approach on `find_funct_ptr` distinguishes the cases.

Compared to the RTL-level `match_states_State` (`RTLtolerant.v:499-509`), the internal constructor includes:

- **`asm_wc_function (coloring b) f`**: The current function is well-colored. This is essential for every instruction case: it provides the color constraints needed to reason about source matching, destination colors, and vote correctness. The well-coloredness is looked up from `asm_wc_program` via a `find_funct_ptr_asm_wc_fundef` lemma (analogous to `RTLtolerant.v:528-538`). When a call transitions to block `b'`, the new function's well-coloredness is obtained from the program-level hypothesis.

- **`NON_DATA: forall r, data_preg r = false -> r <> PC -> rs1 r = rs2 r`**: Non-data registers (RA/X1 and X31) are always equal between source and target. RA is critical because `Pj_r RA` sets `PC := rs RA` — if RA diverges, returns break the simulation. RA and X31 are never zapped (they are not data registers), but the proof must maintain their equality as an invariant. Instructions that write RA (Pjal_s, Pjal_r) write the same value on both sides; instructions that clobber X31 set it to `Vundef` on both sides.

- **`rs_compat rs1 rs2`**: Register compatibility, analogous to `RS_COMPAT` in `RTLtolerant.v:505`. This ensures `val_compat (rs1 r) (rs2 r)` for all registers, constraining the shape of zapped values. The invariant is maintained because: (a) in the non-faulted case, `Val.lessdef` implies `val_compat`; (b) when a zap occurs, `asm_maybe_zap` requires `val_compat (rs r) v` by construction; (c) for non-data registers, equality implies `val_compat`.

- **`coloring: asm_program_coloring`**: The match relation is parameterized by the program-level coloring (`block -> Z -> preg -> color`), not a per-function coloring. The current function's coloring is accessed via `coloring b` where `b` is the block from `rs1 PC = Vptr b ofs`. On call/return, `b` changes and the new function's coloring is automatically selected.

The position is extracted from `rs1 PC` via `Ptrofs.unsigned ofs` where `rs1 PC = Vptr b ofs`. The match relation requires PC to be a valid pointer (the `Vptr b ofs` witness is part of the constructor), ensuring the position is always well-defined.

Memory matching uses `Mem.extends` (not equality), following the RTL-level `match_states` in `RTLtolerant.v:499-524` which includes `MEM: Memory.Mem.extends m1 m2`. This is needed because the 3-voting source may have more precisely defined memory. **Direction subtlety for stores:** In the backward simulation, when the *target* takes a store step (which succeeds in m2), the proof must show the *source* can also store (in m1). `Mem.store_within_extends` proves the forward direction (m1 stores => m2 stores), not the backward direction needed here. However, since faults only affect registers (not memory), both sides start from the same initial state, perform identical allocation/deallocation sequences, and store to the same addresses (White address registers match exactly). This means both sides have identical permissions and identical `Mem.valid_access` throughout execution. Store success on the target side implies `Mem.valid_access` for that location, which is identical on the source side, so the source store also succeeds. Note: `Mem.extends` is about value definedness (the extending memory has values that are `Val.lessdef`-related), not about permissions — the permission identity comes from the structural argument that both sides perform the same operations.

Unlike RTL's `match_rs` which takes a `live : Regset.t` parameter (used only in the faulted case; the non-faulted case quantifies over all registers without liveness filtering), the Asm version quantifies over all data registers (`data_preg r = true`) since no Asm-level liveness analysis is used (see Phase 2).

**Proof structure:** The proof proceeds by case analysis on each Asm step. For each instruction:
1. **Non-faulted case (no zap):** The source and target step identically. Update the match relation by accounting for the destination register's new value. Color consistency ensures the invariant is maintained.
2. **Faulted case (zap occurs):** The target's destination register is replaced by an arbitrary value of compatible type. The match relation weakens to exclude the faulted register's color. Subsequent vote instructions will correct the damage because the other two copies (of different colors) are still correct, and majority voting produces the correct result.

**Key cases:**
- **Arithmetic (unprotected):** Source and target produce the same result (since inputs match by `Val.lessdef`). If zapped, the faulted register gets an arbitrary value but its color is marked. Subsequent vote on Red/Green/Blue registers will have 2 correct + 1 corrupted, and 2-voting semantics yields the correct result.
- **Vote (Pbuiltin vote):** Three arguments of colors Red, Green, Blue. By the match relation, at least two of the three match the source. The 2-vote semantics requires only 2 equal arguments to produce a defined result. The 3-vote semantics requires all 3 equal but the source register state has `Val.lessdef` (possibly Vundef on the 3-voting side due to the 3-voting strictness).
- **White-destination instructions (protected):** These have White destinations so `asm_zap_allowed` is False (since `is_basic White = false`). They can never be faulted. Source and target inputs are White, so they always match even after a prior fault. Result is White, so no color separation is needed.
- **Function call to internal function:** The call instruction (`Pjal_s`/`Pjal_r`) sets RA and PC. Since RA is a non-data register, it's always equal between source and target. PC points to the callee. The match relation transitions to the new function's coloring via `coloring b'`. The `asm_wc_function` for the new function is obtained from `asm_wc_program` via `find_funct_ptr_asm_wc_fundef`.
- **Function call to external function:** After executing `Pjal_s`/`Pjal_r`, PC points to an external function's block. The match relation uses the `asm_match_state_external` constructor (no coloring needed). The external call executes atomically on both sides, then returns to the caller via `PC <- rs RA`.
- **Return from external function:** After an external call completes (via `exec_step_external`), `undef_caller_save_regs` is applied and PC is set to `rs RA`. Since RA is equal on both sides, PC points back to the caller. The internal match constructor is re-established using the caller's coloring at `pos_call + 1`. **Callee-save color stability** is critical here: the coloring at pos+1 must assign the same colors to callee-save registers as at pos (the call site). This is enforced by the color consistency constraint (rule 13): `Pjal_s` does not modify callee-save registers, so for all callee-save registers `r`, `col(pos, r) = col(pos+1, r)`. Combined with the calling convention (callee-save register values are unchanged), the `asm_match_rs` invariant transfers directly from `caller_col` (the saved coloring snapshot) to the post-call coloring for callee-save registers. Caller-save registers become `Vundef` on both sides via `undef_caller_save_regs`, so they trivially match via `Val.lessdef_refl`. The excluded color `c` in the faulted case transfers directly: the same color `c` that was excluded in `asm_match_rs caller_col` is excluded in `asm_match_rs (coloring b_caller (pos+1))`, because the color consistency constraint ensures `caller_col r = coloring b_caller (pos+1) r` for callee-save registers, and caller-save registers match trivially regardless of color.
- **Return from internal function:** When an internal callee returns via `Pj_r RA`, the simulation has maintained the match relation through the callee's entire execution. PC becomes `rs RA`, which is equal on both sides (RA is a non-data register). The proof re-establishes `asm_match_state_internal` for the caller. Note: unlike external calls, internal calls do NOT invoke `undef_caller_save_regs` at the call point — `Pjal_s`/`Pjal_r` only set PC and RA. The callee may freely clobber caller-save registers during its execution, and the simulation proof maintains the match relation through all callee steps. The match relation at the return point is the result of the simulation running through the callee, not a simple application of `undef_caller_save_regs`.

**Backward simulation diagram type:** Following the RTL-level proof (`RTLtolerant.v:3237`), the backward simulation uses `Backward_simulation` with a well-founded order `fault_order` on the fault bit (a boolean order where `false < true`). This allows stuttering: when the target takes a step that triggers a fault (transitioning from `fault = false` to `fault = true`), the source may take zero steps (stuttering), with the decrease in `fault_order` ensuring well-foundedness. The RTL proof uses `Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ fault_order i' i)` as the simulation diagram — the Asm version should use the same pattern.

**Initial state match:** The `bsim_initial_states_exist` obligation requires showing that for every initial state of the 3-voting source, there exists a corresponding initial faulty state. This is straightforward: `initial_fstate p (mkfstate s false)` for any `Asm.initial_state p s`. The `bsim_match_initial_states` obligation requires showing the match relation holds initially: since both source and target start from the same initial state with `fault = false`, `asm_match_rs` holds by `Val.lessdef_refl` on all registers.

**Differences from RTL proof (`RTLtolerant.v`, ~3267 lines):**
- Asm has no CFG, so "successor" is just position+1 (or branch target). This simplifies some reasoning about color consistency along edges.
- Asm has more instruction cases (168 constructors vs. 10 RTL constructors), but most follow the same small set of proof patterns. Heavy use of Ltac automation is essential.
- Asm state is simpler: just `(regset, mem)`, no explicit call stack, function, SP, PC in the state record (they are in the regset). This means we don't need to match call stack frames etc. However, we do need to deal with the PC register explicitly.
- The `maybe_zap` at Asm level is analogous but operates on `preg` rather than `reg`.
- No liveness analysis is needed -- the match relation quantifies over all data registers.

**Estimation:** This will likely be the largest single file, perhaps 2000-4000 lines. The RTL version is ~3267 lines and Asm has more cases but potentially less complexity per case (no CFG reasoning).

**Exit criteria:** `riscV/Asmtolerant.v` compiles with `asm_faulty_backward_simulation` fully proved (no Admitted).

---

### Phase 7: Top-Level Theorem (`driver/Complements.v`)

**Motivation.** Compose all the refinements into the final Asm-level fault tolerance theorem.

**File to modify:** `driver/Complements.v`

**New theorem:**
```coq
Theorem transf_c_program_preservation_faulty:
  forall p tp col_tree beh,
    transf_c_program p = OK tp ->
    Asmcolorcheck.check_program tp = Some col_tree ->
    let col := coloring_of_tree (Genv.globalenv tp) col_tree in
    program_behaves (asm_faulty_semantics col tp) beh ->
    exists beh', program_behaves (Csem.semantics p) beh'
              /\ behavior_improves beh' beh.
```

**Proof outline:**
```
Given: Asmcolorcheck.check_program tp = Some col_tree
       col = coloring_of_tree (Genv.globalenv tp) col_tree
       program_behaves (asm_faulty_semantics col tp) beh

By check_program_sound: asm_wc_program col tp
                                                                [faulty sim]
(5) => exists beh4, program_behaves (Asm.semantics@Three tp) beh4
                    /\ behavior_improves beh4 beh

We factor transf_c_program into:
  transf_c_program = transf_c_program_to_rtl' ; transf_rtl_program_to_rtl' ; transf_rtl_program''
yielding intermediate programs:
  p --[c_to_rtl']--> p_rtl --[rtl_to_rtl']--> p_tmr --[rtl_to_asm]--> tp

                                                                [backend backward sim]
(4) => exists beh3, program_behaves (RTL.semantics@Three p_tmr) beh3
                    /\ behavior_improves beh3 beh4
   (via backward_simulation from RTL@Three to Asm@Three, obtained from
    forward_to_backward_simulation applied to the composed backend forward sim)

                                                                [TMR backward sim]
(3) => exists beh2, program_behaves (RTL.semantics@Three p_rtl) beh2
                    /\ behavior_improves beh2 beh3
   (via transf_rtl_program_to_rtl'_preservation)

                                                                [weak agreement + C-to-RTL backward sim]
(2+1) => exists beh0, program_behaves (Csem.semantics p) beh0
                    /\ behavior_improves beh0 beh2
   (via transf_c_program_to_rtl'_preservation', which internally applies
    no_votes_weak_agreement' at the RTL level and then the C-to-RTL backward sim)

Compose all behavior_improves transitively:
  behavior_improves beh0 beh
```

**Backend simulation construction (step 4):** This is non-trivial glue that requires:

1. **Factoring lemma:** Decompose `transf_c_program` into `transf_c_program_to_rtl'`, `transf_rtl_program_to_rtl'`, and `transf_rtl_program''` (note: two primes -- `transf_rtl_program''` in `Compiler.v:126` is the backend-only function from RTL to Asm; `transf_rtl_program'` at line 139 includes TMR+backend). Prove `transf_c_program p = OK tp -> exists p_rtl p_tmr, transf_c_program_to_rtl' p = OK p_rtl /\ transf_rtl_program_to_rtl' p_rtl = OK p_tmr /\ transf_rtl_program'' p_tmr = OK tp`. An analogous factoring lemma `apply_partial_factor` already exists for the RTL-level proof (`Complements.v:285-293`); this extends it one step further. Note: `transf_c_program` uses `transf_clight_program` (→ `transf_rtl_program`) while `transf_c_program_to_rtl'` uses `transf_clight_program_to_rtl` (→ `transf_rtl_program_to_rtl`). These have syntactically identical bodies (they are separate definitions with the same RHS), so their equivalence can be discharged by `unfold ...; reflexivity` (or via `print_identity`/`compose_print_identity` lemmas in `Compiler.v`). The equivalence propagates straightforwardly up through `transf_cminor_program`/`transf_cminor_program_to_rtl` and `transf_clight_program`/`transf_clight_program_to_rtl`. The more substantive factoring step is decomposing `transf_rtl_program'` into `transf_rtl_program_to_rtl'` followed by `transf_rtl_program''`, which requires reasoning about `print (print_RTL 12)` identity at the boundary (using `compose_print_identity`) and `apply_partial_factor`. The three-way split proof follows this sketch:
```coq
Lemma transf_c_program_factor3 p tp :
  transf_c_program p = OK tp ->
  exists p_rtl p_tmr,
    transf_c_program_to_rtl' p = OK p_rtl /\
    transf_rtl_program_to_rtl' p_rtl = OK p_tmr /\
    transf_rtl_program'' p_tmr = OK tp.
Proof.
  intro H.
  (* Step 1: split at the clight_to_rtl / rtl_to_asm boundary *)
  (* transf_c_program = transl_program @@@ transf_clight_program *)
  (* transf_clight_program body = transf_clight_program_to_rtl body ; transf_rtl_program' body *)
  (* These have syntactically identical bodies, so unfold; reflexivity works *)
  apply apply_partial_factor in H. destruct H as (p_mid & H1 & H2).
  (* Step 2: split transf_rtl_program' into transf_rtl_program_to_rtl' ; transf_rtl_program'' *)
  apply apply_partial_factor in H2. destruct H2 as (p_tmr & H2 & H3).
  (* compose_print_identity eliminates the print boundary *)
  eauto.
Qed.
```
This is routine (two applications of `apply_partial_factor` with `compose_print_identity` for the debug print boundaries) but must be done carefully to ensure the intermediate types match.

2. **Composed backend forward simulation at Three:** Compose forward simulations from `Allocproof.transf_program_correct`, `Tunnelingproof.transf_program_correct`, `Linearizeproof.transf_program_correct`, `CleanupLabelsproof.transf_program_correct`, `Debugvarproof.transf_program_correct`, `Stackingproof.transf_program_correct`, `Asmgenproof.transf_program_correct` into a single `forward_simulation (@RTL.semantics Three VoteSemantics_Three p_tmr) (@Asm.semantics Three VoteSemantics_Three tp)`. After Phase 0's vote_type parameterization of `riscV/Asmgenproof.v` and `riscV/Asmgenproof1.v`, instantiation at `Three` should be mechanical. The composition uses `compose_forward_simulations` repeatedly, following the pattern in the existing `transf_rtl_program_to_rtl'_forward_simulation`. Note: `Complements.v:28-71` already contains `transf_rtl_to_asm_match_prog` and `rtl_to_asm_passes` which compose the backend pass matches, and a commented-out `transf_rtl_program'_forward_simulation` (lines 77-100) that was never completed. This existing infrastructure should be built upon. **Investigation of the commented-out code:** The commented-out `transf_rtl_program'_forward_simulation` at `Complements.v:77-114` follows the standard CompCert pattern of composing pass simulations via `compose_forward_simulations`. It was commented out (not deleted) together with several other lemmas (`compiled_rtl_safe`, `compiled_asm_weak_agreement`) that represent earlier, pre-parameterization attempts at the proof. The code uses un-parameterized types (no `@...Three...`), confirming it predates the vote_type parameterization work. The approach itself — composing backend pass forward simulations — is standard and known to work (CompCert's own `transf_c_program_correct` does exactly this). The likely reason for abandonment was that it wasn't needed for the RTL-level theorem, not a fundamental blocking issue. After Phase 0 completes (vote_type parameterization of RISC-V files), this same composition should work at the `Three` instantiation, since each backend pass proof is generic over the vote_type. The main risk is that `Stackingproof.transf_program_correct` requires `return_address_offset` (provided by `Asmgenproof0`), which must also be parameterized — but `Asmgenproof0` already has VOTE parameterization (line 787). If any pass proof unexpectedly fails at `Three`, it would manifest as a type error during Phase 0, not as a silent correctness issue. This should be verified early in Phase 0 by attempting to build for `riscv-linux`.

3. **Conversion to backward simulation:** Apply `forward_to_backward_simulation` (from `common/Smallstep.v:1890`), which requires `receptive L1` and `determinate L2` for `forward_simulation L1 L2`. Here L1 = RTL@Three, L2 = Asm@Three, so we need `RTL.semantics_receptive` (exists at `backend/RTL.v:346`) and `Asm.semantics_determinate` (exists at `riscV/Asm.v:1152`, must be generalized to the vote_type-parameterized version in Phase 0). This yields a `backward_simulation (@RTL.semantics Three VoteSemantics_Three p_tmr) (@Asm.semantics Three VoteSemantics_Three tp)`.

This composition can be structured as a lemma `transf_rtl_program''_preservation`:
```coq
Lemma transf_rtl_program''_preservation p tp beh :
  transf_rtl_program'' p = OK tp ->
  program_behaves (@Asm.semantics Three VoteSemantics_Three tp) beh ->
  exists beh', program_behaves (@RTL.semantics Three VoteSemantics_Three p) beh' /\
            behavior_improves beh' beh.
```

**Exit criteria:** `make driver/Complements.vo` succeeds with the new theorem proved.

---

### Phase 8: Validation and Integration Testing

**Actions:**
1. `make proof` - all Coq proofs compile.
2. `make check-admitted` - no Admitted proofs in any file.
3. `make ccomp` - the compiler binary builds.
4. Compile test programs with `-tmr` targeting RISC-V and verify:
   - The Asm color checker accepts the output.
   - The compiled program runs correctly (with QEMU or similar).
5. Test edge cases: programs with function calls, loops, conditionals, multiple data types.

---

## Key Technical Challenges and Design Decisions

### 1. Register coloring at Asm level is simpler than RTL

At RTL, there are unbounded pseudoregisters, making the coloring domain large. At Asm, there are exactly 61 data registers (29 integer + 32 float, as defined by `data_preg`). This means:
- The liveness-based optimization for color inference is **unnecessary** at Asm level. A dense 61-entry table per instruction is O(n) in function size (61 is a constant), not O(n * r) with r growing proportionally to n as at RTL.
- The coloring is `Z -> preg -> color` where the `preg` domain is finite and small.
- The color consistency constraints are easier to check because the set is at most 61 registers.
- No Asm-level liveness analysis is needed for any part of the proof or checker.

### 2. Stack slots and memory

At the Asm level, "stack slots" from the Locations/LTL/Linear levels have been lowered to memory accesses via SP+offset. These are **memory operations** (loads and stores), not register operations. Since our fault model only corrupts registers (not memory), stack slot contents are immune to faults. This is actually simpler than RTL, where pseudoregisters include both what will become machine registers and what will become stack slots.

However, this means that values living in stack slots (spilled registers) lose their TMR color protection: once spilled, each copy gets its own stack slot, but when reloaded, the reload instruction (a load) has a White destination. Thus after reloading, the value is White and no longer redundantly protected by TMR — the TMR protection coverage is reduced for that value. This is correct behavior (not an error), since:
- Each spill still gets its own distinct stack slot (the allocator sees three independent live ranges)
- The color checker validates consistency: reloaded values are White-colored, and any subsequent operations on them follow White rules
- The fault model only corrupts registers, not memory, so the spilled values themselves are safe in memory

In practice, after register allocation, the TMR copies of a value should be in three different machine registers. If spilling occurs, the color inference will assign White to the relevant loads/stores and the checker will validate this. In the proof, after a spill+reload, the reloaded value is White and no longer basic-colored-protected. If the TMR pass subsequently uses smove to propagate the reloaded value back to basic-colored shadow copies before the next vote, the color checker validates this flow: the reload is White, the smove transitions White→Pink→basic, and the vote consumes Red/Green/Blue as expected. The color consistency constraints enforce that this chain is well-formed.

### 3. Multi-instruction expansion

Some RTL instructions expand to multiple Asm instructions. For example, `Iop Oaddimm` might become `Paddiw` (a single instruction), but `Iop Omulhs` might expand to multiple instructions. The TMR pass works at RTL level, so it replicates the RTL instruction, and then each replica expands independently to the same sequence of Asm instructions.

**For unprotected (basic-colored) operations:** The color of intermediate results within an expansion should all be the same basic color.

**For protected (White) operations that expand to multiple instructions:** All intermediate results should be White. For example, `Ocmp (Ccomplu Cle)` (protected when `Archi.ptr64 = true`) expands to `Psltul rd r2 r1 :: Pxoriw rd rd Int.one :: k` in `riscV/Asmgen.v:305`. Both the `Psltul` intermediate result and the final `Pxoriw` result should be White. This is handled naturally by the coloring-dependent `asm_zap_allowed` design (Phase 1): since both destinations are White, neither instruction is zappable, regardless of the fact that `Pxoriw` can also appear in faultable contexts.

The color checker validates each instruction independently based on the coloring. It does not need awareness of expansion boundaries — the color inference oracle, which has compilation context, ensures that the coloring is consistent across multi-instruction expansions.

### 4. Caller-save registers and function calls

At Asm level, there are two cases for function calls:

**External calls** (`exec_step_external`): `undef_caller_save_regs` is applied, setting caller-save registers to `Vundef` on both sides. After the call, the result is in a specific register (e.g., X10/A0) and is White. The TMR smove instructions will copy it to Green and Blue shadow registers. Caller-save registers trivially match via `Val.lessdef_refl` (both `Vundef`).

**Internal calls** (`Pjal_s`/`Pjal_r`): These instructions only set PC and RA — they do NOT call `undef_caller_save_regs`. The callee may freely clobber caller-save registers during its execution. The match relation is maintained through the callee's entire execution by the simulation proof itself, not by a one-shot application of `undef_caller_save_regs` at the call point.

**Callee-save registers** preserve their values across calls. Their colors should be stable across the call (the color checker enforces this via the consistency constraint along control-flow edges). The `asm_match_rs` invariant transfers across the call because callee-save registers are unchanged and their colors at `pos_call` equal their colors at `pos_call + 1`.

### 5. Temporary register X31

RISC-V reserves X31 as a temporary that some pseudo-instructions clobber (set to Vundef). X31 should be White (unprotected). The color checker should verify that X31 is never used as a TMR-protected register.

### 6. Determinacy and receptiveness

The faulty Asm semantics is nondeterministic (due to the zap). The non-faulty Asm semantics is deterministic (proved via `Asm.semantics_determinate` at `riscV/Asm.v:1152`, which must be generalized to the vote_type-parameterized version in Phase 0). Determinacy of the vote-parameterized version requires showing that vote builtins remain deterministic under both `Two` and `Three` instantiations. The key insight: both `Two` and `Three` voting are deterministic partial functions — given the same inputs, they always produce the same output (the majority value if enough inputs agree, `Vundef` otherwise). This makes `external_call` deterministic for vote builtins under any vote_type instantiation, and the `sd_determ` obligation for `semantics_determinate` follows.

For Phase 7's backend backward simulation construction, `forward_to_backward_simulation` requires `receptive RTL@Three` (from `RTL.semantics_receptive` at `backend/RTL.v:346`) and `determinate Asm@Three` (from the generalized `Asm.semantics_determinate`). Note: `Asm.semantics_receptive` does **not** exist in the codebase and is not needed.

### 7. `exec_instr` must not get Stuck on Vundef inputs for unprotected operations

The faulty backward simulation requires that whenever the target (2-voting faulty) steps, the source (3-voting non-faulty) can match. Since `asm_match_rs` uses `Val.lessdef`, the source can have `Vundef` where the target has a defined value (for registers whose color was faulted). If `exec_instr` returns `Stuck` when given `Vundef` inputs, the source would get stuck while the target steps, breaking the backward simulation.

For unprotected (basic-colored) arithmetic, CompCert's `Val.add`, `Val.mul`, `Val.and`, etc. map `Vundef` inputs to `Vundef` outputs (returning a value, not `None`), so `exec_instr` returns `Next` with `Vundef` rather than `Stuck`. Operations wrapped in `Val.maketotal` (like `Val.divs`, `Val.intoffloat`) also return `Vundef` for bad inputs via `Val.maketotal None = Vundef`. This property must be verified for every Asm instruction case in the faulty simulation proof.

For protected (White) operations, the arguments always match exactly (White registers are unaffected by faults), so the `Vundef` concern doesn't arise. Similarly, load/store addresses are White, so `exec_load`/`exec_store` always receive valid addresses.

For conditional branches, the comparison functions (`Val.cmpu_bool` etc.) can return `None` for `Vundef` inputs, which would make `eval_branch` return `Stuck`. But branch condition registers are required to be White, so they always match exactly.

Since the plan eliminates liveness-based quantification (quantifying over all data registers, not just live ones), ALL data registers including dead ones participate in the match relation. Dead registers may have `Vundef` on the source side. This is safe because dead registers are not read by subsequent instructions, but the proof must carefully track that only White (exactly-matching) registers are read by instructions that could Stuck.

### 8. The match relation must handle `nextinstr`

Every Asm instruction updates PC via `nextinstr`. The match relation must state that PC is always equal between source and target (or related by `Val.lessdef`). Since PC is never zapped (it's not a data register), this is straightforward: `rs1 PC = rs2 PC`.

### 9. Register allocation feasibility

The entire approach relies on the Asm color checker succeeding on programs compiled with `-tmr`. If the register allocator coalesces TMR shadow copies or spills them poorly, the color checker will fail, making the theorem vacuously true.

Key open questions:
- Does the register allocator's interference graph keep TMR copies separate? The TMR pass creates three independent live ranges for each replicated value, and the interference graph should naturally keep them in different registers.
- If register pressure forces spilling of TMR copies, what happens? Spilled values become memory (White after reload), which is safe but means fault tolerance coverage is reduced for those values.
- Are modifications to the register allocator needed? Possibly -- the allocator should be guided to keep TMR copies in distinct registers. This is an implementation concern, not a proof concern.

**This is a major feasibility risk.** Empirical validation should happen as early as possible — ideally *before* starting proof work. After Phase 0 (RISC-V vote_type parameterization), configure for `riscv-linux`, compile test programs with `-tmr`, and manually inspect whether TMR copies end up in distinct physical registers. CompCert's IRC register allocator should naturally keep TMR copies separate because the TMR pass creates three independent live ranges that interfere with each other, forcing distinct register assignments. However, under high register pressure, spilling may occur. After Phase 5 (oracle + wiring), the Asm color checker provides automated validation. If the checker frequently fails, allocator modifications (e.g., priority hints for TMR copies) may be needed — this is an implementation concern, not a proof concern.

---

## Dependency Graph

```
Phase 0: Parameterize RISC-V Asm by vote_type
    |
    v
Phase 2: Asmcolor.v (color spec)
   / \
  v   v
Phase 1  Phase 3: Asmcolorcheck.v (checker)
(Asmfault.v)    |
  |             v
  |       Phase 4 + Phase 5: Oracle + Wiring
  |          /
  v         v
Phase 6: Asmtolerant.v (faulty simulation proof)
    |
    v
Phase 7: Complements.v (top-level theorem + backend simulation composition)
    |
    v
Phase 8: Validation
```

Note: Phase 1 depends on Phase 2 for the `asm_coloring` type and `is_basic`. If these are factored into a shared module, Phases 1 and 2 can proceed in parallel.

Phase 0 unblocks all subsequent phases. Phase 2 (color spec) should come before Phase 1, since Phase 1 imports the `asm_coloring` type and `is_basic` from Phase 2. Alternatively, the `asm_coloring` type can be defined in a shared location (it is just `Z -> preg -> color`, where `color` is already in `RTLcolor.v`), which would allow Phases 1 and 2 to proceed in parallel. Phase 3 depends on Phase 2. Phases 4 and 5 depend on Phase 3. Phase 6 depends on Phases 1-3. Phase 7 depends on Phase 6. Phase 8 depends on Phase 7. The dependency structure is: Phase 0 → Phase 2 → {Phase 1, Phase 3} → {Phase 4, Phase 5} → Phase 6 → Phase 7 → Phase 8. (Phases 1 and 3 are independent and can proceed in parallel from Phase 2.)

---

## New Files Summary

| File | ~Lines | Description |
|------|--------|-------------|
| `riscV/Asmfault.v` | ~180 | Faulty RISC-V Asm semantics (incl. initial/final states) |
| `riscV/Asmcolor.v` | ~400-500 | Declarative color system for RISC-V Asm (168 instruction constructors) |
| `riscV/Asmcolorcheck.v` | ~800-1200 | Verified Boolean color checker for RISC-V Asm (168 instruction cases) |
| `riscV/Asminfercolor.ml` | ~400 | Unverified color inference oracle |
| `riscV/Asmtolerant.v` | ~3000-4000 | Faulty backward simulation proof |

## Modified Files Summary

| File | Changes |
|------|---------|
| `riscV/Asm.v` | Add `Section VOTE` parameterization; generalize `semantics_determinate` |
| `riscV/Asmgenproof.v` | Adapt to vote_type parameterization |
| `riscV/Asmgenproof1.v` | Adapt to vote_type parameterization |
| `riscV/SelectOpproof.v` | Adapt to vote_type parameterization (x86 counterpart has `Section VOTE`) |
| `riscV/SelectLongproof.v` | Adapt to vote_type parameterization (x86 counterpart has `Section VOTE`) |
| `driver/Complements.v` | Add `transf_c_program_preservation_faulty` + backend sim composition |
| `driver/Driver.ml` | Wire Asm color checker into pipeline |
| `extraction/extraction.v` | Add extraction for `Asmcolorcheck.infer_coloring` |
| `Makefile` / `_CoqProject` | Add new `.v` files |
| `Makefile.extr` | Add `Asminfercolor.ml` |

Note: `backend/Asmgenproof0.v` already has VOTE parameterization (line 787) and should not need changes.

---

## Risk Assessment

### High risk: Phase 6 (Asmtolerant.v)
The faulty simulation proof is the largest and most complex component. At RTL it is ~3267 lines. At Asm it will be similar or larger due to the expanded instruction set. Mitigation: heavy Ltac automation for the many instruction cases that follow the same pattern; develop the proof incrementally starting with arithmetic instructions.

### Medium risk: Phase 0 (vote_type parameterization)
Touching `Asm.v` and its dependents ripples through many files. `riscV/Asmgenproof.v` and `riscV/Asmgenproof1.v` do not currently have `Section VOTE` and will need parameterization. The generalization of `semantics_determinate` to the vote-parameterized version requires showing vote builtins are deterministic under both `Two` and `Three`. Mitigation: follow the x86 pattern exactly; provide backward-compatible wrappers.

### Medium risk: Phase 3 (Asmcolorcheck.v soundness proof)
The `check_col_instr_sound` lemma at RTL was already non-trivial. At Asm with 168 instruction constructors it will have many cases. Mitigation: structure the checker and proof around a small number of instruction categories (arithmetic, load, store, branch, builtin, pseudo) with shared helper lemmas.

### Medium risk: Register allocation feasibility
The Asm color checker may fail on TMR-compiled programs if the register allocator doesn't keep TMR copies separate. This would make the theorem vacuously true. Mitigation: empirical testing as early as possible — after Phase 0, manually inspect register assignments on TMR-compiled programs; after Phase 5, run the Asm color checker. Consider register allocator hints if needed.

### Medium risk: Phase 7 (backend simulation composition)
Composing 7 forward simulations at the `Three` instantiation and converting to a backward simulation is non-trivial glue. Each pass proof must work at the `Three` instantiation, and the factoring lemma must correctly decompose `transf_c_program`. Mitigation: follow the existing patterns (`transf_rtl_program_to_rtl'_forward_simulation`, `apply_partial_factor`) closely.

### Low risk: Phase 4 (Asminfercolor.ml)
This is unverified OCaml. Its correctness doesn't matter for the proof - only for whether the checker succeeds. Mitigation: test on representative programs.

---

## Recommended Implementation Order

1. **Phase 0** - Do first as it unblocks everything.
2. **Phase 2** - Color spec (defines `asm_coloring` type and color rules needed by Phase 1).
3. **Phase 1 + Phase 3** - Fault semantics and color checker (Phase 1 imports color types from Phase 2; Phase 3 needs Phase 2's color rules). Can proceed in parallel.
4. **Phase 4 + Phase 5** - Oracle and wiring (needs Phase 3). **Then immediately test** on TMR-compiled programs to validate register allocation feasibility.
5. **Phase 6** - Faulty simulation (the big one; needs Phases 1-3).
6. **Phase 7** - Top-level theorem + backend simulation composition (needs Phase 6).
7. **Phase 8** - Validation.

---

## Appendix: Asm Instruction Classification for Color System

Because `asm_zap_allowed` is coloring-dependent (see Phase 1), there is no longer a static "faultable vs. protected" classification of Asm instruction opcodes. Instead, an instruction is zappable iff its destination is basic-colored. The Appendix below classifies instructions by their **RTL origin** and the color the oracle should assign, for reference during implementation.

### Dual-use instructions (can be basic-colored OR White depending on RTL origin)

These Asm instruction constructors arise from both protected and unprotected RTL operations:

- **Psubl**: from `Onegl` (NOT protected, basic-colored) via `Psubl rd X0 rs`, AND from `Osubl` (protected when `Archi.ptr64 = true`) via `Psubl rd rs1 rs2`.
- **Pxoriw**: from `Oxorimm` (NOT protected, basic-colored), AND from protected `Ocmp (Ccomplu Cle/Cgt)` multi-instruction expansion (`Psltul; Pxoriw`).
- **Psltul**: from protected `Ocmp (Ccomplu _)` expansion (e.g., `transl_cond_int64u` generates `Psltul` for `Clt`, `Cle`, `Cgt`, `Cge`), AND from `sltuimm64` which may be used in non-protected contexts via `Asmgen.v`'s various comparison code generation paths. Note: `Pseqw`/`Psnew`/`Pseql`/`Psnel` are separate instruction constructors with their own `exec_instr` cases — they do NOT expand to `Psltul` at runtime.
- **Pmv** (integer move): from register-to-register copy of a basic-colored TMR value, OR from register allocation inserting a copy of a White value (e.g., function return value, address).
- **Pfmv** (float move): same dual-use pattern as `Pmv` for float registers.
The coloring-dependent `asm_zap_allowed` handles these naturally: the oracle assigns colors based on compilation context, and the checker validates consistency.

### Always basic-colored when generated (from unprotected RTL operations only)

Integer register-register: Paddw, Psubw, Pmulw, Pmulhw, Pmulhuw, Pandw, Porw, Pxorw, Paddl, Pmull, Pmulhl, Pmulhul, Pandl, Porl, Pxorl, Pseqw, Psnew, Pseql, Psnel, Pcvtl2w, Pcvtw2l

Integer register-immediate: Paddiw, Pandiw, Poriw, Pluiw, Paddil, Pandil, Poril, Pxoril, Pluil

Immediate-amount shifts: Pslliw, Psrliw, Psraiw, Psllil, Psrlil, Psrail (from `Oshlimm`, `Oshrimm`, `Oshruimm`, `Oshllimm`, `Oshrlimm`, `Oshrluimm` — these are NOT in `is_protected` because the shift amount is a compile-time constant that cannot be corrupted)

Integer comparisons (non-pointer): Psltw, Psltuw, Psltl, Psltiw, Psltiuw, Psltil

Float arithmetic: Pfadds, Pfsubs, Pfmuls, Pfaddd, Pfsubd, Pfmuld, Pfnegs, Pfabss, Pfnegd, Pfabsd, Pfcvtds, Pfcvtsd

Float division: Pfdivs, Pfdivd (NOTE: `Odivf`/`Odivfs` are NOT in `is_protected` — float division always produces valid results)

Float comparisons: Pfeqs, Pflts, Pfles, Pfeqd, Pfltd, Pfled (NOTE: `Ocmp (Ccompf _)` and `Ocmp (Ccompfs _)` are NOT in `is_protected`)

Int-to-float conversions: Pfcvtsw, Pfcvtswu, Pfcvtdw, Pfcvtdwu, Pfcvtsl, Pfcvtslu, Pfcvtdl, Pfcvtdlu (always well-defined)

Unsigned float-to-int conversions: Pfcvtwus, Pfcvtlus, Pfcvtwud, Pfcvtlud (not in `is_protected`; NaN/out-of-range inputs are handled by `Val.maketotal`, which returns `Vundef` rather than causing `Stuck`, and `Vundef` propagates correctly via `Val.lessdef` in the proof)

### Always White when generated (from protected RTL operations only)

Integer division/remainder: Pdivw, Pdivuw, Premw, Premuw, Pdivl, Pdivul, Preml, Premul (from `Odiv`, `Odivu`, `Omod`, `Omodu`, `Odivl`, `Odivlu`, `Omodl`, `Omodlu`)

Register-amount shifts: Psllw, Psrlw, Psraw, Pslll, Psrll, Psral (from `Oshl`, `Oshr`, `Oshru`, `Oshll`, `Oshrl`, `Oshrlu` — these are in `is_protected` because a corrupted shift amount could cause UB)

Signed float-to-int conversions: Pfcvtws, Pfcvtwd, Pfcvtls, Pfcvtld (from `Ointofsingle`, `Ointoffloat`, `Olongofsingle`, `Olongoffloat` — only these 4 are in `is_protected`)

Conditional select: Pcsel (from `Osel`). Note: `exec_instr` for `Pcsel` returns `Vundef` (not `Stuck`) when the condition register is neither `Vone` nor `Vzero` (`riscV/Asm.v:623-627`). The "always White" classification is essential for correctness: if `Pcsel`'s destination were basic-colored and zapped, the condition register mismatch between source and target could cause divergent value selection, breaking the simulation. Since Pcsel is always White, its inputs match exactly and the `Vundef` fallback never causes a problem.

### Always White destination (never zappable due to White coloring)

Loads: Plb, Plbu, Plh, Plhu, Plw, Plw_a, Pld, Pld_a, Pfls, Pfld, Pfld_a (destination register `rd` is White; address register must be White)

Pseudo-instructions with data register destinations: Pallocframe (modifies X30 and SP, both White), Pfreeframe (modifies SP, White), Ploadsymbol (destination `rd` White), Ploadsymbol_high (destination `rd` White), Ploadli (destination `rd` White), Ploadfi (destination `rd` White), Ploadsi (destination `rd` White)

### No destination data register (never zappable regardless of coloring)

Stores: Psb, Psh, Psw, Psw_a, Psd, Psd_a, Pfss, Pfsd, Pfsd_a

Branches: Pbeqw, Pbnew, Pbltw, Pbltuw, Pbgew, Pbgeuw, Pbeql, Pbnel, Pbltl, Pbltul, Pbgel, Pbgeul

Jumps: Pj_l, Pj_s, Pj_r, Pjal_s, Pjal_r (note: Pjal_s/Pjal_r write to RA/X1, but RA is excluded by `data_preg`)

Labels/debug: Plabel, Pcfi_rel_offset (these are modeled as no-ops: `Next (nextinstr rs) m`)

Jump table: Pbtbl (sets PC and clobbers both X31 and X5; X31 is not a data register per `data_preg`, but X5 IS a data register). `dests_of_instr (Pbtbl _ _) = [IR X5]`. X5 must be White at all positions, so `asm_zap_allowed` is False (since `is_basic White = false`). The color checker must verify X5 is White. The use of `col (pos + 1)` in `asm_zap_allowed` is harmless here because the lookup never reaches `is_basic` on a True branch (see note in Phase 1)

Builtins: Pbuiltin (all variants) — builtins DO have destination registers (the `res` field), but are never zappable because `asm_fstep_builtin` bypasses `asm_maybe_zap`. Their destinations are White (or Red/Green/Blue for votes/smoves, handled by specific color rules).

### Not generated by `riscV/Asmgen.v` (unmodeled — `exec_instr` returns `Stuck`)

Float min/max: Pfmins, Pfmaxs, Pfmind, Pfmaxd

Float square root: Pfsqrts, Pfsqrtd (no `Osqrt` in `riscV/Op.v`)

Fused multiply-add: Pfmadds, Pfmsubs, Pfnmadds, Pfnmsubs, Pfmaddd, Pfmsubd, Pfnmaddd, Pfnmsubd

FP/integer register moves: Pfmvxs, Pfmvsx, Pfmvxd, Pfmvdx

Other unmodeled: Pcfi_adjust, Pfence, Pnop

These all return `Stuck` in `exec_instr` and should never appear in code generated by `Asmgen`. They can be classified as White for completeness. Note: `Pcfi_rel_offset` IS modeled (as a no-op: `Next (nextinstr rs) m`) and appears under "No destination data register" above, while `Pcfi_adjust` is unmodeled.

*Note on pointer comparisons: On 64-bit RISC-V (`Archi.ptr64 = true`), `Ocmp (Ccomplu _)` and `Ocmp (Ccompluimm _ _)` are protected. These expand to multi-instruction sequences using `Psltul`, `Psltiul`, `Pxoriw`, etc. The coloring-dependent design handles this: the oracle assigns White to all destinations in the expansion, making none of them zappable.*
