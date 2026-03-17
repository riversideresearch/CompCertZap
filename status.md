# RTLtolerant.v Status

## Current State

Branch: `improve-builtins-tmr`

`step_simulation` in RTLtolerant.v is fully proved (Qed). No `Admitted` proofs remain in the project. The full chain builds: RTLtolerant.vo, RTLtmrproof.vo, Complements.vo.

## Changes Made

1. **`common/Builtins.v`**: shifts (`BI_i64_shl/shr/sar`) set to `false` in `builtin_can_replicate_bf` (needed because `val_compat` of shift results is unprovable when the shift amount is faulted).

2. **`backend/RTLcolor.v`**: strengthened `wc_Ibuiltin_safe` frame condition — removed the arg-register exclusion (`~ Exists (in_builtin_arg r) bargs ->`), so all non-res live registers preserve their color. This matches `wc_Iop_safe` and is necessary for the faulted match_rs proof (arg registers must have stable colors to carry Val.lessdef across instructions).

3. **`backend/RTLcolorcheck.v`**: updated the Boolean checker for safe builtins to match the strengthened wc condition (removed `existsb (in_builtin_argb r) bargs ||` from the for_all check).

4. **`backend/RTLtolerant.v`**:
   - Added `safe_external_call_val_compat` lemma: lifts `builtin_sem_val_compat` to the `external_call` level.
   - Proved the faulted safe-builtin case of `step_simulation` (previously `admit`).
   - Changed `Admitted` to `Qed`.

## Next Steps

None for the proof — the TMR backward simulation is complete. Future work could re-add shifts to `builtin_can_replicate_bf` with a refined coloring rule that separates shift-amount register colors.
