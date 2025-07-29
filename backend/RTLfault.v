Require Import
  Events
  (* List *)
  Registers
  RTL
  Smallstep
  Values
.
(* Import ListNotations. *)

Record fstate : Type := mkfstate {
  fs_state: RTL.state
; fault: bool
}.

Inductive val_compat : val -> val -> Prop :=
| val_compat_undef : val_compat Vundef Vundef
| val_compat_int : forall i j, val_compat (Vint i) (Vint j)
| val_compat_long : forall i j, val_compat (Vlong i) (Vlong j)
| val_compat_float : forall x y, val_compat (Vfloat x) (Vfloat y)
| val_compat_single : forall x y, val_compat (Vsingle x) (Vsingle y)
| val_compat_ptr : forall b1 b2 ofs1 ofs2, val_compat (Vptr b1 ofs1) (Vptr b2 ofs2).

Inductive zap : RTL.state -> RTL.state -> Prop :=
| zap_reg : forall stk f sp pc rs m r v,
    val_compat (rs # r) v ->
    zap (State stk f sp pc rs m) (State stk f sp pc (rs # r <- v) m).

(* TODO: may need to do this the way Dave did in the other faulty
   semantics, where there's a single step rule with a maybe_fault
   condition. That way, a single step in this semantics always
   coincides with a single step in the nonfaulty semantics. *)
Inductive fstep (ge : genv) : fstate -> trace -> fstate -> Prop :=
| fstep_step : forall s t s' b,
    RTL.step ge s t s' ->
    fstep ge (mkfstate s b) t (mkfstate s' b)
| fstep_zap : forall s s',
    zap s s' ->
    fstep ge (mkfstate s false) E0 (mkfstate s' true).
