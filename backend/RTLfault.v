Require Import
  Events
  Globalenvs
  Integers
  (* List *)
  Registers
  RTL
  Smallstep
  Values
.
(* Import ListNotations. *)

Record fstate : Type :=
  mkfstate { fs_state : RTL.state
           ; fault : bool }.

Inductive val_compat : val -> val -> Prop :=
| val_compat_undef : forall v, val_compat Vundef v
| val_compat_int : forall i j, val_compat (Vint i) (Vint j)
| val_compat_long : forall i j, val_compat (Vlong i) (Vlong j)
| val_compat_float : forall x y, val_compat (Vfloat x) (Vfloat y)
| val_compat_single : forall x y, val_compat (Vsingle x) (Vsingle y)
| val_compat_ptr : forall b1 b2 ofs1 ofs2, val_compat (Vptr b1 ofs1) (Vptr b2 ofs2).

Lemma val_compat_refl (v : val) :
  val_compat v v.
Proof. destruct v; constructor. Qed.

Lemma val_lessdef_compat (v1 v2 : val) :
  Val.lessdef v1 v2 ->
  val_compat v1 v2.
Proof.
  intro H; inversion H; subst; try constructor.
  apply val_compat_refl.
Qed.

(* Inductive zap : RTL.state -> RTL.state -> Prop := *)
(* | zap_reg : forall stk f sp pc rs m r v, *)
(*     val_compat (rs # r) v -> *)
(*     zap (State stk f sp pc rs m) (State stk f sp pc (rs # r <- v) m). *)

(* (* TODO: may need to do this the way Dave did in the other faulty *)
(*    semantics, where there's a single step rule with a maybe_fault *)
(*    condition. That way, a single step in this semantics always *)
(*    coincides with a single step in the nonfaulty semantics. *) *)
(* Inductive fstep (ge : genv) : fstate -> trace -> fstate -> Prop := *)
(* | fstep_step : forall s t s' b, *)
(*     RTL.step ge s t s' -> *)
(*     fstep ge (mkfstate s b) t (mkfstate s' b) *)
(* | fstep_zap : forall s s', *)
(*     zap s s' -> *)
(*     fstep ge (mkfstate s false) E0 (mkfstate s' true). *)

Definition zap_allowed (i : instruction) : Prop :=
  match i with
  | Iload _ _ _ _ _ => False
  | Istore _ _ _ _ _ => False
  | Icall _ _ _ _ _ => False
  | Itailcall _ _ _ => False
  | Ibuiltin _ _ _ _ => False
  | _ => True
  end.

Inductive maybe_zap : RTL.state -> bool -> RTL.state -> bool -> Prop :=
| maybe_zap_refl : forall s b,
    maybe_zap s b s b
| maybe_zap_reg : forall stk f sp pc rs m r v,
    val_compat (rs # r) v ->
    maybe_zap (State stk f sp pc rs m) false (State stk f sp pc (rs # r <- v) m) true.

Inductive fstep (ge : genv) : fstate -> trace -> fstate -> Prop :=
| fstep_step :
  forall s b t s' b' s''
    (STEP: RTL.step ge s t s')
    (ZAP: maybe_zap s' b s'' b'),
    fstep ge {| fs_state := s; fault := b |} t {| fs_state := s''; fault := b'|}.

Inductive initial_state (p : program) : fstate -> Prop :=
| initial_state_intro : forall s,
    RTL.initial_state p s ->
    initial_state p {| fs_state := s; fault := false |}.

Definition final_state (s : fstate) (r : int) : Prop :=
  RTL.final_state s.(fs_state) r.

Definition faulty_semantics (p : program) :=
  Semantics fstep (initial_state p) final_state (Genv.globalenv p).
