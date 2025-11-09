Require Import
  AST
  Builtins2
  Coqlib
  Events
  Globalenvs
  Integers
  Maps
  Memory
  Op
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

(* Inductive val_compat : val -> val -> Prop := *)
(* | val_compat_undef : forall v, val_compat Vundef v *)
(* | val_compat_int : forall i j, val_compat (Vint i) (Vint j) *)
(* | val_compat_long : forall i j, val_compat (Vlong i) (Vlong j) *)
(* | val_compat_float : forall x y, val_compat (Vfloat x) (Vfloat y) *)
(* | val_compat_single : forall x y, val_compat (Vsingle x) (Vsingle y) *)
(* | val_compat_ptr : forall b1 b2 ofs1 ofs2, val_compat (Vptr b1 ofs1) (Vptr b2 ofs2). *)

(* Lemma val_compat_refl (v : val) : *)
(*   val_compat v v. *)
(* Proof. destruct v; constructor. Qed. *)

(* Lemma val_compat_trans (v1 v2 v3 : val) : *)
(*   val_compat v1 v2 -> *)
(*   val_compat v2 v3 -> *)
(*   val_compat v1 v3. *)
(* Proof. *)
(*   intros H1 H2. *)
(*   inversion H1; inversion H2; subst; try solve [constructor]; congruence. *)
(* Qed. *)

(* Lemma val_lessdef_compat (v1 v2 : val) : *)
(*   Val.lessdef v1 v2 -> *)
(*   val_compat v1 v2. *)
(* Proof. *)
(*   intro H; inversion H; subst; try constructor. *)
(*   apply val_compat_refl. *)
(* Qed. *)

(* Technically we could/should allow faults (and not vote on) on most
   builtins, just not external function calls or votes themselves. *)
Definition zap_allowed (i : instruction) : Prop :=
  match i with
  | Iload _ _ _ _ _ => False
  | Istore _ _ _ _ _ => False
  | Icall _ _ _ _ _ => False
  | Itailcall _ _ _ => False
  | Ibuiltin _ _ _ _ => False
  | _ => True
  end.

(* NOTE: with the backward simulation approach (and fstep using
   3-voting semantics when a fault hasn't occurred yet), we should be
   able to use exact matching of register contents (of unfaulted
   colors) instead of Val.lessdef. *)

Inductive maybe_zap : RTL.state -> RTL.state -> bool -> Prop :=
| maybe_zap_refl : forall s, maybe_zap s s false
| maybe_zap_reg : forall stk f sp pc rs m v i r,
    (* val_compat (rs # r) v -> *)
    f.(fn_code) ! pc = Some i ->
    zap_allowed i ->
    res_of_instruction i = Some r ->
    maybe_zap (State stk f sp pc rs m) (State stk f sp pc (rs # r <- v) m) true.

Section RELSEM.
Variable ge: genv.

(* Use 3-vote semantics until a fault has occurred, then switch to
   2-vote semantics. Can do this on a per-function basis if we
   generalize to one fault per function. *)
Inductive fstep : fstate -> trace -> fstate -> Prop :=
| fstep_step_not_zapped : forall s t s' s'' b
    (STEP: @RTL.step Builtins2.Three Builtins2.VoteSemantics_Three ge s t s')
    (ZAP: maybe_zap s' s'' b),
    fstep {| fs_state := s; fault := false |} t {| fs_state := s''; fault := b |}
| fstep_step_zapped : forall s t s'
    (STEP: @RTL.step Builtins2.Two Builtins2.VoteSemantics_Two ge s t s'),
    fstep {| fs_state := s; fault := true |} t {| fs_state := s'; fault := true |}.

Inductive initial_state (p : program) : fstate -> Prop :=
| initial_state_intro : forall s,
    RTL.initial_state p s ->
    initial_state p {| fs_state := s; fault := false |}.

Definition final_state (s : fstate) (r : int) : Prop :=
  RTL.final_state s.(fs_state) r.

End RELSEM.

Definition faulty_semantics (p : program) :=
  Semantics fstep (initial_state p) final_state (Genv.globalenv p).
