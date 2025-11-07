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

Lemma val_compat_trans (v1 v2 v3 : val) :
  val_compat v1 v2 ->
  val_compat v2 v3 ->
  val_compat v1 v3.
Proof.
  intros H1 H2.
  inversion H1; inversion H2; subst; try solve [constructor]; congruence.
Qed.

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

(* Technically we could/should allow faults (and not vote on) on most
   builtins, just not external function calls. *)
Definition zap_allowed (i : instruction) : Prop :=
  match i with
  | Iload _ _ _ _ _ => False
  | Istore _ _ _ _ _ => False
  | Icall _ _ _ _ _ => False
  | Itailcall _ _ _ => False
  | Ibuiltin _ _ _ _ => False
  | _ => True
  end.

(* Should this just fault the result register of the current *)
(*    instruction? That would let us allow faults on smoves, for *)
(*    example. *)
Inductive maybe_zap : RTL.state -> bool -> RTL.state -> bool -> Prop :=
| maybe_zap_refl : forall s b,
    maybe_zap s b s b
| maybe_zap_reg : forall stk f sp pc rs m r v,
    val_compat (rs # r) v ->
    maybe_zap (State stk f sp pc rs m) false (State stk f sp pc (rs # r <- v) m) true.

Section RELSEM.
Variable ge: genv.

Definition find_function
      (ros: reg + ident) (rs: regset) : option fundef :=
  match ros with
  | inl r => Genv.find_funct ge rs#r
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

(** Copy/paste of RTL.step except 1) exec_Iop makes eval_operation
    total so we don't get stuck when arguments don't have the right
    constructors (e.g., non-int arguments to division), and 2)
    specialized to 2-voting. *)
Inductive step: RTL.state -> trace -> RTL.state -> Prop :=
  | exec_Inop:
      forall s f sp pc rs m pc',
      (fn_code f)!pc = Some(Inop pc') ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' rs m)
  | exec_Iop:
      forall s f sp pc rs m op args res pc' v,
      (fn_code f)!pc = Some(Iop op args res pc') ->
      v = Val.maketotal (eval_operation ge sp op rs##args m) ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' (rs#res <- v) m)
  | exec_Iload:
      forall s f sp pc rs m chunk addr args dst pc' a v,
      (fn_code f)!pc = Some(Iload chunk addr args dst pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' (rs#dst <- v) m)
  | exec_Istore:
      forall s f sp pc rs m chunk addr args src pc' a m',
      (fn_code f)!pc = Some(Istore chunk addr args src pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a rs#src = Some m' ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' rs m')
  | exec_Icall:
      forall s f sp pc rs m sig ros args res pc' fd,
      (fn_code f)!pc = Some(Icall sig ros args res pc') ->
      find_function ros rs = Some fd ->
      funsig fd = sig ->
      step (State s f sp pc rs m)
        E0 (Callstate (Stackframe res f sp pc' rs :: s) fd rs##args m)
  | exec_Itailcall:
      forall s f stk pc rs m sig ros args fd m',
      (fn_code f)!pc = Some(Itailcall sig ros args) ->
      find_function ros rs = Some fd ->
      funsig fd = sig ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (State s f (Vptr stk Ptrofs.zero) pc rs m)
        E0 (Callstate s fd rs##args m')
  | exec_Ibuiltin:
      forall s f sp pc rs m ef args res pc' vargs t vres m',
      (fn_code f)!pc = Some(Ibuiltin ef args res pc') ->
      eval_builtin_args ge (fun r => rs#r) sp m args vargs ->
      @external_call Two VoteSemantics_Two ef ge vargs m t vres m' ->
      step (State s f sp pc rs m)
         t (State s f sp pc' (regmap_setres res vres rs) m')
  | exec_Icond:
      forall s f sp pc rs m cond args ifso ifnot b pc',
      (fn_code f)!pc = Some(Icond cond args ifso ifnot) ->
      eval_condition cond rs##args m = Some b ->
      pc' = (if b then ifso else ifnot) ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' rs m)
  | exec_Ijumptable:
      forall s f sp pc rs m arg tbl n pc',
      (fn_code f)!pc = Some(Ijumptable arg tbl) ->
      rs#arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some pc' ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' rs m)
  | exec_Ireturn:
      forall s f stk pc rs m or m',
      (fn_code f)!pc = Some(Ireturn or) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (State s f (Vptr stk Ptrofs.zero) pc rs m)
        E0 (Returnstate s (regmap_optget or Vundef rs) m')
  | exec_function_internal:
      forall s f args m m' stk,
      Val.has_argtype_list args f.(fn_sig).(sig_args) ->
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      step (Callstate s (Internal f) args m)
        E0 (State s
                  f
                  (Vptr stk Ptrofs.zero)
                  f.(fn_entrypoint)
                  (init_regs args f.(fn_params))
                  m')
  | exec_function_external:
      forall s ef args res t m m',
      @external_call Two VoteSemantics_Two ef ge args m t res m' ->
      step (Callstate s (External ef) args m)
         t (Returnstate s res m')
  | exec_return:
      forall res f sp pc rs s vres m,
      step (Returnstate (Stackframe res f sp pc rs :: s) vres m)
        E0 (State s f sp pc (rs#res <- vres) m).

Inductive fstep : fstate -> trace -> fstate -> Prop :=
| fstep_step :
  forall s b t s' b' s''
    (STEP: step s t s')
    (ZAP: maybe_zap s' b s'' b'),
    fstep {| fs_state := s; fault := b |} t {| fs_state := s''; fault := b'|}.

(* Inductive fstep (ge : genv) : fstate -> trace -> fstate -> Prop := *)
(* | fstep_zap : forall stk f sp pc rs m r v t *)
(*   (COMPAT: val_compat (rs # r) v), *)
(*     fstep ge {| fs_state := State stk f sp pc rs m; fault := false |} t *)
(*              {| fs_state := State stk f sp pc (rs # r <- v) m; fault := true |} *)
(* | fstep_step : forall s b t s' *)
(*   (STEP: @RTL.step Builtins2.Two Builtins2.VoteSemantics_Two ge s t s'), *)
(*     fstep ge {| fs_state := s; fault := b |} t {| fs_state := s'; fault := b|}. *)

Inductive initial_state (p : program) : fstate -> Prop :=
| initial_state_intro : forall s,
    RTL.initial_state p s ->
    initial_state p {| fs_state := s; fault := false |}.

Definition final_state (s : fstate) (r : int) : Prop :=
  RTL.final_state s.(fs_state) r.

End RELSEM.

Definition faulty_semantics (p : program) :=
  Semantics fstep (initial_state p) final_state (Genv.globalenv p).



(* dec 4 2:20pm with espinoza *)
(* beavercreek 2365 lakeview dr *)
