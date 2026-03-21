Require Import
  AST
  Builtins
  FaultPolicy
  CompCertZapUtils
  Builtins2
  Coqlib
  Events
  Globalenvs
  Integers
  Maps
  Memory
  Op
  Registers
  RTL
  Smallstep
  Values
.

Record fstate : Type :=
  mkfstate { fs_state : RTL.state
           ; fault : bool }.


(* Technically we could/should allow faults (and not vote on) on most
   builtins, just not external function calls or votes themselves. *)
Definition zap_allowed (i : instruction) : Prop :=
  match i with
  | Iop op _ _ _ => ~ is_protected op
  | Iload _ _ _ _ _ => False
  | Istore _ _ _ _ _ => False
  | Icall _ _ _ _ _ => False
  | Itailcall _ _ _ => False
  | Ibuiltin ef _ _ _ => builtin_can_fault ef = true
  | _ => True
  end.

Inductive maybe_zap (f : function) (pc : node)
  : RTL.state -> bool -> RTL.state -> bool -> Prop :=
| maybe_zap_refl : forall s b, maybe_zap f pc s b s b
| maybe_zap_reg : forall stk sp pc' rs m i r v,
    val_compat (rs # r) v ->
    f.(fn_code) ! pc = Some i ->
    zap_allowed i ->
    res_of_instruction i = Some r ->
    maybe_zap f pc
      (State stk f sp pc' rs m) false
      (State stk f sp pc' (rs # r <- v) m) true.

Section RELSEM.
Variable ge: genv.

Inductive not_regular_state : RTL.state -> Prop :=
| not_regular_state_Callstate : forall stk f args m,
    not_regular_state (Callstate stk f args m)
| not_regular_state_Returnstate : forall stk v m,
    not_regular_state (Returnstate stk v m).

Inductive fstep : fstate -> trace -> fstate -> Prop :=
| fstep_step_State : forall stk f sp pc rs m t s' s'' b b'
    (STEP: @RTL.step Builtins2.Two Builtins2.VoteSemantics_Two ge
             (State stk f sp pc rs m) t s')
    (ZAP: maybe_zap f pc s' b s'' b'),
    fstep
      {| fs_state := State stk f sp pc rs m; fault := b |}
      t
      {| fs_state := s''; fault := b' |}
| fstep_step_other : forall s t s' b
    (HS: not_regular_state s)
    (STEP: @RTL.step Builtins2.Two Builtins2.VoteSemantics_Two ge s t s'),
    fstep {| fs_state := s; fault := b |} t {| fs_state := s'; fault := b |}.

Inductive initial_state (p : program) : fstate -> Prop :=
| initial_state_intro : forall s,
    RTL.initial_state p s ->
    initial_state p {| fs_state := s; fault := false |}.

Definition final_state (s : fstate) (r : int) : Prop :=
  RTL.final_state s.(fs_state) r.

End RELSEM.

Definition faulty_semantics (p : program) :=
  Semantics fstep (initial_state p) final_state (Genv.globalenv p).


(** * val_compat monotonicity for safe builtins *)

(** Helper: [val_compat] is preserved through [proj_num] and [inj_num].
    For a [mkbuiltin_nNt] builtin, arguments are extracted via [proj_num]
    (which returns a default when the value constructor doesn't match the
    expected type), a pure function is applied, and the result is wrapped
    via [inj_num].  Under [val_compat], inputs of the same constructor
    produce same-constructor outputs. *)

Lemma val_compat_proj_num_inj (targ: typ) (tres: xtype)
      (f1 f2: valty targ -> valxty tres) (v1 v2: val) :
  val_compat v1 v2 ->
  val_compat
    (proj_num targ Vundef v1 (fun x => inj_num tres (f1 x)))
    (proj_num targ Vundef v2 (fun x => inj_num tres (f2 x))).
Proof.
  intros Hcompat; inv Hcompat; destruct targ; simpl; try constructor;
    destruct tres; simpl; try constructor.
Qed.

(** ** Per-class lemmas for mkbuiltin_n1t builtins *)

Lemma val_compat_mkbuiltin_n1t
      (targ: typ) (tres: xtype) (f: valty targ -> valxty tres)
      (vargs1 vargs2: list val) (vres1: val) :
  Forall2 val_compat vargs1 vargs2 ->
  mkbuiltin_n1t targ tres f vargs1 = Some vres1 ->
  exists vres2,
    mkbuiltin_n1t targ tres f vargs2 = Some vres2 /\
    val_compat vres1 vres2.
Proof.
  intros Hcompat Hsem.
  simpl in *.
  destruct vargs1 as [|v1 [|]]; try discriminate.
  inv Hcompat. inv H3. inv Hsem.
  eexists; split; [reflexivity|].
  apply val_compat_proj_num_inj; auto.
Qed.

(** Helper: [val_compat] through nested [proj_num]/[inj_num] for 2-arg
    numerical builtins. *)

Lemma val_compat_proj_num_inj2 (targ1 targ2: typ) (tres: xtype)
      (f1 f2: valty targ1 -> valty targ2 -> valxty tres) (v1 v2 w1 w2: val) :
  val_compat v1 v2 ->
  val_compat w1 w2 ->
  val_compat
    (proj_num targ1 Vundef v1 (fun x1 =>
     proj_num targ2 Vundef w1 (fun x2 => inj_num tres (f1 x1 x2))))
    (proj_num targ1 Vundef v2 (fun x1 =>
     proj_num targ2 Vundef w2 (fun x2 => inj_num tres (f2 x1 x2)))).
Proof.
  intros Hv Hw; inv Hv; destruct targ1; simpl; try constructor;
    apply val_compat_proj_num_inj; auto.
Qed.

Lemma val_compat_mkbuiltin_n2t
      (targ1 targ2: typ) (tres: xtype)
      (f: valty targ1 -> valty targ2 -> valxty tres)
      (vargs1 vargs2: list val) (vres1: val) :
  Forall2 val_compat vargs1 vargs2 ->
  mkbuiltin_n2t targ1 targ2 tres f vargs1 = Some vres1 ->
  exists vres2,
    mkbuiltin_n2t targ1 targ2 tres f vargs2 = Some vres2 /\
    val_compat vres1 vres2.
Proof.
  intros Hcompat Hsem.
  simpl in *.
  destruct vargs1 as [|v1 [|w1 [|]]]; try discriminate.
  inv Hcompat. inv H3.
  match goal with H : Forall2 _ nil _ |- _ => inv H end.
  inv Hsem.
  eexists; split; [reflexivity|].
  apply val_compat_proj_num_inj2; auto.
Qed.

(** ** val_compat lemmas for mkbuiltin_v2t builtins *)

(** [Val.mull'] takes [Vint * Vint -> Vlong], otherwise [Vundef].
    Under [val_compat], both sides either produce [Vlong] or [Vundef]. *)

Lemma val_compat_mull' v1 v1' v2 v2' :
  val_compat v1 v1' ->
  val_compat v2 v2' ->
  val_compat (Val.mull' v1 v2) (Val.mull' v1' v2').
Proof.
  intros H0 H1; inv H0; inv H1; simpl; constructor.
Qed.

(** Generic tactic for 2-arg v2t builtin val_compat proofs *)

Local Ltac solve_v2t_builtin vc_lemma :=
  let Hcompat := fresh "Hcompat" in
  let Hsem := fresh "Hsem" in
  intros Hcompat Hsem;
  simpl in *;
  destruct Hcompat as [| ? ? ? ? ? Hcompat]; [discriminate|];
  destruct Hcompat as [| ? ? ? ? ? Hcompat]; [discriminate|];
  destruct Hcompat; [|discriminate];
  inv Hsem;
  eexists; split; [reflexivity|];
  eapply vc_lemma; eassumption.

(** Lifting [val_compat_addl] to the builtin semantics wrapper. *)

Lemma builtin_sem_val_compat_addl vargs1 vargs2 vres1 :
  Forall2 val_compat vargs1 vargs2 ->
  standard_builtin_sem BI_addl vargs1 = Some vres1 ->
  exists vres2,
    standard_builtin_sem BI_addl vargs2 = Some vres2 /\
    val_compat vres1 vres2.
Proof. solve_v2t_builtin val_compat_addl. Qed.

(** Lifting [val_compat_mull'] to the builtin semantics wrapper. *)

Lemma builtin_sem_val_compat_mull vargs1 vargs2 vres1 :
  Forall2 val_compat vargs1 vargs2 ->
  standard_builtin_sem BI_mull vargs1 = Some vres1 ->
  exists vres2,
    standard_builtin_sem BI_mull vargs2 = Some vres2 /\
    val_compat vres1 vres2.
Proof. solve_v2t_builtin val_compat_mull'. Qed.

(** Lifting [val_compat_subl] to the builtin semantics wrapper.
    Requires [Archi.ptr64 = false] because [BI_subl] is only classified
    as replicable when [negb Archi.ptr64 = true] (CLAS-07). *)

Lemma builtin_sem_val_compat_subl vargs1 vargs2 vres1 :
  Archi.ptr64 = false ->
  Forall2 val_compat vargs1 vargs2 ->
  standard_builtin_sem BI_subl vargs1 = Some vres1 ->
  exists vres2,
    standard_builtin_sem BI_subl vargs2 = Some vres2 /\
    val_compat vres1 vres2.
Proof.
  intros Harchi. solve_v2t_builtin val_compat_subl.
Qed.

(** ** Shift builtins: restricted val_compat lemmas *)

(** IMPORTANT: The general val_compat monotonicity does NOT hold for shift
    builtins (BI_i64_shl, BI_i64_shr, BI_i64_sar) when the shift amount
    is faulted.  The issue is that [Int.ltu n2 Int64.iwordsize'] may
    succeed on one side and fail on the other, producing [Vlong] on one side
    and [Vundef] on the other.  Since [val_compat (Vlong _) Vundef] is NOT
    a constructor of [val_compat], the proof does not close.

    We provide restricted lemmas for the case where the shift amount is
    identical on both sides (the [val_compat_shll_imm] pattern).  The general
    case is left as a documented limitation -- the tolerant proof (Phase 3)
    may only encounter shifts where the shift amount register is not the
    faulted register, in which case the restricted lemma suffices. *)

(** Demonstration that the general shift proof does not close.
    The stuck goal is [val_compat (Vlong _) Vundef] when [Int.ltu]
    succeeds on the left (non-faulted) and fails on the right (faulted).
    We simply state that this lemma is NOT provable in general and abort. *)
Lemma builtin_sem_val_compat_shl_UNPROVABLE vargs1 vargs2 vres1 :
  Forall2 val_compat vargs1 vargs2 ->
  standard_builtin_sem BI_i64_shl vargs1 = Some vres1 ->
  exists vres2,
    standard_builtin_sem BI_i64_shl vargs2 = Some vres2 /\
    val_compat vres1 vres2.
Proof.
  (* Proof cannot be completed: when both args are Vlong/Vint with
     val_compat, Int.ltu may diverge between the two sides, producing
     Vlong on the left and Vundef on the right.  val_compat (Vlong _) Vundef
     is not a constructor of val_compat. *)
Abort.

(** The general proof for shifts cannot be completed.
    Instead, provide the restricted form where the shift amount
    is known to be the same on both sides. *)

Lemma builtin_sem_val_compat_shl_restricted v1 v1' n vres1 :
  val_compat v1 v1' ->
  standard_builtin_sem BI_i64_shl (v1 :: Vint n :: nil) = Some vres1 ->
  exists vres2,
    standard_builtin_sem BI_i64_shl (v1' :: Vint n :: nil) = Some vres2 /\
    val_compat vres1 vres2.
Proof.
  intros Hcompat Hsem.
  simpl in *. inv Hsem.
  eexists; split; [reflexivity|].
  apply val_compat_shll_imm; auto.
Qed.

Lemma builtin_sem_val_compat_shr_restricted v1 v1' n vres1 :
  val_compat v1 v1' ->
  standard_builtin_sem BI_i64_shr (v1 :: Vint n :: nil) = Some vres1 ->
  exists vres2,
    standard_builtin_sem BI_i64_shr (v1' :: Vint n :: nil) = Some vres2 /\
    val_compat vres1 vres2.
Proof.
  intros Hcompat Hsem.
  simpl in *. inv Hsem.
  eexists; split; [reflexivity|].
  apply val_compat_shrlu_imm; auto.
Qed.

Lemma builtin_sem_val_compat_sar_restricted v1 v1' n vres1 :
  val_compat v1 v1' ->
  standard_builtin_sem BI_i64_sar (v1 :: Vint n :: nil) = Some vres1 ->
  exists vres2,
    standard_builtin_sem BI_i64_sar (v1' :: Vint n :: nil) = Some vres2 /\
    val_compat vres1 vres2.
Proof.
  intros Hcompat Hsem.
  simpl in *. inv Hsem.
  eexists; split; [reflexivity|].
  apply val_compat_shrl_imm; auto.
Qed.

(** ** Unified builtin_sem_val_compat dispatcher *)

(** The unified dispatcher is gated by [builtin_can_replicate_bf bf = true].
    For shift builtins, we prove the property using a different technique:
    since [mkbuiltin_v2t] always returns [Some] for 2-argument inputs,
    we know both sides produce [Some].  For the val_compat of the results,
    we observe that shifts with faulted shift amounts can produce
    incompatible results.  However, the proof for shifts CAN be completed
    by case-splitting on all combinations of [val_compat] constructors
    and all [Int.ltu] outcomes.  Let us attempt the full proof.

    Key insight: when both arguments are NOT of the expected type
    (e.g., not Vlong/Vint), both sides produce Vundef, which IS val_compat.
    The problematic case is ONLY when one side's ltu succeeds and the other
    fails.  But since val_compat_undef says val_compat Vundef v (Vundef on
    LEFT), we can handle the case where the LEFT side's ltu FAILS (producing
    Vundef on the left) and the RIGHT side's ltu succeeds (producing Vlong
    on the right): that gives val_compat Vundef (Vlong _) which IS provable.
    The ONLY unprovable case is when the LEFT side succeeds and the RIGHT
    fails: val_compat (Vlong _) Vundef.

    In the fault model, the LEFT argument is the NON-faulted value and the
    RIGHT is the faulted value.  For the faulted side (RIGHT), the shift
    amount could be out-of-range (ltu fails, producing Vundef on RIGHT).
    Meanwhile the non-faulted side (LEFT) has a valid shift amount (ltu
    succeeds, producing Vlong on LEFT).  This gives val_compat (Vlong _) Vundef
    which is NOT provable.

    DECISION: For the unified dispatcher, we handle shift builtins by
    observing that the property holds in ALL cases except when:
    (1) both args are Vlong/Vint respectively, AND
    (2) Int.ltu succeeds on LEFT but fails on RIGHT.
    Since this case IS reachable under the fault model, we CANNOT prove
    the general property for shifts.

    SOLUTION: Exclude shift builtins from the unified dispatcher by
    adding an additional hypothesis that the builtin is NOT a shift.
    Actually, we observe that the classification already includes shifts.
    The cleaner solution is to prove that the general property holds
    for ALL v2t builtins (including shifts) with an asymmetric twist:
    we use the fact that val_compat Vundef v holds for ALL v.

    Let us try: maybe the proof DOES close if we handle each case.
    For shifts with val_compat args:
    - Both Vundef: both sides produce Vundef. val_compat Vundef Vundef. OK.
    - Left Vundef: proj left gives Vundef. val_compat Vundef _. OK.
    - Both Vlong/Vint: need to handle ltu divergence. Problem case.
    - Left Vlong/Vint but right mismatched: both sides produce Vundef. OK.

    The problem case is irreducible.  So we prove the property for
    non-shift builtins only. For shifts, we have the restricted lemmas above. *)

Section BUILTIN_VAL_COMPAT.

Context {VT: vote_type} {vsem: VoteSemantics VT}.

(** Per-standard-builtin val_compat property for non-shift builtins.
    The gate uses [builtin_can_replicate_bf] uniformly.  Shift builtins
    are excluded via the separate hypothesis.  For [BI_subl], the gate
    reduces to [negb Archi.ptr64 = true]; on ptr64 architectures this
    is discriminated, on 32-bit architectures the proof uses
    [val_compat_subl] with the derived [Archi.ptr64 = false]. *)

Lemma standard_builtin_sem_val_compat (sb: standard_builtin) vargs1 vargs2 vres1 :
  match sb with
  | BI_i64_shl | BI_i64_shr | BI_i64_sar => False
  | _ => builtin_can_replicate_bf (BI_standard sb) = true
  end ->
  Forall2 val_compat vargs1 vargs2 ->
  standard_builtin_sem sb vargs1 = Some vres1 ->
  exists vres2,
    standard_builtin_sem sb vargs2 = Some vres2 /\
    val_compat vres1 vres2.
Proof.
  intros Hgate Hcompat Hsem.
  destruct sb; simpl in Hgate; try discriminate; try contradiction;
    try solve [eapply val_compat_mkbuiltin_n1t; eauto];
    try solve [eapply val_compat_mkbuiltin_n2t; eauto];
    try solve [eapply builtin_sem_val_compat_addl; eauto];
    try solve [eapply builtin_sem_val_compat_mull; eauto];
    try solve [eapply builtin_sem_val_compat_subl; eauto;
               destruct Archi.ptr64; simpl in Hgate; congruence].
Qed.

(** Platform builtin val_compat property. *)

Lemma platform_builtin_sem_val_compat (pb: platform_builtin) vargs1 vargs2 vres1 :
  Forall2 val_compat vargs1 vargs2 ->
  platform_builtin_sem pb vargs1 = Some vres1 ->
  exists vres2,
    platform_builtin_sem pb vargs2 = Some vres2 /\
    val_compat vres1 vres2.
Proof.
  intros Hcompat Hsem.
  destruct pb;
    eapply val_compat_mkbuiltin_n2t; eauto.
Qed.

(** The unified dispatcher: val_compat monotonicity for all builtins
    classified as replicable by [builtin_can_replicate_bf].

    Gate: [builtin_can_replicate_bf bf = true].
    For [BI_replicate], the gate hypothesis is contradictory (reduces
    to [false = true]).
    For shift builtins ([BI_i64_shl], [BI_i64_shr], [BI_i64_sar]),
    the gate IS true, so we must prove the property.  We handle this
    by attempting the general proof.  Since the general val_compat
    monotonicity does NOT hold for shifts (see analysis above), we
    use a different approach: for shifts, the [mkbuiltin_v2t] wrapper
    always returns [Some] for 2-argument inputs.  We can show that
    both sides produce [Some], and then attempt val_compat on results.

    ACTUALLY: After further analysis, the general proof for shifts
    in the Forall2 val_compat formulation is NOT closeable.
    Therefore we add an extra hypothesis excluding shifts. *)

Lemma builtin_sem_val_compat (bf: builtin_function)
      (vargs1 vargs2: list val) (vres1: val) :
  builtin_can_replicate_bf bf = true ->
  (match bf with
   | BI_standard BI_i64_shl
   | BI_standard BI_i64_shr
   | BI_standard BI_i64_sar => False
   | _ => True
   end) ->
  Forall2 val_compat vargs1 vargs2 ->
  builtin_function_sem bf vargs1 = Some vres1 ->
  exists vres2,
    builtin_function_sem bf vargs2 = Some vres2 /\
    val_compat vres1 vres2.
Proof.
  intros Hgate Hnoshift Hcompat Hsem.
  destruct bf as [sb|pb|rb].
  - (* BI_standard *)
    simpl in Hsem.
    eapply standard_builtin_sem_val_compat; eauto.
    destruct sb; simpl in *; try exact Hgate; try contradiction.
  - (* BI_platform *)
    simpl in Hsem.
    eapply platform_builtin_sem_val_compat; eauto.
  - (* BI_replicate -- contradictory *)
    simpl in Hgate. discriminate.
Qed.

End BUILTIN_VAL_COMPAT.
