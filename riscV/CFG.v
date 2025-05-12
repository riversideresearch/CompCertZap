(** * Construct control flow graphs for assembler *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Asm.

Local Open Scope error_monad_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

(** TODO: Misplaced *)
Definition omap {A B} (f : A -> B) (m : option A) : option B :=
  match m with
  | Some x => Some (f x)
  | None => None
  end.
#[global] Arguments omap _ _ _ & !_ / : simpl nomatch, assert.

Lemma omap_compose {A B C} (g : B -> C) (f : A -> B) (m : option A) :
  omap g (omap f m) = omap (fun x => g (f x)) m.
Proof. now destruct m. Qed.

Lemma omap_id {A} (f : A -> A) (m : option A) :
  (forall x, f x = x) -> omap f m = m.
Proof. intros Hf. destruct m; simpl; auto. now rewrite Hf. Qed.

(** ** Assumptions about assembly *)

Definition label := positive.
Local Bind Scope positive_scope with label.

(**
An instruction's [kind] determines its successors in the control flow
graph.
*)

Variant kind : Type :=
| Label (lab : label)	(**i branch target, control flows to next instruction *)
| Exit	(**i exit a function's body (no successors) *)
| Branch (lab : label)	(**i unconditional branch *)
| CBranch (lab : label)	(**i conditional branch *)
| BTbl (tbl : list label)	(**i branch table *)
| Fallthrough.	(**i control flows to the next instruction *)

Module Type ASM.
  Parameter Inline instruction : Type.
  Parameter classify : instruction -> kind.

  Definition code := list instruction.
  Parameter find_instr : Z -> code -> option instruction.
  Parameter is_label : label -> instruction -> bool.
  Parameter label_pos : label -> Z -> code -> option Z.

  (* Not yet needed *)
  Axiom find_instr_spec : forall ofs c,
    0 <= ofs -> find_instr ofs c = nth_error c (Z.to_nat ofs).

  Axiom is_label_classify : forall lab i,
    if is_label lab i then classify i = Label lab else classify i <> Label lab.

  Axiom label_pos_mono : forall lab acc c ofs,
    label_pos lab acc c = Some ofs -> acc + 1 <= ofs.

  Axiom label_pos_nil : forall lab ofs, label_pos lab ofs nil = None.
  Axiom label_pos_cons : forall lab ofs i c,
    label_pos lab ofs (i :: c) =
    if is_label lab i
    then Some (ofs + 1)
    else label_pos lab (ofs + 1) c.
End ASM.

(* EXAMPLE *)
Module RiscVAsm <: ASM.
  Definition instruction := instruction.

  Definition classify (i : instruction) : kind :=
    match i with
    | Pj_l lab => Branch lab
    | Pj_s _ _ | Pj_r _ _ => Exit
    | Pjal_s _ _ | Pjal_r _ _ => Fallthrough
    | Pbeqw _ _ lab
    | Pbnew _ _ lab
    | Pbltw _ _ lab
    | Pbltuw _ _ lab
    | Pbgew _ _ lab
    | Pbgeuw _ _ lab
    | Pbeql _ _ lab
    | Pbnel _ _ lab
    | Pbltl _ _ lab
    | Pbltul _ _ lab
    | Pbgel _ _ lab
    | Pbgeul _ _ lab => CBranch lab
    | Plabel lab => Label lab
    | Pbtbl _ tbl => BTbl tbl
    | _ => Fallthrough
    end.

  Definition code := list instruction.
  Definition find_instr := find_instr.
  Definition is_label := is_label.
  Definition label_pos := label_pos.

  Lemma find_instr_spec ofs c :
    0 <= ofs -> find_instr ofs c = nth_error c (Z.to_nat ofs).
  Proof.
    revert ofs. induction c as [|i c IH]; intros ofs Hofs; simpl.
    { symmetry. apply nth_error_nil. }
    destruct (zeq ofs 0) as [->|?]; simpl; auto.
    rewrite IH; [|lia]. rewrite nth_error_cons.
    destruct (Z.to_nat ofs) eqn:?; [|f_equal]; lia.
  Qed.

  Lemma is_label_classify lab i :
    if is_label lab i then classify i = Label lab else classify i <> Label lab.
  Proof.
    unfold is_label. generalize (is_label_correct lab i).
    destruct (Asm.is_label _ _).
    { now intros ->. }
    destruct i; try discriminate; simpl. intros ? EQ. inv EQ. auto.
  Qed.

  Lemma label_pos_mono lab acc c ofs :
    label_pos lab acc c = Some ofs -> acc + 1 <= ofs.
  Proof.
    revert acc. induction c; simpl; intros acc Hlab.
    { discriminate. }
    destruct (Asm.is_label _ _).
    { inv Hlab. lia. }
    specialize (IHc _ Hlab). lia.
  Qed.

  Lemma label_pos_nil lab ofs : label_pos lab ofs nil = None.
  Proof. reflexivity. Qed.

  Lemma label_pos_cons lab ofs i c :
    label_pos lab ofs (i :: c) =
    if is_label lab i
    then Some (ofs + 1)
    else label_pos lab (ofs + 1) c.
  Proof. reflexivity. Qed.

End RiscVAsm.

(** ** Code offsets *)
(**
Relative offsets into an internal function's code (bumped by 1 to fit
in positive and work with Kildall's algorithm).
*)
Definition rel_pc : Type := positive.
Global Bind Scope positive_scope with rel_pc.

(** ** Building a control flow graph *)
Module Type CFG_DEFS (Import Asm : ASM).

  (**
  Node in an assembler CFG are addressed by code offsets (type
  [rel_pc]).
  *)
  #[projections(primitive)]
  Record node : Type := Node {
    code : instruction;
    succ : list rel_pc;
  }.

  Module Notations.
    Add Printing Constructor node.
  End Notations.

  (** [rel_pc] to [node]. Compare to Kildall's algorithm. *)
  Definition cfg : Type := PTree.t node.

End CFG_DEFS.

Module Type BUILD_CFG (Import Asm : ASM) (Import Defs : CFG_DEFS Asm).

  (**
  Build a control flow graph from a function's code.
  *)
  Parameter build_cfg' : Asm.code -> res cfg.

End BUILD_CFG.

Module Type CFG (Import Asm : ASM).
  Include CFG_DEFS Asm.
  Include BUILD_CFG Asm.
End CFG.

(** ** Utilities for [rel_pc] *)
Module Relpc.

  (**
  Bijection between relative PCs and code offsets of type [Z].
  *)
  Definition to_Z (pc : rel_pc) : Z := Z.pred (Z.pos pc).
  Definition of_Z (o : Z) : rel_pc := Z.to_pos (Z.succ o).

  Lemma to_of_Z o : 0 <= o -> to_Z (of_Z o) = o.
  Proof. unfold to_Z, of_Z. lia. Qed.
  Lemma of_to_Z pc : of_Z (to_Z pc) = pc.
  Proof. unfold to_Z, of_Z. lia. Qed.
  Lemma to_Z_inj pc1 pc2 : to_Z pc1 = to_Z pc2 -> pc1 = pc2.
  Proof.
    intros H%(f_equal of_Z). now rewrite !of_to_Z in H.
  Qed.
  Lemma of_Z_inj o1 o2 :
    0 <= o1 -> 0 <= o2 -> of_Z o1 = of_Z o2 -> o1 = o2.
  Proof.
    intros ?? H%(f_equal to_Z). now rewrite !to_of_Z in H.
  Qed.

  Lemma succ_of_Z z : 0 <= z -> Pos.succ (of_Z z) = of_Z (z + 1).
  Proof. unfold of_Z. lia. Qed.

  Lemma to_Z_succ pc : to_Z pc + 1 = to_Z (Pos.succ pc).
  Proof. unfold to_Z. lia. Qed.

End Relpc.

(** ** Label environments *)
(**
A finite map from [label] to [rel_pc] used to build CFGs without
linear factors from <<label_pos>>.
*)
Definition labelenv : Type := PTree.t rel_pc.

Module Type LABEL_ENV (Import Asm : ASM).

  Parameter make_labelenv' : Asm.code -> res labelenv.

  Notation label_pos' lab c := (label_pos lab 0 c) (only parsing).

  Axiom label_pos_labelenv : forall c m,
    make_labelenv' c = OK m ->
    forall lab : label, label_pos' lab c = omap Relpc.to_Z (m!lab).
  Axiom labelenv_label_pos : forall c m,
    make_labelenv' c = OK m ->
    forall lab : label, m!lab = omap Relpc.of_Z (label_pos' lab c).

End LABEL_ENV.

(** ** Building control flow graphs *)

Module BuildCFG (Import Asm : ASM)
  (Import LabelEnv : LABEL_ENV Asm)
  (Import Defs : CFG_DEFS Asm) <: BUILD_CFG Asm Defs.

  Definition resolve (m : labelenv) (lab : label) : res rel_pc :=
    match m!lab with
    | Some pc => OK pc
    | None => Error (MSG "unbound label " :: POS lab :: nil)
    end.

  Definition resolve_list (m : labelenv) :=
  fix resolve_list (labs : list label) (acc : list rel_pc) : res (list rel_pc) :=
    match labs with
    | nil => OK (rev acc)
    | lab :: labs => do pc <- resolve m lab; resolve_list labs (pc :: acc)
    end.

  Definition successors (m : labelenv) (next : rel_pc)
      (i : instruction) : res (list rel_pc) :=
    match classify i with
    | Label _ => OK (next :: nil)
    | Exit => OK nil
    | Branch lab => do pc <- resolve m lab; OK (pc :: nil)
    | CBranch lab => do pc <- resolve m lab; OK (pc :: next :: nil)
    | BTbl tbl => do pcs <- resolve_list m tbl nil; OK pcs
    | Fallthrough => OK (next :: nil)
    end.

  Definition build_cfg (m : labelenv) :=
  fix build_cfg (c : Asm.code) (pc : rel_pc) (acc : cfg) {struct c} : res cfg :=
    match c with
    | nil => OK acc
    | i :: c =>
      let next := Pos.succ pc in
      do pcs <- successors m next i;
      let acc := PTree.set pc (Node i pcs) acc in
      build_cfg c next acc
    end.

  Definition build_cfg' (c : Asm.code) : res (PTree.t node) :=
    do m <- make_labelenv' c;
    build_cfg m c xH (PTree.empty _).

End BuildCFG.

Module Cfg (Import Asm : ASM) (LE : LABEL_ENV Asm) <: CFG Asm.
  Include CFG_DEFS Asm.
  Include BuildCFG Asm LE.
End Cfg.

(** Building label environments *)
Module LabelEnv (Import Asm : ASM) <: LABEL_ENV Asm.

  Fixpoint make_labelenv (pc : rel_pc) (c : Asm.code) (m : labelenv) : res labelenv :=
    match c with
    | nil => OK m
    | i :: c =>
      let next := Pos.succ pc in
      let k := make_labelenv next c in
      match classify i with
      | Label lab =>
        match PTree.get lab m with
        | Some pc' =>
          Error (MSG "ambiguous label " :: POS lab ::
            MSG " at PC " :: POS pc' ::
            MSG " and PC " :: POS pc :: nil)
        | None => k (PTree.set lab next m)
        end
      | _ => k m
      end
    end.

  Definition make_labelenv' (c : Asm.code) : res labelenv :=
    make_labelenv xH c (PTree.empty _).

  Notation label_pos' lab c := (label_pos lab 0 c) (only parsing).

  Lemma make_labelenv_mono pc pc' c m1 m2 lab :
    make_labelenv pc c m1 = OK m2 ->
    m1!lab = Some pc' ->
    m2!lab = Some pc'.
  Proof.
    revert pc m1.
    induction c as [|i c IH]; simpl; intros pc m1 Hm Hget.
    { now inv Hm. }
    destruct (classify i); eauto; [].
    destruct (m1 ! _) eqn:Hget'; [discriminate|].
    erewrite IH; eauto. rewrite PTree.gso; auto. intros ->.
    rewrite Hget in Hget'. discriminate.
  Qed.

  Lemma label_pos_get z c acc m lab ofs :
    make_labelenv (Relpc.of_Z z) c acc = OK m ->
    0 <= z ->
    label_pos lab z c = Some ofs ->
    m!lab = Some (Relpc.of_Z ofs).
  Proof.
    revert z acc.
    induction c as [|i c IH]; simpl; intros z acc Hm Hz Hlab.
    { rewrite label_pos_nil in Hlab. discriminate. }
    rewrite label_pos_cons in Hlab.
    generalize (is_label_classify lab i). intros Hkind.
    rewrite Relpc.succ_of_Z in Hm; auto.
    destruct (is_label lab i).
    { rewrite Hkind in Hm.
      destruct (acc ! lab); [discriminate|].
      erewrite make_labelenv_mono; eauto.
      rewrite PTree.gss. now inv Hlab. }
    destruct (classify i).
    1: destruct (acc ! _); [discriminate|].
    all: erewrite IH; eauto.
    all: lia.
  Qed.

  Lemma label_pos'_get lab c ofs m :
    make_labelenv' c = OK m ->
    label_pos' lab c = Some ofs ->
    m!lab = Some (Relpc.of_Z ofs).
  Proof.
    intros. eapply label_pos_get; eauto. eassumption. reflexivity.
  Qed.

  Lemma get_label_pos pc pc' c acc m lab :
    make_labelenv pc c acc = OK m ->
    m!lab = Some pc' ->
    acc!lab = Some pc' \/
    label_pos lab (Relpc.to_Z pc) c = Some (Relpc.to_Z pc').
  Proof.
    revert pc acc. induction c as [|i c IH]; simpl; intros pc acc Hm Hget.
    { left. now inv Hm. }
    rewrite label_pos_cons, Relpc.to_Z_succ.
    generalize (is_label_classify lab i). intros Hkind.
    destruct (is_label lab i).
    { clear IH. right.
      rewrite Hkind in Hm. clear Hkind.
      destruct (acc ! lab); [discriminate|].
      rewrite (make_labelenv_mono Hm (PTree.gss lab (Pos.succ pc) acc)) in Hget.
      now inv Hget. }
    destruct (classify i) as [lab'| | | | |]; auto.
    destruct (acc ! _); [discriminate|].
    destruct (IH _ _ Hm Hget) as [Hacc|?]; auto.
    destruct (peq lab lab'); subst.
    { exfalso. now apply Hkind. }
    rewrite PTree.gso in Hacc; auto.
  Qed.

  Lemma get_label_pos' c m lab pc :
    make_labelenv' c = OK m ->
    m!lab = Some pc ->
    label_pos' lab c = Some (Relpc.to_Z pc).
  Proof.
    intros Hm Hlab.
    destruct (get_label_pos Hm Hlab). discriminate. assumption.
  Qed.

  Lemma label_pos_labelenv c m :
    make_labelenv' c = OK m ->
    forall lab : label, label_pos' lab c = omap Relpc.to_Z (m!lab).
  Proof.
    intros Hm lab.
    destruct (label_pos' lab c) as [ofs|] eqn:Hlab;
    destruct (m!lab) as [pc|] eqn:Hget; simpl.
    - erewrite label_pos'_get in Hget; eauto.
      inv Hget. rewrite Relpc.to_of_Z; auto.
      apply label_pos_mono in Hlab. lia.
    - erewrite label_pos'_get in Hget; eauto. discriminate.
    - erewrite get_label_pos' in Hlab; eauto.
    - reflexivity.
  Qed.

  Lemma labelenv_label_pos c m :
    make_labelenv' c = OK m ->
    forall lab : label, m!lab = omap Relpc.of_Z (label_pos' lab c).
  Proof.
    intros. erewrite label_pos_labelenv; eauto.
    rewrite omap_compose, omap_id; auto. apply Relpc.of_to_Z.
  Qed.

End LabelEnv.

Module Type EXAMPLE.
  Module LE := LabelEnv RiscVAsm.
  Module Import Cfg := Cfg RiscVAsm LE.

  Definition sg := AST.mksignature nil AST.Xvoid AST.cc_default.
  Definition before : list instruction :=
    Plabel 1%positive ::
    Pnop ::
    Pj_r RA sg ::
    nil
  .
  Definition after : cfg := ltac:(
    let cfg := eval vm_compute in
      match build_cfg' before with
      | OK c => c
      | Error _ => PTree.empty _
      end
    in exact cfg
  ).
  Compute PTree.get 1 after.
  Compute PTree.get 2 after.
  Compute PTree.get 3 after.
End EXAMPLE.
