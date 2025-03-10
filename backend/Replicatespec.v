(** TODO: maybe copy monadInv tactic for use with RTLgen monad. *)

Require Import
  AST
  Coqlib
  Errors
  Globalenvs
  Integers
  Linking
  Maps
  Memory
  Op
  Registers
  Replicate
  RTLgen
  RTLtyping
  Smallstep
  Values
.
Require Import RTL.
Require Import Replicate.
Require Import Errors.
Import ListNotations.

Local Open Scope positive_scope.

Ltac gen_case H :=
  match goal with
  | [ _: match ?X with
         | RTLgen.Error _ => _
         | RTLgen.OK _ _ _ => _ end = _ |- _ ] =>
      destruct X eqn:H
  end.

Ltac lr_case :=
  match goal with
  | [ _: match ?X with
         | left _ => _
         | right _ => _ end = _ |- _ ] =>
      destruct X
  end.

Definition rm_wf (rm : PMap.t (reg * reg)) (l : list positive) : Prop :=
  forall r1 r2 r3,
    In r1 l ->
    PMap.get r1 rm = (r2, r3) ->
    NoDup [r1; r2; r3] /\
      forall r1' r2' r3',
        In r1' l ->
        r1 <> r1' ->
        PMap.get r1' rm = (r2', r3') ->
        NoDup [r1; r2; r3; r1'; r2'; r3'].

Inductive match_regs (rm : PMap.t (reg * reg))
  : list reg -> list reg -> list reg -> Prop :=
| match_nil : match_regs rm [] [] []
| match_cons : forall r1 r2 r3 rs1 rs2 rs3,
    rm !! r1 = (r2, r3) ->
    match_regs rm rs1 rs2 rs3 ->
    match_regs rm (r1 :: rs1) (r2 :: rs2) (r3 :: rs3).

(* Inductive maj_voteR (c : code) (r1 r2 r3 : reg) (pc succ : node) : typ -> Prop := *)
(* | maj_vote_int : *)
(*   forall n1 n2, *)
(*     c ! pc = Some (Icond (Ccomp Cne) [r1; r2] n1 succ) -> *)
(*     c ! n1 = Some (Icond (Ccomp Ceq) [r2; r3] n2 succ) -> *)
(*     c ! n2 = Some (Iop Omove [r2] r1 succ) -> *)
(*     maj_voteR c r1 r2 r3 pc succ Tint *)
(* | maj_vote_long : *)
(*   forall n1 n2, *)
(*     c ! pc = Some (Icond (Ccompl Cne) [r1; r2] n1 succ) -> *)
(*     c ! n1 = Some (Icond (Ccompl Ceq) [r2; r3] n2 succ) -> *)
(*     c ! n2 = Some (Iop Omove [r2] r1 succ) -> *)
(*     maj_voteR c r1 r2 r3 pc succ Tlong *)
(* | maj_vote_single : *)
(*   forall n1 n2, *)
(*     c ! pc = Some (Icond (Ccompfs Cne) [r1; r2] n1 succ) -> *)
(*     c ! n1 = Some (Icond (Ccompfs Ceq) [r2; r3] n2 succ) -> *)
(*     c ! n2 = Some (Iop Omove [r2] r1 succ) -> *)
(*     maj_voteR c r1 r2 r3 pc succ Tsingle *)
(* | maj_vote_float : *)
(*   forall n1 n2, *)
(*     c ! pc = Some (Icond (Ccompf Cne) [r1; r2] n1 succ) -> *)
(*     c ! n1 = Some (Icond (Ccompf Ceq) [r2; r3] n2 succ) -> *)
(*     c ! n2 = Some (Iop Omove [r2] r1 succ) -> *)
(*     maj_voteR c r1 r2 r3 pc succ Tfloat *)
(* . *)

Definition comp_of_typ (ty : typ) : comparison -> condition :=
  match ty with
  | Tint => Ccompu
  | Tlong => Ccomplu
  | Tsingle => Ccompfs
  | Tfloat => Ccompf
  | _ => Ccomp
  end.

Definition is_actual_type (ty : typ) : Prop :=
  match ty with
  | Tany32 => False
  | Tany64 => False
  | _ => True
  end.

Inductive maj_voteR
  (c : code) (ty : typ) (r1 r2 r3 : reg) (pc succ : node) : Prop :=
| maj_vote_1 :
  forall n,
    is_actual_type ty ->
    c ! pc = Some (Icond (comp_of_typ ty Cne) [r1; r2] n succ) ->
    (* c ! n = Some (Iop Omove [r3] r1 succ) -> *)
    c ! n = Some (smove ty r3 r1 succ) ->
    maj_voteR c ty r1 r2 r3 pc succ.

(* Fixpoint maj_vote_regs *)
(*   (re : regenv) (rm : PMap.t (reg * reg)) (regs : list reg) (pc : node) *)
(*   : mon node := *)
(*   match regs with *)
(*   | [] => ret pc *)
(*   | r1 :: rs => *)
(*       do succ <- maj_vote_regs re rm rs pc; *)
(*       let (r2, r3) := PMap.get r1 rm in *)
(*       maj_vote re r1 r2 r3 succ *)
(*   end. *)

Inductive maj_vote_regsR c re rm : list reg -> node -> node -> Prop :=
| maj_vote_regs_nil :
  forall pc,
    maj_vote_regsR c re rm nil pc pc
| maj_vote_regs_cons :
  forall r1 r2 r3 args pc succ n,
    rm # r1 = (r2, r3) ->
    maj_vote_regsR c re rm args pc n ->
    maj_voteR c (re r1) r1 r2 r3 n succ ->
    maj_vote_regsR c re rm (r1 :: args) pc succ
.

Inductive match_instr
  (re : regenv) (rm : PMap.t (reg * reg)) (pc : positive) (c : code)
  : instruction -> Prop :=
| match_inop :
  forall n,
    PTree.get pc c = Some (Inop n) ->
    match_instr re rm pc c (Inop n)
| match_iop :
  forall op args1 args2 args3 res1 res2 res3 n1 n2 succ,
    match_regs rm args1 args2 args3 ->
    rm !! res1 = (res2, res3) ->
    c ! pc = Some (Iop op args2 res2 n1) ->
    c ! n1 = Some (Iop op args3 res3 n2) ->
    c ! n2 = Some (Iop op args1 res1 succ) ->
    match_instr re rm pc c (Iop op args1 res1 succ)
| match_iload :
  forall chunk addr args1 args2 args3 res1 res2 res3 n1 n2 succ,
    match_regs rm args1 args2 args3 ->
    rm !! res1 = (res2, res3) ->
    c ! pc = Some (Iload chunk addr args2 res2 n1) ->
    c ! n1 = Some (Iload chunk addr args3 res3 n2) ->
    c ! n2 = Some (Iload chunk addr args1 res1 succ) ->
    match_instr re rm pc c (Iload chunk addr args1 res1 succ)
| match_istore :
  forall chunk addr args src1 src2 src3 n succ,
    rm !! src1 = (src2, src3) ->
    maj_vote_regsR c re rm args pc n ->
    c ! n = Some (Istore chunk addr args src1 succ) ->
    match_instr re rm pc c (Istore chunk addr args src1 succ)
| match_icall :
  forall sig fn args dst1 dst2 dst3 succ n1 n2 n3,
    rm !! dst1 = (dst2, dst3) ->
    maj_vote_regsR c re rm args pc n1 ->
    c ! n1 = Some (Icall sig fn args dst1 n2) ->
    (* c ! n2 = Some (Iop Omove [dst1] dst2 n3) -> *)
    (* c ! n3 = Some (Iop Omove [dst1] dst3 succ) -> *)
    c ! n2 = Some (smove (re dst1) dst1 dst2 n3) ->
    c ! n3 = Some (smove (re dst1) dst1 dst3 succ) ->
    match_instr re rm pc c (Icall sig fn args dst1 succ)
.

(* Inductive maj_vote_regsR c re rm : list reg -> node -> node -> Prop := *)

  (* | Itailcall: signature -> reg + ident -> list reg -> instruction *)
  (* | Ibuiltin: external_function -> list (builtin_arg reg) -> builtin_res reg -> node -> instruction *)
  (* | Icond: condition -> list reg -> node -> node -> instruction *)
  (* | Ijumptable: reg -> list node -> instruction *)
  (* | Ireturn: option reg -> instruction. *)

Definition match_code (re : regenv) (rm : PMap.t (reg * reg)) (c c': code) : Prop :=
  forall p i, c ! p = Some i -> match_instr re rm p c' i.

Inductive match_entrypoint (re : regenv) (rm : PMap.t (reg * reg)) (c : code)
  : list reg -> node -> node -> Prop :=
| match_entrypoint_nil :
  forall entrypoint,
    match_entrypoint re rm c [] entrypoint entrypoint
| match_entrypoint_cons :
  forall param params entrypoint n m p r2 r3,
    rm !! param = (r2, r3) ->
    (* c ! entrypoint = Some (Iop Omove [param] r2 n) -> *)
    (* c ! n = Some (Iop Omove [param] r3 m) -> *)
    c ! entrypoint = Some (smove (re param) param r2 n) ->
    c ! n = Some (smove (re param) param r3 m) ->
    match_entrypoint re rm c params m p ->
    match_entrypoint re rm c (param :: params) entrypoint p.

Inductive match_function re rm : function -> function -> Prop :=
| match_fun : forall old_rm sig params stacksize c c' entrypoint entrypoint',
    (* rm_wf rm (PSet.elements (all_regs params c)) -> *)
    match_code re rm c c' ->
    match_entrypoint re rm c' params entrypoint' entrypoint ->
    match_function re rm
      ({|
          fn_sig := sig
        ; fn_params := params
        ; fn_stacksize := stacksize
        ; fn_code := c
        ; fn_entrypoint := entrypoint
        ; fn_rm := old_rm
       |})
      ({|
          fn_sig := sig
        ; fn_params := params
        ; fn_stacksize := stacksize
        ; fn_code := c'
        ; fn_entrypoint := entrypoint'
        ; fn_rm := Some rm
        |}).

Inductive match_fundef: fundef -> fundef -> Prop :=
| match_internal :
  forall re rm f tf
    (FUN : match_function re rm f tf),
    match_fundef (Internal f) (Internal tf)
| match_external :
  forall f,
    match_fundef (External f) (External f).

Lemma match_regs_map_rm rm l :
  match_regs rm l (map (fun r => fst rm # r) l) (map (fun r => snd rm # r) l).
Proof.
  induction l; constructor; auto.
  destruct (rm # a); reflexivity.
Qed.

Lemma state_incr_maj_voteR s s' ty r1 r2 r3 pc succ :
  is_actual_type ty ->
  (forall pc : positive, (st_code s) ! pc = None \/
                      (st_code s') ! pc = (st_code s) ! pc) ->
  maj_voteR (st_code s) ty r1 r2 r3 pc succ ->
  maj_voteR (st_code s') ty r1 r2 r3 pc succ.
Proof.
  intros Hty Hle Hmaj; inv Hmaj.
  destruct (Hle pc) as [?|Hpc]; try congruence.
  destruct (Hle n) as [?|Hn]; try congruence.
  econstructor; auto.
  - rewrite Hpc; eauto.
  - rewrite Hn; eauto.
Qed.

Lemma state_incr_maj_vote_regsR re rm p s s' rs n :
  (forall pc : positive, (st_code s) ! pc = None \/
                      (st_code s') ! pc = (st_code s) ! pc) ->
  maj_vote_regsR (st_code s) re rm rs p n ->
  maj_vote_regsR (st_code s') re rm rs p n.
Proof.
  revert p n s s'.
  induction rs; intros p n s s' Hle Hmaj; inv Hmaj.
  { constructor. }
  econstructor; eauto.
  eapply state_incr_maj_voteR; eauto.
  inv H5; auto.
Qed.

Lemma state_incr_match_instr re rm p i s s' :
  state_incr s s' ->
  match_instr re rm p (st_code s) i ->
  match_instr re rm p (st_code s') i.
Proof.
  intros Hs Hmatch.
  inv Hs.
  inv Hmatch.
  - constructor; destruct (H1 p); congruence.
  - destruct (H1 p) as [?|Hs']; try congruence.
    destruct (H1 n1) as [?|Hs'1]; try congruence.
    destruct (H1 n2) as [?|Hs'2]; try congruence.
    econstructor; eauto.
    + rewrite Hs'; eauto.
    + rewrite Hs'1; eauto.
    + rewrite Hs'2; eauto.
  - destruct (H1 p) as [?|Hs']; try congruence.
    destruct (H1 n1) as [?|Hs'1]; try congruence.
    destruct (H1 n2) as [?|Hs'2]; try congruence.
    econstructor; eauto.
    + rewrite Hs'; eauto.
    + rewrite Hs'1; eauto.
    + rewrite Hs'2; eauto.
  - destruct (H1 n) as [?|Hs']; try congruence.
    econstructor; eauto.
    2: { rewrite Hs'; auto. }
    eapply state_incr_maj_vote_regsR; eauto.
  - destruct (H1 n1) as [?|Hn1]; try congruence.
    destruct (H1 n2) as [?|Hn2]; try congruence.
    destruct (H1 n3) as [?|Hn3]; try congruence.
    econstructor; eauto.
    + eapply state_incr_maj_vote_regsR; eauto.
    + rewrite Hn1; eauto.
    + rewrite Hn2; eauto.
    + rewrite Hn3; auto.
Qed.

Lemma maj_vote_maj_voteR re r1 r2 r3 pc succ s s' pf :
  pc < s.(st_nextnode) ->
  maj_vote re r1 r2 r3 pc s = RTLgen.OK succ s' pf ->
  maj_voteR s'.(st_code) (re r1) r1 r2 r3 pc succ.
Proof.
(*   unfold maj_vote, RTLgen.bind; simpl; intros Hlt Hmaj. *)
(*   gen_case H0; inv Hmaj. *)
(*   gen_case H2; inv H1. *)
(*   gen_case H1; inv H2. *)
(*   gen_case H2; inv H1. *)
(*   gen_case H1; inv H2. *)
(*   gen_case H2; inv H3. *)
(*   gen_case H3; inv H2. *)
(*   unfold update_instr in *. *)
(*   lr_case; try congruence; lr_case; inv H3. *)
(*   lr_case; try congruence; lr_case; inv H1. *)
(*   simpl in *. *)
(*   inv s6; inv s5; inv s4; inv s3; inv s2; inv s1; inv pf. *)
(*   simpl in *; unfold Ple in *. *)
(*   assert (s.(st_nextnode) <= s'0.(st_nextnode)). *)
(*   { clear H0; inv s0; auto. } *)
(*   eapply maj_vote_1 with (n:=st_nextnode s'0). *)
(*   - destruct (re r1); inv H0; apply I. *)
(*   - rewrite PTree.gso; try lia. *)
(*     rewrite PTree.gss. *)
(*     destruct (re r1); inv H0; reflexivity. *)
(*   - rewrite PTree.gss; reflexivity. *)
  (* Qed. *)
Admitted.

Lemma maj_vote_succ_lt_nextnode re r1 r2 r3 pc succ s s' pf :
  pc < s.(st_nextnode) ->
  maj_vote re r1 r2 r3 pc s = RTLgen.OK succ s' pf ->
  succ < s'.(st_nextnode).
Proof.
(*   unfold maj_vote, RTLgen.bind; simpl; intros Hlt Hmaj. *)
(*   gen_case H0; inv Hmaj. *)
(*   gen_case H2; inv H1. *)
(*   gen_case H1; inv H2. *)
(*   gen_case H2; inv H1. *)
(*   gen_case H1; inv H2. *)
(*   gen_case H2; inv H3. *)
(*   gen_case H3; inv H2. *)
(*   unfold update_instr in *. *)
(*   lr_case; try congruence; lr_case; inv H3. *)
(*   lr_case; try congruence; lr_case; inv H1. *)
(*   simpl in *; lia. *)
  (* Qed. *)
Admitted.

Lemma maj_vote_regs_succ_lt_nextnode re rm regs pc succ s s' pf :
  pc < s.(st_nextnode) ->
  maj_vote_regs re rm regs pc s = RTLgen.OK succ s' pf ->
  succ < s'.(st_nextnode).
Proof.
  revert pc succ s s' pf.
  induction regs; intros pc n s s' pf Hlt Hmaj; inv Hmaj; auto.
  unfold RTLgen.bind in H0.
  gen_case Hmaj; inv H0.
  destruct (rm # a) eqn:Ha.
  gen_case H0; inv H1.
  apply IHregs in Hmaj; auto.
  eapply maj_vote_succ_lt_nextnode; eauto.
Qed.

Lemma maj_vote_regs_maj_vote_regsR re rm regs pc succ s s' pf :
  pc < s.(st_nextnode) ->
  maj_vote_regs re rm regs pc s = RTLgen.OK succ s' pf ->
  maj_vote_regsR s'.(st_code) re rm regs pc succ.
Proof.
  revert pc succ s s' pf.
  induction regs; simpl; intros pc succ s s' pf Hlt Hmaj.
  { inv Hmaj; constructor. }
  unfold RTLgen.bind in Hmaj.
  gen_case H0; inv Hmaj.
  destruct (rm # a) eqn:Ha.
  gen_case Hmaj; inv H1.
  pose proof H0 as H0'.
  apply maj_vote_regs_succ_lt_nextnode in H0'; auto.
  apply IHregs in H0; auto.
  econstructor; eauto.
  - eapply state_incr_maj_vote_regsR.
    2: { eauto. }
    clear Hmaj; inv s1; auto.
  - eapply maj_vote_maj_voteR; eauto.
Qed.

Lemma maj_voteR_ptree_set c ty r1 r2 r3 pc succ n i :
  c ! n = None ->
  maj_voteR c ty r1 r2 r3 pc succ ->
  maj_voteR (PTree.set n i c) ty r1 r2 r3 pc succ.
Proof.
  intros Hc Hmaj; inv Hmaj.
  econstructor; auto.
  - destruct (DecidableTypeEx.Positive_as_DT.eq_dec n pc); subst; try congruence.
    rewrite PTree.gso; eauto.
  - rewrite PTree.gso; eauto.
    intro; subst; congruence.
Qed.

Lemma maj_vote_regsR_ptree_set c re rm rs pc succ n i :
  c ! n = None ->
  maj_vote_regsR c re rm rs pc succ ->
  maj_vote_regsR (PTree.set n i c) re rm rs pc succ.
Proof.
  revert pc succ.
  induction rs; intros pc succ Hc Hmaj; inv Hmaj.
  { constructor. }
  econstructor; eauto.
  apply maj_voteR_ptree_set; auto.
Qed.

(** The translation algorithm meets its relational specification. *)
Lemma iterM_match_instr
  p i (l : list (positive * instruction)) re rm s s' pf :
  p < s.(st_nextnode) ->
  In (p, i) l ->
  iterM (transf_instr re rm) l s = RTLgen.OK tt s' pf ->
  match_instr re rm p (st_code s') i.
Proof.
  revert s s' pf; induction l; simpl; intros s s' pf Hlt Hin Htransf.
  { contradiction. }
  unfold RTLgen.bind in Htransf.
  gen_case Hiter; inv Htransf.
  gen_case Htransf; inv H0.
  destruct Hin as [?|Hin]; subst.
  - simpl in Htransf.
    destruct i.
    
    (* Inop *)
    + unfold update_instr in Htransf.
      lr_case; try congruence; lr_case; inv Htransf.
      simpl; constructor; rewrite PTree.gss; reflexivity.

    (* Iop *)
    + unfold RTLgen.bind in Htransf.
      gen_case Hreserve0; inv Htransf.
      gen_case H1; inv H0.
      gen_case H2; inv H1.
      gen_case Hupdp; inv H2.
      gen_case H3; inv H0.
      gen_case Hupdn0; inv H3.
      gen_case Hupd'; inv H0.
      unfold update_instr in *.
      lr_case; try congruence; lr_case; inv Hupd'.
      lr_case; try congruence; lr_case; inv Hupdn0.
      lr_case; try congruence; lr_case; inv Hupdp.
      inv Hreserve0.
      destruct (rm # r) eqn:Hrmr; simpl in *.
      assert (p < st_nextnode s'0).
      { clear Hiter; inv s0; simpl in *; unfold Ple in *; lia. }
      eapply match_iop with (pc := p)
                            (n1 := s'0.(st_nextnode))
                            (n2 := Pos.succ (s'0.(st_nextnode))); eauto.
      { apply match_regs_map_rm. }
      * rewrite 2!PTree.gso; try lia.
        rewrite PTree.gss; reflexivity.
      * rewrite PTree.gso; try lia.
        rewrite PTree.gss; reflexivity.
      * rewrite PTree.gss; reflexivity.

    (* Iload *)
    + unfold RTLgen.bind in Htransf; simpl in Htransf.
      gen_case H0; inv Htransf.
      gen_case H1; inv H0.
      gen_case Hupdp; inv H1.
      gen_case H1; inv H0.
      gen_case Hupd'; inv H1.
      gen_case Hupd''; inv H0.
      unfold update_instr in *.
      lr_case; try congruence; lr_case; inv Hupd''.
      lr_case; try congruence; lr_case; inv Hupd'.
      lr_case; try congruence; lr_case; inv Hupdp.
      destruct (rm # r) eqn:Hrmr; simpl in *.
      assert (p < st_nextnode s'0).
      { clear Hiter; inv s0; simpl in *; unfold Ple in *; lia. }
      eapply match_iload with (pc := p)
                              (n1 := s'0.(st_nextnode))
                              (n2 := Pos.succ (s'0.(st_nextnode))); eauto.
      { apply match_regs_map_rm. }
      * rewrite 2!PTree.gso; try lia.
        rewrite PTree.gss; reflexivity.
      * rewrite PTree.gso; try lia.
        rewrite PTree.gss; reflexivity.
      * rewrite PTree.gss; reflexivity.

    (* Istore *)
    + unfold RTLgen.bind in Htransf; simpl in Htransf.
      gen_case Hmaj; inv Htransf.
      gen_case Hupd; inv H0.
      apply maj_vote_regs_maj_vote_regsR in Hmaj.
      2: { clear Hiter; inv s0; unfold Ple in *; lia. }
      unfold update_instr in Hupd.
      lr_case; try congruence.
      lr_case; inv Hupd.
      simpl in *.
      inv s1; inv s3; inv pf; simpl in *; unfold Ple in *.
      destruct (rm # r) eqn:Hrmr; simpl in *.
      econstructor.
      { eauto. }
      2: { rewrite PTree.gss; reflexivity. }
      apply maj_vote_regsR_ptree_set; auto.

    (* Icall *)
    + unfold RTLgen.bind in Htransf; simpl in Htransf.
      gen_case Hmaj; inv Htransf.
      gen_case H1; inv H0.
      gen_case H0; inv H1.
      gen_case H1; inv H0.
      unfold copy_to_shadows in H2.
      destruct (rm # r) eqn:Hrmr.
      unfold RTLgen.bind in H2.
      gen_case H0; inv H2.
      (* gen_case H2; inv H0. *)
      (* gen_case H0; inv H3. *)
      (* gen_case H3; inv H0. *)
      (* gen_case H0; inv H4. *)
      (* assert (p < st_nextnode s'0). *)
      (* { clear Hiter; inv s0; simpl in *; unfold Ple in *; lia. } *)
      (* assert (Hn0: n0 < s'1.(st_nextnode)). *)
      (* { eapply maj_vote_regs_succ_lt_nextnode. *)
      (*   2: { eauto. } *)
      (*   auto. } *)
      (* apply maj_vote_regs_maj_vote_regsR in Hmaj. *)
      (* 2: { clear Hiter; inv s0; unfold Ple in *; lia. } *)
      (* unfold update_instr in *. *)
      (* lr_case; try congruence; lr_case; inv H0. *)
      (* lr_case; try congruence; lr_case; inv H3. *)
      (* lr_case; try congruence; lr_case; inv H1. *)
      (* inv H2. *)
      (* simpl in *. *)
      (* inv s12; inv s11; inv s10; inv s9; inv s8; inv s7; *)
      (*   inv s6; inv s5; inv s4; inv s1; inv pf. *)
      (* simpl in *; unfold Ple in *. *)
      (* destruct s3. *)
      (* { admit. } *)
      (* { econstructor. *)
      (*   { eauto. } *)
      (*   4: { rewrite PTree.gss; reflexivity. } *)
      (*   * repeat apply maj_vote_regsR_ptree_set; eauto. *)
      (* * rewrite 2!PTree.gso; try lia. *)
      (*   rewrite PTree.gss; eauto. *)
      (* * rewrite PTree.gso; try lia. *)
    (*   rewrite PTree.gss; reflexivity. } *)
      admit.

    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
  - unfold RTLgen.bind in Htransf.
    destruct u.
    assert (H: match_instr re rm p (st_code s'0) i).
    { eapply IHl; eauto. }
    eapply state_incr_match_instr; eauto.
Admitted.

Lemma transf_code_code_matches (c : code) (re : regenv) rm s s' pf :
  (forall p i, c ! p = Some i -> p < st_nextnode s) ->
  transf_code re rm c s = RTLgen.OK tt s' pf ->
  match_code re rm c s'.(st_code).
Proof.
  intros Hlt Hc p i Hi.
  eapply iterM_match_instr; eauto.
  apply PTree.elements_correct; auto.
Qed.

Lemma bind_inversion :
  forall (A B: Type) (f: mon A) (g: A -> mon B) (y: B) s0 s2 pf,
    RTLgen.bind f g s0 = RTLgen.OK y s2 pf ->
  exists x s1 pf0 pf1, f s0 = RTLgen.OK x s1 pf0 /\ g x s1 = RTLgen.OK y s2 pf1.
Proof.
  intros A B f g u s s' pf Heq.
  unfold RTLgen.bind in Heq.
  destruct (f s) eqn:Hf; inv Heq.
  destruct (g a s'0) eqn:Hg; inv H0.
  eexists; eexists; eexists; eexists; split; eauto.
Qed.

Lemma transf_fun_code_matches
  rm (f : function) (re : regenv) entrypoint s s1 s' pf pf1 :
  transf_fun re f s = RTLgen.OK entrypoint s' pf ->
  (* replication_map f s = RTLgen.OK rm s1 pf1 -> *)
  replication_map f s = RTLgen.OK rm s1 pf1 ->
  (forall p i, (fn_code f) ! p = Some i -> p < st_nextnode s) ->
  match_code re rm f.(fn_code) s'.(st_code).
Proof.
  intros Hf Hrm Hlt.
  unfold transf_fun in Hf.
  apply bind_inversion in Hf.
  destruct Hf as (rm' & s1' & pf0 & pf1' & Hrm' & Hf).
  rewrite Hrm' in Hrm; inv Hrm.
  apply bind_inversion in Hf.
  destruct Hf as (n0 & s2 & pf2 & pf3 & Hparams & Hf).
  apply bind_inversion in Hf.
  destruct Hf as ([] & s3 & pf4 & pf5 & Hf & Hret).
  inv Hret.
  apply transf_code_code_matches in Hf; auto.
  intros p i Hpi.
  clear Hparams.
  inv pf1; inv pf2.
  unfold Ple in *.
  specialize (Hlt p i Hpi); lia.
Qed.

Lemma lt_ptree_fold_max c p i :
  c ! p = Some i ->
  p < PTree.fold (fun m pc (_ : instruction) => Pos.max m pc) c 1 + 1.
Proof.
  revert p i.
  apply PTree_Properties.fold_ind; intros t Ht p i Htp.
  { specialize (Ht p); congruence. }
  intros Hcp HI p' i' Htp'.
  destruct (DecidableTypeEx.Positive_as_DT.eq_dec p p'); subst.
  { lia. }
  assert (H: (PTree.remove p t) ! p' = Some i').
  { rewrite PTree.gro; auto. }
  specialize (HI p' i' H); lia.
Qed.

Lemma lt_nextnode_init_state p i sig params stacksize c entrypoint rm :
  c ! p = Some i ->
  p < st_nextnode (init_state {| fn_sig := sig
                               ; fn_params := params
                               ; fn_stacksize := stacksize
                               ; fn_code := c
                               ; fn_entrypoint := entrypoint
                               ; fn_rm := rm
                              |}).
Proof. intro Hget; eapply lt_ptree_fold_max; eauto. Qed.

Lemma lt_nextnode_init_state' p i f :
  (fn_code f) ! p = Some i ->
  p < st_nextnode (init_state f).
Proof. intro Hget; eapply lt_ptree_fold_max; eauto. Qed.

Lemma transf_fun'_code_matches rm (f tf : function) (re : regenv) s pf :
  transf_fun' re f = OK tf ->
  (* replication_map f (init_state f) = RTLgen.OK rm s pf -> *)
  replication_map f (init_state f) = RTLgen.OK rm s pf ->
  match_code re rm f.(fn_code) tf.(fn_code).
Proof.
  unfold transf_fun'.
  destruct (transf_fun re f (init_state f)) eqn:Hf; intros H Hrm; inv H; simpl.
  destruct p; inv H1.
  eapply transf_fun_code_matches; eauto.
  intros; eapply lt_nextnode_init_state'; eauto.
Qed.

Lemma transf_function_code_matches rm (f tf : function) s pf :
  transf_function f = OK tf ->
  (* replication_map f (init_state f) = RTLgen.OK rm s pf -> *)
  replication_map f (init_state f) = RTLgen.OK rm s pf ->
  exists re, match_code re rm f.(fn_code) tf.(fn_code).
Proof.
  intro H; monadInv H.
  exists x; eapply transf_fun'_code_matches; eauto.
Qed.

Inductive reg_used_in_instr (r : reg) : instruction -> Prop :=
| reg_used_iop_args : forall op args res succ,
    In r args ->
    reg_used_in_instr r (Iop op args res succ)
| reg_used_iop_res : forall op args succ,
    reg_used_in_instr r (Iop op args r succ)
| reg_used_iload_args : forall chunk addr args res succ,
    In r args ->
    reg_used_in_instr r (Iload chunk addr args res succ)
| reg_used_iload_res : forall chunk addr args succ,
    reg_used_in_instr r (Iload chunk addr args r succ)
| reg_used_istore_args : forall chunk addr args src succ,
    In r args ->
    reg_used_in_instr r (Istore chunk addr args src succ)
| reg_used_istore_src : forall chunk addr args succ,
    reg_used_in_instr r (Istore chunk addr args r succ)
| reg_used_icall_fn : forall sig args dst succ,
    reg_used_in_instr r (Icall sig (inl r) args dst succ)
| reg_used_icall_args : forall sig fn args dst succ,
    In r args ->
    reg_used_in_instr r (Icall sig fn args dst succ)
| reg_used_icall_dst : forall sig fn args succ,
    reg_used_in_instr r (Icall sig fn args r succ)
(* TODO: rest of instructions *)
.

  (* | Icall: signature -> reg + ident -> list reg -> reg -> node -> instruction *)
  (*     (** [Icall sig fn args dest succ] invokes the function determined by *)
  (*         [fn] (either a function pointer found in a register or a *)
  (*         function name), giving it the values of registers [args] *)
  (*         as arguments.  It stores the return value in [dest] and branches *)
  (*         to [succ]. *) *)

Definition reg_used_in_code (c : code) (r : reg) : Prop :=
  exists pc instr,
    c! pc = Some instr /\ reg_used_in_instr r instr.

Definition rm_inv
  (c : code) (rm : PMap.t (reg * reg)) (rs rs' : regset) : Prop :=
  forall r1, reg_used_in_code c r1 ->
        let (r2, r3) := rm # r1 in
        rs # r1 = rs' # r1 /\
          rs # r1 = rs' # r2 /\
          rs # r1 = rs' # r3 /\
          ~ reg_used_in_code c r2 /\
          ~ reg_used_in_code c r3.

Inductive match_stackframe : stackframe -> stackframe -> Prop :=
| match_frame :
  forall re rm res f tf sp pc rs trs n1 n2 res2 res3
    (FUN : match_function re rm f tf)
    (INV : rm_inv f.(fn_code) rm rs trs)
    (RM: rm # res = (res2, res3))
    (Hn1: tf.(fn_code) ! n1 = Some (Iop Omove [res] res2 n2))
    (Hn2: tf.(fn_code) ! n2 = Some (Iop Omove [res] res3 pc)),
    match_stackframe
      (Stackframe res f sp pc rs)
      (Stackframe res tf sp n1 trs).

(* Inductive wt_state: state -> Prop := *)
(*   | wt_state_intro: *)
(*       forall s f sp pc rs m env *)
(*         (WT_STK: wt_stackframes s (fn_sig f)) *)
(*         (WT_FN: wt_function f env) *)
(*         (WT_RS: wt_regset env rs), *)
(*       wt_state (State s f sp pc rs m) *)
(*   | wt_state_call: *)
(*       forall s f args m, *)
(*       wt_stackframes s (funsig f) -> *)
(*       wt_fundef f -> *)
(*       Val.has_type_list args (proj_sig_args (funsig f)) -> *)
(*       wt_state (Callstate s f args m) *)
(*   | wt_state_return: *)
(*       forall s v m sg, *)
(*       wt_stackframes s sg -> *)
(*       Val.has_type v (proj_sig_res sg) -> *)
(*       wt_state (Returnstate s v m). *)

Definition valid_pointer m b ofs : Prop :=
  Mem.valid_pointer m b (Ptrofs.unsigned ofs)
  || Mem.valid_pointer m b (Ptrofs.unsigned ofs - 1) = true.

Inductive match_states : state -> state -> Prop :=
| match_regular_states :
  forall stk tstk f tf sp pc rs rs' m re rm
    (* Well-typed *)
    (WT_STK: wt_stackframes stk (fn_sig f))
    (WT_FN: wt_function f re)
    (WT_RS: wt_regset re rs)
    (* Match *)
    (STACKS : list_forall2 match_stackframe stk tstk)
    (* (LINK: linkorder cu prog) *)
    (* (FUN: transf_function f = OK tf), *)
    (FUN : match_function re rm f tf)
    (RM : rm_inv f.(fn_code) rm rs rs')
    (RM_WF : rm_wf rm (fun_regs_list f)),
    (* (PTR: forall r, reg_used_in_code f.(fn_code) r -> *)
    (*            forall b ofs, rs # r = Vptr b ofs -> *)
    (*                     valid_pointer m b ofs), *)
    (* (RM_EQ : replication_map f.(fn_params) f.(fn_code) (init_state f) = *)
    (*            RTLgen.OK rm s1 pf), *)
    match_states (State stk f sp pc rs m) (State tstk tf sp pc rs' m)
| match_call_states :
  forall stk tstk f tf args m
    (* Well-typed *)
    (WT_STK : wt_stackframes stk (funsig f))
    (WT_FN : wt_fundef f)
    (WT_ARGS : Val.has_type_list args (proj_sig_args (funsig f)))
    (* Match *)
    (STACKS : list_forall2 match_stackframe stk tstk)
    (FUN : match_fundef f tf),
    match_states (Callstate stk f args m) (Callstate tstk tf args m)
| match_return_states :
  forall stk tstk sig v m
    (* Well-typed *)
    (WT_STK : wt_stackframes stk sig)
    (WT_RES : Val.has_type v (proj_sig_res sig))
    (* Match *)
    (STACKS : list_forall2 match_stackframe stk tstk),
    match_states (Returnstate stk v m) (Returnstate tstk v m)
.

(* Lemma match_states_wt_state (s ts : state) : *)
(*   match_states s ts -> *)
(*   wt_state s. *)
(* Proof. intro Hmatch; inv Hmatch; econstructor; eauto. Qed. *)

(* Lemma wt_match_stackframe s tstk re rm f tf : *)
(*   list_forall2 match_stackframe s tstk -> *)
(*   wt_stackframes s (fn_sig f) -> *)
(*   match_function re rm f tf -> *)
(*   wt_stackframes tstk (fn_sig tf). *)
(* Proof. *)
  
(* Admitted. *)

(* Definition rm_re (rm : PMap.t (reg * reg)) (re : regenv) : regenv := *)
(*   re. *)

(* Lemma wt_match_function re rm f tf : *)
(*   wt_function f re -> *)
(*   match_function re rm f tf -> *)
(*   wt_function tf (rm_re rm re). *)
(* Proof. *)
  
(* Admitted. *)

(* Lemma wt_match s ts : *)
(*   (* wt_state s -> *) *)
(*   match_states s ts -> *)
(*   wt_state ts. *)
(* Proof. *)
(*   intros Hmatch; inv Hmatch. *)
(*   - assert (Hwt: wt_function f re). *)
(*     { admit. } *)
(*     apply wt_state_intro with (env:=rm_re rm re). *)
(*     + eapply wt_match_stackframe; eauto. *)
(*     + (* eapply wt_match_function. *) *)
(*       admit. *)
      
(*     + admit. *)
(*   - admit. *)
(*   - admit. *)
(* Admitted. *)
