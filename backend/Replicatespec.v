(** Relational specificaton of the TMR transformation. *)

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

Ltac gen_contra :=
  try match goal with
  | [H: RTLgen.Error _ = RTLgen.OK _ _ _ |- _ ] => inv H
  | [H: RTLgen.OK _ _ _ = RTLgen.Error _ |- _ ] => inv H
  end.

Ltac gen_inv :=
  match goal with
  | [H: RTLgen.OK _ _ _ = RTLgen.OK _ _ _ |- _ ] => inv H
  end.

Ltac gen_case H :=
  match goal with
  | [ _: match ?X with
         | RTLgen.Error _ => _
         | RTLgen.OK _ _ _ => _ end = _ |- _ ] =>
      destruct X eqn:H
  end; gen_contra; try gen_inv.

Ltac egen_case :=
  let H := fresh "H" in
  gen_case H.

Ltac lr_case :=
  match goal with
  | [ _: match ?X with
         | left _ => _
         | right _ => _ end = _ |- _ ] =>
      destruct X
  end; gen_contra; try gen_inv.

Ltac reserve_instr_inv :=
  match goal with
  | [ H: reserve_instr ?s = RTLgen.OK ?n ?s' ?pf |- _ ] => inv H
  end.

Ltac state_incr_inv :=
  match goal with
  | [ H: state_incr ?s1 ?s2 |- _ ] => inv H
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
  forall vote,
    is_actual_type ty ->
    maj_vote_of_typ ty r1 r2 r3 = Some vote ->
    c ! pc = Some (vote succ) ->
    maj_voteR c ty r1 r2 r3 pc succ.

Inductive maj_vote_regsR c re rm : list reg -> node -> node -> Prop :=
| maj_vote_regs_nil :
  forall pc,
    maj_vote_regsR c re rm nil pc pc
| maj_vote_regs_cons :
  forall r1 r2 r3 args pc succ n,
    rm # r1 = (r2, r3) ->
    maj_vote_regsR c re rm args pc n ->
    maj_voteR c (re r1) r1 r2 r3 n succ ->
    maj_vote_regsR c re rm (r1 :: args) pc succ.

Inductive smoveR
  (c : code) (ty : typ) (src dst1 dst2 : reg) (pc succ : node): Prop :=
| smove_1 :
  forall n mov1 mov2,
    smove ty src dst1 = Some mov1 ->
    smove ty src dst2 = Some mov2 ->
    c ! pc = Some (mov1 n) ->
    c ! n = Some (mov2 succ) ->
    smoveR c ty src dst1 dst2 pc succ.

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
  forall sig fn args res1 res2 res3 succ n1 n2,
    rm !! res1 = (res2, res3) ->
    maj_vote_regsR c re rm (regs_of_fn fn ++ args) pc n1 ->
    c ! n1 = Some (Icall sig fn args res1 n2) ->
    smoveR c (re res1) res1 res2 res3 n2 succ ->
    match_instr re rm pc c (Icall sig fn args res1 succ)
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
  forall param params entrypoint n p r2 r3,
    rm !! param = (r2, r3) ->
    smoveR c (re param) param r2 r3 entrypoint n ->
    match_entrypoint re rm c params n p ->
    match_entrypoint re rm c (param :: params) entrypoint p.

Inductive match_function re rm : function -> function -> Prop :=
| match_fun : forall sig params stacksize c c' entrypoint entrypoint',
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
       |})
      ({|
          fn_sig := sig
        ; fn_params := params
        ; fn_stacksize := stacksize
        ; fn_code := c'
        ; fn_entrypoint := entrypoint'
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
  econstructor; eauto.
  rewrite Hpc; eauto.
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
  - inv H5.
    destruct (H1 n) as [?|Hn]; try congruence.
    destruct (H1 n1) as [?|Hn1]; try congruence.
    destruct (H1 n2) as [?|Hn2]; try congruence.
    (* destruct (H1 n3) as [?|Hn3]; try congruence. *)
    econstructor; eauto.
    + eapply state_incr_maj_vote_regsR; eauto.
    + rewrite Hn1; eauto.
    + econstructor; eauto.
      * rewrite Hn2; eauto.
      * rewrite Hn; auto.
Qed.

Lemma maj_vote_of_typ_is_actual_type ty r1 r2 r3 i :
  maj_vote_of_typ ty r1 r2 r3 = Some i ->
  is_actual_type ty.
Proof.
  destruct ty; simpl; intro Hmaj; auto; inv Hmaj.
Qed.

Lemma maj_vote_maj_voteR re r1 r2 r3 pc succ s s' pf :
  pc < s.(st_nextnode) ->
  maj_vote re r1 r2 r3 pc s = RTLgen.OK succ s' pf ->
  maj_voteR s'.(st_code) (re r1) r1 r2 r3 pc succ.
Proof.
  unfold maj_vote, RTLgen.bind; simpl; intros Hlt Hmaj.
  destruct (maj_vote_of_typ (re r1) r1 r2 r3) eqn:Hty.
  2: { inv Hmaj. }
  repeat egen_case.
  unfold update_instr in *; simpl in *.
  lr_case; try congruence; lr_case.
  simpl in *.
  econstructor; eauto.
  2: { rewrite PTree.gss; reflexivity. }
  eapply maj_vote_of_typ_is_actual_type; eauto.
Qed.

Lemma maj_vote_succ_lt_nextnode re r1 r2 r3 pc succ s s' pf :
  pc < s.(st_nextnode) ->
  maj_vote re r1 r2 r3 pc s = RTLgen.OK succ s' pf ->
  succ < s'.(st_nextnode).
Proof.
  unfold maj_vote, RTLgen.bind; simpl; intros Hlt Hmaj.
  destruct (maj_vote_of_typ (re r1) r1 r2 r3) eqn:Hty.
  2: { inv Hmaj. }
  repeat egen_case.
  unfold update_instr in *; simpl in *.
  lr_case; try congruence; lr_case.
  simpl in *; lia.
Qed.

Lemma maj_vote_regs_succ_lt_nextnode re rm regs pc succ s s' pf :
  pc < s.(st_nextnode) ->
  maj_vote_regs re rm regs pc s = RTLgen.OK succ s' pf ->
  succ < s'.(st_nextnode).
Proof.
  revert pc succ s s' pf.
  induction regs; intros pc n s s' pf Hlt Hmaj; inv Hmaj; auto.
  unfold RTLgen.bind in H0.
  gen_case Hmaj.
  destruct (rm # a) eqn:Ha.
  egen_case.
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
  gen_case H0.
  destruct (rm # a) eqn:Ha.
  destruct (maj_vote re a r r0 n s'0) eqn:Hm; gen_contra; gen_inv.
  pose proof H0 as H0'.
  apply maj_vote_regs_succ_lt_nextnode in H0'; auto.
  apply IHregs in H0; auto.
  econstructor; eauto.
  - eapply state_incr_maj_vote_regsR.
    2: { eauto. }
    clear Hm; inv s1; auto.
  - eapply maj_vote_maj_voteR; eauto.
Qed.

Lemma maj_voteR_ptree_set c ty r1 r2 r3 pc succ n i :
  c ! n = None ->
  maj_voteR c ty r1 r2 r3 pc succ ->
  maj_voteR (PTree.set n i c) ty r1 r2 r3 pc succ.
Proof.
  intros Hc Hmaj; inv Hmaj.
  econstructor; eauto.
  - destruct (DecidableTypeEx.Positive_as_DT.eq_dec n pc);
      subst; try congruence.
    rewrite PTree.gso; eauto.
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
  p i (l : list (positive * instruction)) re rm s s' pf u :
  p < s.(st_nextnode) ->
  In (p, i) l ->
  iterM (transf_instr re rm) l s = RTLgen.OK u s' pf ->
  match_instr re rm p (st_code s') i.
Proof.
  revert s s' pf; induction l; simpl; intros s s' pf Hlt Hin Htransf.
  { contradiction. }
  unfold RTLgen.bind in Htransf.
  gen_case Hiter.
  gen_case Htransf'.
  destruct Hin as [?|Hin]; subst.
  - simpl in Htransf'.
    destruct i.
    
    (* Inop *)
    + unfold update_instr in Htransf'.
      repeat lr_case.
      simpl; constructor; rewrite PTree.gss; reflexivity.

    (* Iop *)
    + unfold RTLgen.bind in Htransf'.
      repeat egen_case.
      unfold update_instr in *.
      repeat lr_case.
      inv H; inv H1.
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
    + unfold RTLgen.bind in Htransf'; simpl in Htransf'.
      repeat egen_case.
      unfold update_instr in *.
      repeat lr_case.
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
    + unfold RTLgen.bind in Htransf'; simpl in Htransf'.
      gen_case Hmaj.
      gen_case Hupd.
      apply maj_vote_regs_maj_vote_regsR in Hmaj.
      2: { clear Hiter; inv s0; unfold Ple in *; lia. }
      unfold update_instr in Hupd.
      repeat lr_case.
      simpl in *.
      inv s1; inv s3; inv pf; simpl in *; unfold Ple in *.
      destruct (rm # r) eqn:Hrmr; simpl in *.
      econstructor.
      { eauto. }
      2: { rewrite PTree.gss; reflexivity. }
      apply maj_vote_regsR_ptree_set; auto.

    (* Icall *)
    + unfold RTLgen.bind in Htransf'; simpl in Htransf'.
      repeat egen_case.
      unfold copy_to_shadows in H0.
      destruct (rm # r) eqn:Hrmr.
      unfold RTLgen.bind in H0.
      unfold error in *.
      destruct (smove (re r) r r0) eqn:Hmov1; gen_contra.
      destruct (smove (re r) r r1) eqn:Hmov2; gen_contra.
      repeat egen_case.
      unfold update_instr in *.
      repeat lr_case.
      simpl in *.
      assert (p < st_nextnode s'0).
      { clear Hiter; inv s0; simpl in *; unfold Ple in *; lia. }
      assert (Hn0: n0 < s'1.(st_nextnode)).
      { eapply maj_vote_regs_succ_lt_nextnode.
        2: { eauto. }
        auto. }
      apply maj_vote_regs_maj_vote_regsR in H.
      2: { clear Hiter; inv s0; unfold Ple in *; lia. }
      reserve_instr_inv.
      simpl in *.
      repeat state_incr_inv.
      simpl in *; unfold Ple in *.
      econstructor; eauto.
      * repeat apply maj_vote_regsR_ptree_set; eauto.
      * rewrite PTree.gss; reflexivity.
      * econstructor; eauto.
        { rewrite 2!PTree.gso; try lia.
          rewrite PTree.gss; reflexivity. }
        { rewrite PTree.gso; try lia.
          rewrite PTree.gss; reflexivity. }
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
  - unfold RTLgen.bind in Htransf'.
    destruct u, u0.
    assert (H: match_instr re rm p (st_code s'0) i).
    { eapply IHl; eauto. }
    eapply state_incr_match_instr; eauto.
Admitted.

Lemma transf_code_code_matches (c : code) (re : regenv) rm s s' pf u :
  (forall p i, c ! p = Some i -> p < st_nextnode s) ->
  transf_code re rm c s = RTLgen.OK u s' pf ->
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

Lemma lt_nextnode_init_state p i sig params stacksize c entrypoint :
  c ! p = Some i ->
  p < st_nextnode (init_state {| fn_sig := sig
                               ; fn_params := params
                               ; fn_stacksize := stacksize
                               ; fn_code := c
                               ; fn_entrypoint := entrypoint
                              |}).
Proof. intro Hget; eapply lt_ptree_fold_max; eauto. Qed.

Lemma lt_nextnode_init_state' p i f :
  (fn_code f) ! p = Some i ->
  p < st_nextnode (init_state f).
Proof. intro Hget; eapply lt_ptree_fold_max; eauto. Qed.

Lemma transf_fun'_code_matches rm (f tf : function) (re : regenv) s pf :
  transf_fun' re f = OK tf ->
  replication_map f (init_state f) = RTLgen.OK rm s pf ->
  match_code re rm f.(fn_code) tf.(fn_code).
Proof.
  unfold transf_fun'.
  destruct (transf_fun re f (init_state f)) eqn:Hf; intros H Hrm; inv H; simpl.
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

Inductive copy_paramsR re rm c : list reg -> node -> node -> Prop :=
| copy_params_nil :
  forall n,
    copy_paramsR re rm c [] n n
| copy_params_cons :
  forall param params succ n p r2 r3,
    rm # param = (r2, r3) ->
    (* c ! n = Some (Iop Omove [param] r2 m) -> *)
    (* c ! m = Some (Iop Omove [param] r3 p) -> *)
    (* c ! n = Some (smove (re param) param r2 m) -> *)
    (* c ! m = Some (smove (re param) param r3 p) -> *)
    smoveR c (re param) param r2 r3 n p ->
    copy_paramsR re rm c params p succ ->
    copy_paramsR re rm c (param :: params) n succ.

Lemma copy_params_copy_paramsR re rm params n succ s0 s1 pf c :
  copy_params re rm params succ s0 = RTLgen.OK n s1 pf ->
  (forall p i, s1.(st_code) ! p = Some i -> c ! p = Some i) ->
  copy_paramsR re rm c params n succ.
Proof.
  revert pf.
  revert s0 s1 n succ.
  induction params; simpl; intros s0 s1 n succ pf Hcopy Hc; inv Hcopy.
  { constructor. }
  unfold RTLgen.bind in H0; simpl in H0.
  repeat egen_case.
  (* gen_case H1; inv H0. *)
  (* gen_case H3; inv H2. *)
  (* gen_case H2; inv H3. *)
  (* gen_case H3; inv H2. *)
  unfold copy_to_shadows in H1.
  destruct (rm # a) eqn:Ha.
  unfold RTLgen.bind in H1; simpl in H1.
  unfold error in H1.
  destruct (smove (re a) a r) eqn:Hmov1; gen_contra.
  destruct (smove (re a) a r0) eqn:Hmov2; gen_contra.
  repeat egen_case.
  (* gen_case H4; inv H3. *)
  (* gen_case H3; inv H4. *)
  (* gen_case H4; inv H0. *)
  unfold update_instr in *.
  (* simpl in *. *)
  repeat lr_case.
  (* lr_case; try congruence. *)
  (* lr_case; inv H4. *)
  (* lr_case; try congruence. *)
  (* lr_case; inv H3. *)
  simpl in *.
  repeat state_incr_inv.
  (* inv s7; inv s5; inv s6; inv s3; inv s4; inv s2; inv pf. *)
  simpl in *; unfold Ple in *.
  econstructor; eauto.
  - econstructor; eauto; apply Hc.
    + rewrite PTree.gso; try lia.
      rewrite PTree.gss; eauto.
    + rewrite PTree.gss; eauto.
  - eapply IHparams; eauto.
    intros p' instr Hget.
    apply Hc.
    specialize (H17 p'); destruct H17; congruence.
Qed.

Lemma copy_paramsR_match_entrypoint re rm params entrypoint n c :
  copy_paramsR re rm c params n entrypoint ->
  match_entrypoint re rm c params n entrypoint.
Proof.
  revert entrypoint n.
  induction params; simpl; intros entrypoint n Hcopy; inv Hcopy.
  { constructor. }
  econstructor; eauto.
Qed.

Lemma copy_params_match_entrypoint re rm params entrypoint s0 s1 pf1 n :
  copy_params re rm params entrypoint s0 = RTLgen.OK n s1 pf1 ->
  match_entrypoint re rm s1.(st_code) params n entrypoint.
Proof.
  intros Hcopy.
  apply copy_paramsR_match_entrypoint.
  eapply copy_params_copy_paramsR; eauto.
Qed.

Lemma match_entrypoint_monotone re rm c1 c2 params n entrypoint :
  match_entrypoint re rm c1 params n entrypoint ->
  (forall p i, c1 ! p = Some i -> c2 ! p = Some i) ->
  match_entrypoint re rm c2 params n entrypoint.
Proof.
  revert n entrypoint; induction params;
    simpl; intros n entrypoint Hmatch Hle; inv Hmatch.
  { constructor. }
  econstructor; eauto.
  inv H2; econstructor; eauto.
Qed.

Lemma transf_function_match_fundef (f tf : fundef) :
  transf_fundef f = OK tf ->
  match_fundef f tf.
Proof.
  intro Htransf.
  destruct f; simpl in Htransf.
  - monadInv Htransf.
    monadInv EQ.
    rename x0 into re.
    unfold transf_fun' in EQ1.
    egen_case; try congruence.
    inv EQ1.
    unfold transf_fun in H.
    unfold RTLgen.bind in H.
    repeat egen_case.
    apply transf_code_code_matches in H1.
    inv H3.
    2: {
      intros p i Hpi.
      apply lt_nextnode_init_state' in Hpi.
      clear H0 H H1.
      repeat state_incr_inv.
      unfold Ple in *.
      simpl in *.
      lia. }
    destruct f.
    simpl in *.
    econstructor.
    constructor; eauto.
    apply copy_params_match_entrypoint in H.
    eapply match_entrypoint_monotone; eauto.
    clear H0 H H1.
    repeat state_incr_inv.
    unfold Ple in *.
    simpl in *.
    intros p i Hpi.
    destruct (H7 p); congruence.
  - inv Htransf; constructor.
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

(* Inductive match_stackframe (prog : program) : stackframe -> stackframe -> Prop := *)
Inductive match_stackframe : stackframe -> stackframe -> Prop :=
| match_frame :
  forall re rm res f tf sp pc rs trs n1 n2 res2 res3 mov1 mov2
    (* (GENV: exists (v : val), Genv.find_funct (Genv.globalenv prog) v = Some (Internal f)) *)
    (* (GENV: exists i, In (i, Gfun (Internal f)) (prog_defs prog)) *)
    (FUN : match_function re rm f tf)
    (INV : rm_inv f.(fn_code) rm rs trs)
    (RM: rm # res = (res2, res3)),
    (* (Hn1: tf.(fn_code) ! n1 = Some (Iop Omove [res] res2 n2)) *)
    (* (Hn2: tf.(fn_code) ! n2 = Some (Iop Omove [res] res3 pc)), *)
    smove (re res) res res2 = Some mov1 ->
    smove (re res) res res3 = Some mov2 ->
    tf.(fn_code) ! n1 = Some (mov1 n2) ->
    tf.(fn_code) ! n2 = Some (mov2 pc) ->
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

(* Definition valid_pointer m b ofs : Prop := *)
(*   Mem.valid_pointer m b (Ptrofs.unsigned ofs) *)
(*   || Mem.valid_pointer m b (Ptrofs.unsigned ofs - 1) = true. *)

(* TODO: add invariant that all functions in the global environment
   (for the source program) are well-typed. Shouldn't need to do type
   preservation stuff if we just do that. *)
(* Inductive match_states (prog : program) : state -> state -> Prop := *)
Inductive match_states : state -> state -> Prop :=
| match_regular_states :
  forall stk tstk f tf sp pc rs rs' m re rm
    (* Well-typed *)
    (WT_STK: wt_stackframes stk (fn_sig f))
    (WT_FN: wt_function f re)
    (WT_RS: wt_regset re rs)
    (* Match *)
    (* (GENV: exists (v : val), Genv.find_funct (Genv.globalenv prog) v = Some (Internal f)) *)
    (* (GENV: exists i, In (i, Gfun (Internal f)) (prog_defs prog)) *)
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
    (* (WT_FN : forall fd, f = Internal fd -> exists re, wt_function fd re) *)
    (* (WT_ARGS : Val.has_type_list args (proj_sig_args (funsig f))) *)
    (* Match *)
    (* (GENV: exists (v : val), Genv.find_funct (Genv.globalenv prog) v = Some f) *)
    (* (GENV: exists i, In (i, Gfun f) (prog_defs prog)) *)
    (STACKS : list_forall2 match_stackframe stk tstk)
    (FUN : match_fundef f tf),
    match_states (Callstate stk f args m) (Callstate tstk tf args m)
| match_return_states :
  forall sig stk tstk v m
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
