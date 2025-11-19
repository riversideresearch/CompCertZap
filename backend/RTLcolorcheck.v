Require Import
  AST
  Errors
  Coqlib
  Events
  Integers
  List
  Maps
  Registers
  RTL
  RTLcolor
  Values
.

Definition is_basicb (c : color) : bool :=
  match c with
  | Red | Green | Blue => true
  | _ => false
  end.

Definition is_basicb' (oc : option color) : bool :=
  match oc with
  | Some c => is_basicb c
  | None => false
  end.

Lemma is_basicb_spec (c : color) :
  reflect (is_basic c) (is_basicb c).
Proof. destruct c; try (left; constructor); right; intro HC; inv HC. Qed.

Lemma is_basicb'_spec (oc : option color) :
  reflect (is_basic' oc) (is_basicb' oc).
Proof.
  destruct oc; simpl.
  - destruct (is_basicb_spec c).
    + left; constructor; assumption.
    + right; intro HC; inv HC; congruence.
  - right; intro HC; inv HC.
Qed.

Lemma is_basicb'_sound (oc : option color) :
  is_basicb' oc = true ->
  is_basic' oc.
Proof. destruct (is_basicb'_spec oc); congruence. Qed.

Local Open Scope color_scope.

Definition is_colorb (x : option color) (c : color) : bool :=
  match x with
  | Some c' => c' =? c
  | None => false
  end.
Notation is_whiteb x := (is_colorb x White).
Notation is_pinkb x := (is_colorb x Pink).
Notation is_redb x := (is_colorb x Red).
Notation is_greenb x := (is_colorb x Green).
Notation is_blueb x := (is_colorb x Blue).

Definition is_colorb_spec (x : option color) (c : color)
  : reflect (is_color x c) (is_colorb x c).
Proof.
  destruct x; simpl.
  - destruct (eqb_spec c0 c); subst.
    + left; reflexivity.
    + right; congruence.
  - right; congruence.
Qed.

Lemma is_colorb_sound (x : option color) (c : color) :
  is_colorb x c = true -> is_color x c.
Proof. destruct (is_colorb_spec x c); auto; congruence. Qed.

Parameter infer_coloring : function -> option (node -> PTree.t color).

Section color_checker.
  Variable col : node -> PTree.t color.

  (* Definition assert (b : bool) (err_msg : string) : res unit := *)
  (*   if b then OK tt else Error (msg err_msg). *)

  (* Definition check_col_instr (pc : node) (instr : instruction) : res unit := *)
  (*   match instr with *)
  (*   | Inop succ => *)
  (*       assert (PTree_Properties.for_all (col pc) (fun r c => is_colorb ((col succ) ! r) c)) *)
  (*         "" *)
  (*   | Iop op args res succ => *)
  (*       if is_unsafeb op then *)
  (*         bind (assert (forallb (fun arg => is_whiteb ((col pc) ! arg) && *)
  (*                                          is_redb ((col succ) ! arg)) args) *)
  (*                 "") *)
  (*           (fun _ => bind (assert (PTree_Properties.for_all (col pc) *)
  (*                                  (fun r c => inb r args || *)
  (*                                             Pos.eqb r res || *)
  (*                                               is_colorb ((col succ) ! r) c)) *)
  (*                          "") *)
  (*                    (fun _ => assert (is_whiteb ((col succ) ! res)) *)
  (*                             "")) *)
  (*       else *)
  (*         bind (assert (is_basicb' ((col pc) ! res)) "") *)
  (*           (fun _ => bind (assert (forallb (fun arg => (eqb' (col pc) ! arg) *)
  (*                                                   ((col succ) ! res)) args) *)
  (*                          "") *)
  (*                    (fun _ => assert (PTree_Properties.for_all (col pc) *)
  (*                                     (fun r c => is_colorb ((col succ) ! r) c)) *)
  (*                             "")) *)
  (*   | Iload chunk addr args res succ => *)
  (*       bind (assert (forallb (fun arg => is_whiteb ((col pc) ! arg) && *)
  (*                                        is_redb ((col succ) ! arg)) args) *)
  (*               "") *)
  (*         (fun _ => bind (assert (is_whiteb ((col succ) ! res)) "") *)
  (*                  (fun _ => assert (PTree_Properties.for_all (col pc) *)
  (*                                   (fun r c => inb r args || *)
  (*                                              Pos.eqb r res || *)
  (*                                                is_colorb ((col succ) ! r) c)) *)
  (*                           "")) *)
  (*   | _ => *)
  (*       assert false "TODO" *)
  (*   end. *)

  Definition check_col_instr (pc : node) (instr : instruction) : bool :=
    match instr with
    | Inop succ =>
        PTree_Properties.for_all (col pc) (fun r c => is_colorb ((col succ) ! r) c)
    | Iop op args res succ =>
        if is_unsafeb op then
          forallb (fun arg => is_whiteb ((col pc) ! arg)) args &&
            PTree_Properties.for_all (col pc)
              (fun r c => inb r args ||
                         Pos.eqb r res ||
                           is_colorb ((col succ) ! r) c) &&
            is_whiteb ((col succ) ! res)
        else
          is_basicb' ((col succ) ! res) &&
            forallb (fun arg => (eqb' (col pc) ! arg) ((col succ) ! res)) args &&
            PTree_Properties.for_all (col pc)
              (fun r c => Pos.eqb r res || is_colorb ((col succ) ! r) c)
    | Iload chunk addr args res succ =>
        forallb (fun arg => is_whiteb ((col pc) ! arg)) args &&
          is_whiteb ((col succ) ! res) &&
          PTree_Properties.for_all (col pc)
            (fun r c => inb r args ||
                       Pos.eqb r res ||
                         is_colorb ((col succ) ! r) c)
    | Istore chunk addr args src succ =>
        is_whiteb ((col pc) ! src) &&
          forallb (fun arg => is_whiteb ((col pc) ! arg)) args &&
          PTree_Properties.for_all (col pc)
            (fun r c => inb r args ||
                       Pos.eqb r src ||
                         is_colorb ((col succ) ! r) c)
    | Icall sig fn args res succ =>
        (match fn with
         | inl r => is_whiteb ((col pc) ! r)
         | inr _ => true
         end) &&
          forallb (fun arg => is_whiteb ((col pc) ! arg)) args &&
          is_whiteb ((col succ) ! res) &&
          PTree_Properties.for_all (col pc)
            (fun r c => inb r args ||
                       Pos.eqb r res ||
                       match fn with
                       | inl r' => Pos.eqb r' r
                       | inr _ => false
                       end ||
                         is_colorb ((col succ) ! r) c)
    | Itailcall sig fn args =>
        (match fn with
         | inl r => is_whiteb ((col pc) ! r)
         | inr _ => true
         end) &&
          forallb (fun arg => is_whiteb ((col pc) ! arg)) args
    | Ibuiltin ef bargs bres succ =>
        if is_smove_builtinb ef then
          match bargs, bres with
          | BA arg :: nil, BR res =>
              PTree_Properties.for_all (col pc)
                (fun r c => Pos.eqb r arg ||
                           Pos.eqb r res ||
                             is_colorb ((col succ) ! r) c) &&
                if is_whiteb ((col pc) ! arg) then
                  is_pinkb ((col succ) ! arg) &&
                    is_greenb ((col succ) ! res)
                else
                  is_pinkb ((col pc) ! arg) &&
                    is_redb ((col succ) ! arg) &&
                    is_blueb ((col succ) ! res)
          | _, _ => false
          end
        else
          if is_vote_builtinb ef then
            match bargs, bres with
            | BA arg1 :: BA arg2 :: BA arg3 :: nil, BR res =>
                is_redb ((col pc) ! arg1) &&
                  is_greenb ((col pc) ! arg2) &&
                  is_blueb ((col pc) ! arg3) &&
                  is_whiteb ((col succ) ! res) &&
                  PTree_Properties.for_all (col pc)
                    (fun r c => Pos.eqb r res || is_colorb ((col succ) ! r) c)
            | _, _ => false
            end
          else
            forallb (builtin_arg_forallb (fun r => is_whiteb ((col pc) ! r))) bargs &&
              builtin_res_forallb (fun r => is_whiteb ((col succ) ! r)) bres &&
              PTree_Properties.for_all (col pc)
                (fun r c => existsb (in_builtin_argb r) bargs ||
                           in_builtin_resb r bres ||
                             is_colorb ((col succ) ! r) c)
    | Icond cond args ifso ifnot =>
        forallb (fun arg => is_whiteb ((col pc) ! arg)) args &&
          PTree_Properties.for_all (col pc)
            (fun r c => inb r args || (is_colorb ((col ifso) ! r) c &&
                                     is_colorb ((col ifnot) ! r) c))
    | Ijumptable arg tbl =>
        is_whiteb ((col pc) ! arg) &&
          PTree_Properties.for_all (col pc)
            (fun r c => Pos.eqb r arg ||
                       forallb (fun succ => is_colorb ((col succ) ! r) c) tbl)
    | Ireturn or =>
        match or with
        | Some r => is_whiteb ((col pc) ! r)
        | None => true
        end
    end.
  
  Definition check_col_function (f : function) : bool :=
    forallb (fun param => is_colorb ((col f.(fn_entrypoint)) ! param) White) f.(fn_params) &&
      PTree_Properties.for_all f.(fn_code) (fun pc instr => check_col_instr pc instr).

  Ltac destruct_andb H1 H2 :=
    match goal with
    | [ H: _ && _ = true |- _] => apply andb_prop in H; destruct H as [H1 H2]
    end.

  Ltac destruct_orb H1 H2 :=
    match goal with
    | [ H: _ || _ = true |- _] => apply orb_prop in H; destruct H as [H1 | H2]
    end.

  Ltac exploit_in_andb :=
    match goal with
    | [ H: forall _, In _ _ -> _ && _ = true, Hin: In _ _ |- _ ] =>
        apply H in Hin; destruct (andb_prop _ _ Hin)
    end.

  Lemma check_col_instr_sound (pc : node) (instr : instruction) :
    check_col_instr pc instr = true ->
    wc_instruction (fun n r => (col n) ! r) pc instr.
  Proof.
    destruct instr; simpl; intro Hcheck; try congruence.
    - constructor.
      intros r c Hrc.
      rewrite PTree_Properties.for_all_correct in Hcheck.
      apply Hcheck in Hrc.
      apply is_colorb_sound; auto.
    - destruct (is_unsafeb_spec o).
      + destruct_andb Hargs Hn.
        destruct_andb Hargs Hpres.
        rewrite forallb_forall in Hargs.
        rewrite PTree_Properties.for_all_correct in Hpres.
        apply wc_Iop_unsafe; auto.
        * apply Forall_forall; intros x Hin; apply is_colorb_sound; auto.
        * apply is_colorb_sound; auto.
        * intros x c Hnotin Hnoteq Hx.
          apply Hpres in Hx.
          destruct_orb Hin Hx.
          { destruct_orb Hin Hx.
            - exfalso; eapply not_in_inb; eauto.
            - apply Peqb_true_eq in Hx; congruence. }
          apply is_colorb_sound; auto.
      + destruct_andb Hcheck Hpres.
        destruct_andb Hr Hargs.
        rewrite forallb_forall in Hargs.
        rewrite PTree_Properties.for_all_correct in Hpres.
        apply wc_Iop_safe; auto.
        * apply is_basicb'_sound; auto.
        * apply Forall_forall; intros x Hin.
          apply Hargs in Hin.
          apply eqb'_sound; auto.
        * intros x c Hneq Hx.
          apply Hpres in Hx.
          destruct_orb H H.
          { apply Peqb_true_eq in H; congruence. }
          apply is_colorb_sound; auto.
    - destruct_andb Hcheck Hpres.
      destruct_andb Hargs Hwhite.
      rewrite forallb_forall in Hargs.
      rewrite PTree_Properties.for_all_correct in Hpres.
      constructor.
      + apply Forall_forall; intros x Hin; apply is_colorb_sound; auto.
      + apply is_colorb_sound; auto.
      + intros x c Hnotin Hneq Hx.
        apply Hpres in Hx.
        destruct_orb Hin Hx.
        { destruct_orb Hin Hx.
          - exfalso; eapply not_in_inb; eauto.
          - apply Peqb_true_eq in Hx; congruence. }
        apply is_colorb_sound; auto.
    - destruct_andb Hcheck Hpres.
      destruct_andb Hwhite Hargs.
      (* destruct_andb Hwhite Hred. *)
      rewrite forallb_forall in Hargs.
      rewrite PTree_Properties.for_all_correct in Hpres.
      constructor.
      + apply is_colorb_sound; auto.
      (* + apply is_colorb_sound; auto. *)
      + apply Forall_forall; intros x Hin; apply is_colorb_sound; auto.
      + intros x c Hnotin Hneq Hx.
        apply Hpres in Hx.
        destruct_orb Hin Hx.
        { destruct_orb Hin Hx.
          - exfalso; eapply not_in_inb; eauto.
          - apply Peqb_true_eq in Hx; congruence. }
        apply is_colorb_sound; auto.
    -  destruct_andb Hcheck Hpres.
       destruct_andb Hcheck Hwhite.
       destruct_andb Hf Hargs.
       rewrite forallb_forall in Hargs.
       rewrite PTree_Properties.for_all_correct in Hpres.
       constructor.
       + intros x Hx; destruct s0; inv Hx; apply is_colorb_sound; auto.
       + apply Forall_forall; intros x Hin. apply is_colorb_sound; auto.
       + apply is_colorb_sound; auto.
       + intros x c Hnotin Hneqr Hneq Hx.
         apply Hpres in Hx.
         destruct_orb Hin Hx.
         { destruct_orb Hin Hx.
           - destruct_orb Hin Hx.
             { exfalso; eapply not_in_inb; eauto. }
             apply Pos.eqb_eq in Hx; subst; congruence.
           - destruct s0; try congruence.
             apply Pos.eqb_eq in Hx; subst.
             specialize (Hneq x eq_refl); congruence. }
         apply is_colorb_sound; auto.
    - destruct_andb Hf Hargs.
      rewrite forallb_forall in Hargs.
      constructor.
      + intros x Hx; destruct s0; inv Hx.
        apply is_colorb_sound; auto.
      + apply Forall_forall; intros x Hin.
        apply is_colorb_sound; auto.
    - destruct (is_smove_builtinb_spec e).
      + destruct l; try congruence.
        destruct b0; try congruence.
        destruct l; try congruence.
        destruct b; try congruence.
        destruct_andb Hpres Hargs.
        destruct (is_colorb_spec ((col pc) ! x) White).
        * (* white smove *)
          destruct (is_colorb_spec ((col n) ! x) Pink); simpl in *; try congruence.
          apply is_colorb_sound in Hargs; rename Hargs into Hgreen.
          rewrite PTree_Properties.for_all_correct in Hpres.
          apply wc_Ibuiltin_smove_white; auto.
          intros r c H0 H1 Hrc; apply Hpres in Hrc.
          destruct_orb H H.
          { destruct_orb H H; apply Pos.eqb_eq in H; congruence. }
          apply is_colorb_sound; auto.
        * (* pink smove *)
          destruct (is_colorb_spec ((col pc) ! x) Pink); simpl in *; try congruence.
          destruct (is_colorb_spec ((col n) ! x) Red); simpl in *; try congruence.
          destruct (is_colorb_spec ((col n) ! x0) Blue); simpl in *; try congruence.
          rewrite PTree_Properties.for_all_correct in Hpres.
          apply wc_Ibuiltin_smove_pink; auto.
          intros r c H0 H1 Hrc; apply Hpres in Hrc.
          destruct_orb H H.
          { destruct_orb H H; apply Pos.eqb_eq in H; congruence. }
          apply is_colorb_sound; auto.
      + destruct (is_vote_builtinb_spec e).
        * (* vote *)
          repeat match goal with
                 | [ H : match ?x with | _ => _ end = true |- _ ] =>
                     destruct x; try congruence
                 end.
          destruct_andb Hcheck Hpres.
          destruct_andb Hcheck Hwhite.
          destruct_andb Hcheck Hblue.
          destruct_andb Hred Hgreen.
          rewrite PTree_Properties.for_all_correct in Hpres.
          constructor; auto; try solve [apply is_colorb_sound; auto].
          intros r c Hneq Hrc; apply Hpres in Hrc.
          destruct_orb H H.
          { apply Pos.eqb_eq in H; congruence. }
          apply is_colorb_sound; auto.
        * (* other builtin *)
          destruct_andb Hcheck Hpres.
          destruct_andb Hargs Hres.
          rewrite forallb_forall in Hargs.
          rewrite PTree_Properties.for_all_correct in Hpres.
          constructor; auto.
          { apply Forall_forall.
            intros barg Hin.
            apply Hargs in Hin.
            apply builtin_arg_forallb_sound in Hin.
            eapply builtin_arg_forall_impl; eauto.
            intros; apply is_colorb_sound; auto. }
          { apply builtin_res_forallb_sound in Hres.
            eapply builtin_res_forall_impl; eauto.
            intros r Hwhite; apply is_colorb_sound; auto. }
          intros r c Hnotex Hnoteq Hrc; apply Hpres in Hrc.
          destruct_orb H H.
          { destruct_orb H H.
            - apply Forall_Exists_neg in Hnotex.
              rewrite Forall_forall in Hnotex.
              apply existsb_exists in H.
              destruct H as (barg & Hin & Hin').
              apply Hnotex in Hin.
              apply in_builtin_argb_sound in Hin'; contradiction.
            - apply in_builtin_resb_sound in H; contradiction. }
          apply is_colorb_sound; auto.
    - destruct_andb Hargs Hpres.
      rewrite forallb_forall in Hargs.
      rewrite PTree_Properties.for_all_correct in Hpres.
      constructor.
      + apply Forall_forall; intros x Hin.
        apply is_colorb_sound; auto.
      + intros r c' Hnotin Hrc; apply Hpres in Hrc.
        destruct_orb H H.
        * exfalso; eapply not_in_inb; eauto.
        * destruct_andb H H'.
          split; apply is_colorb_sound; auto.
    - destruct_andb Hwhite Hpres.
      rewrite PTree_Properties.for_all_correct in Hpres.
      constructor.
      + apply is_colorb_sound; auto.
      + intros x c Hneq Hxc; apply Hpres in Hxc.
        destruct_orb H H.
        * apply Pos.eqb_eq in H; congruence.
        * rewrite forallb_forall in H.
          apply Forall_forall; intros; apply is_colorb_sound; auto.
    - destruct o.
      + constructor; apply is_colorb_sound; auto.
      + constructor; apply I.
  Qed.

  Lemma check_col_function_sound (f : function) :
    check_col_function f = true ->
    wc_function (fun pc r => (col pc) ! r) f.
  Proof.
    destruct f; unfold check_col_function; simpl.
    intro H.
    apply andb_prop in H.
    destruct H as [Hparams Hcode].
    constructor; simpl.
    - rewrite forallb_forall in Hparams.
      apply Forall_forall.
      intros r Hin.
      apply Hparams in Hin.
      apply is_colorb_sound; auto.
    - rewrite PTree_Properties.for_all_correct in Hcode.
      intros pc instr Hpc.
      apply Hcode in Hpc.
      apply check_col_instr_sound; auto.
  Qed.

  (* Maybe not necessary but should be true anyway. *)
  Lemma check_col_function_complete (f : function) :
    wc_function (fun pc r => (col pc) ! r) f -> check_col_function f = true.
  Admitted.

  Theorem check_col_function_spec (f : function) :
    reflect (wc_function (fun pc r => (col pc) ! r) f) (check_col_function f).
  Proof.
    destruct (check_col_function f) eqn:check.
    - left; apply check_col_function_sound; auto.
    - right; intro Hwc.
      apply check_col_function_complete in Hwc; congruence.
  Qed.

End color_checker.

Definition check_function (f : function) : bool :=
  match infer_coloring f with
  | None => false
  | Some col => check_col_function col f
  end.

Lemma check_function_sound (f : function) :
  check_function f = true -> exists col, wc_function col f.
Proof.
  unfold check_function.
  destruct (infer_coloring f) as [col|]; try congruence.
  intro Hcheck; exists (fun pc r => (col pc) ! r).
  apply check_col_function_sound; assumption.
Qed.

(* check_function_complete not possible because we don't assume
   anything about infer_coloring. *)

Definition check_program (p : program) : bool :=
  forallb (fun def => match snd def with
                   | Gfun (Internal f) => check_function f
                   | _ => true
                   end) p.(prog_defs).

Lemma check_program_sound (p : program) :
  check_program p = true -> wc_program p.
Proof.
  intros Hp i f Hin.
  unfold check_program in Hp.
  rewrite forallb_forall in Hp.
  apply Hp in Hin.
  apply check_function_sound; auto.
Qed.
