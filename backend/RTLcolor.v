Require Import
  AST
  Errors
  Coqlib
  Events
  (* Globalenvs *)
  Integers
  List
  Maps
  Registers
  RTL
  Values
.

Definition optionP {A : Type} (pred : A -> Prop) (o : option A) : Prop :=
  match o with
  | None => True
  | Some a => pred a
  end.

(** Color is position dependent. White is a temporary color that gets
    reset to red after a use (or pink then red in the case of
    smoves). So, red registers are variously red or white/pink
    throughout the function, but green and blue registers stay green
    and blue respectively. *)

Inductive color : Type :=
| Red
| Green
| Blue
| White
| Pink
.

Lemma color_eq: forall (c1 c2 : color), { c1 = c2 } + { c1 <> c2 }.
Proof. decide equality. Defined.

Definition eqb (c1 c2 : color) : bool :=
  match c1, c2 with
  | Red, Red => true
  | Green, Green => true
  | Blue, Blue => true
  | White, White => true
  | Pink, Pink => true
  | _, _ => false
  end.

Declare Scope color_scope.

Infix "=?" := eqb (at level 70) : color_scope.

Local Open Scope color_scope.

Lemma eqb_spec (c1 c2 : color) : reflect (c1 = c2) (c1 =? c2).
Proof. destruct c1, c2; simpl; try left; auto; right; congruence. Qed.

Definition eqb' (oc1 oc2 : option color) : bool :=
  match oc1, oc2 with
  | Some c1, Some c2 => c1 =? c2
  | None, None => true
  | _, _ => false
  end.

Lemma eqb'_spec (oc1 oc2 : option color) : reflect (oc1 = oc2) (eqb' oc1 oc2).
Proof.
  destruct oc1, oc2; try (right; congruence); simpl.
  - destruct (eqb_spec c c0); subst.
    + left; reflexivity.
    + right; intro HC; inv HC; congruence.
  - left; reflexivity.
Qed.

Lemma eqb'_sound (oc1 oc2 : option color) :
  eqb' oc1 oc2 = true ->
  oc1 = oc2.
Proof. destruct (eqb'_spec oc1 oc2); congruence. Qed.

(* Inductive is_basic_color : color -> Prop := *)
(* | is_basic_color_red : is_basic_color Red *)
(* | is_basic_color_green : is_basic_color Green *)
(* | is_basic_color_blue : is_basic_color Blue *)
(* . *)

(* Inductive is_basic : option color -> Prop := *)
(* | is_basic_c : forall c, *)
(*     is_basic_color c -> *)
(*     is_basic (Some c). *)

Inductive is_basic : color -> Prop :=
| is_basic_red : is_basic Red
| is_basic_green : is_basic Green
| is_basic_blue : is_basic Blue.

Inductive is_basic' : option color -> Prop :=
| is_basic'_basic : forall c,
    is_basic c ->
    is_basic' (Some c).

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

(* Inductive is_basic : option color -> Prop := *)
(* | is_basic_red : is_basic (Some Red) *)
(* | is_basic_green : is_basic (Some Green) *)
(* | is_basic_blue : is_basic (Some Blue). *)

(* Inductive is_red : option color -> Prop := *)
(* | is_red_red : is_red (Some Red). *)

(* Inductive is_clear : option color -> Prop := *)
(* | is_clear_clear : is_clear (Some Clear). *)

(* Definition has_color (col : reg -> option color) (r : reg) (c : color) : Prop := *)
(*   match col r with *)
(*   | None => False *)
(*   | Some c' => c = c' *)
(*   end. *)

(* Inductive is_color : option color -> color -> Prop := *)
(* | is_color_c : forall c, *)
(*     is_color (Some c) c. *)

(* Definition is_red (c : option color) : Prop := *)
(*   is_color c Red. *)

(* Definition is_clear (c : option color) : Prop := *)
(*   is_color c Clear. *)

Definition is_color (x : option color) (c : color) : Prop := x = Some c.
Notation is_white x := (is_color x White).
Notation is_pink x := (is_color x Pink).
Notation is_red x := (is_color x Red).
Notation is_green x := (is_color x Green).
Notation is_blue x := (is_color x Blue).

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

Section wc.
  Variable col : node -> reg -> option color.

  (** An instruction is well-colored wrt. coloring [col]. *)
  Inductive wc_instruction (pc : node) : instruction -> Prop :=
  | wc_Inop : forall succ,
      (forall r c, col pc r = Some c -> col succ r = Some c) ->
      wc_instruction pc (Inop succ)
  | wc_Iop_safe : forall op args res succ,
      ~ is_unsafe op ->
      is_basic' (col succ res) ->
      Forall (fun arg => col pc arg = col succ res) args ->
      (forall r c, r <> res -> col pc r = Some c -> col succ r = Some c) ->
      wc_instruction pc (Iop op args res succ)
  | wc_Iop_unsafe : forall op args res succ,
      is_unsafe op ->
      (* TODO: do we need to enforce is_red (col succ arg) here? and
         in similar cases below. It seems like we don't need to. *)
      Forall (fun arg => is_white (col pc arg)) args ->
      is_white (col succ res) ->
      (forall r c, ~ In r args -> r <> res ->
              is_color (col pc r) c -> is_color (col succ r) c) ->
      wc_instruction pc (Iop op args res succ)
  | wc_Iload : forall chunk addr args res succ,
      Forall (fun arg => is_white (col pc arg)) args ->
      is_white (col succ res) ->
      (forall r c, ~ In r args -> r <> res ->
              is_color (col pc r) c -> is_color (col succ r) c) ->
      wc_instruction pc (Iload chunk addr args res succ)
  | wc_Istore : forall chunk addr args src succ,
      is_white (col pc src) ->
      is_red (col succ src) ->
      Forall (fun arg => is_white (col pc arg)) args ->
      (forall r c, ~ In r args -> r <> src ->
              is_color (col pc r) c -> is_color (col succ r) c) ->
      wc_instruction pc (Istore chunk addr args src succ)
  | wc_Icall : forall sig fn args res succ,
      (forall r, fn = inl r -> is_white (col pc r)) ->
      Forall (fun arg => is_white (col pc arg)) args ->
      is_white (col succ res) ->
      (forall r c, ~ In r args -> (forall r', fn = inl r' -> r <> r') ->
              is_color (col pc r) c -> is_color (col succ r) c) ->
      wc_instruction pc (Icall sig fn args res succ)
  | wc_Itailcall : forall sig fn args,
      (forall r, fn = inl r -> is_white (col pc r)) ->
      Forall (fun arg => is_white (col pc arg)) args ->
      wc_instruction pc (Itailcall sig fn args)
  | wc_Ibuiltin_smove_white : forall ef arg res succ,
      is_smove_builtin ef ->
      is_white (col pc arg) ->
      is_pink (col succ arg) ->
      is_green (col succ res) ->
      (forall r c, r <> arg -> r <> res ->
              is_color (col pc r) c -> is_color (col succ r) c) ->
      wc_instruction pc (Ibuiltin ef (BA arg :: nil) (BR res) succ)
  | wc_Ibuiltin_smove_pink : forall ef arg res succ,
      is_smove_builtin ef ->
      is_pink (col pc arg) ->
      is_red (col succ arg) ->
      is_blue (col succ res) ->
      (forall r c, r <> arg -> r <> res ->
              is_color (col pc r) c -> is_color (col succ r) c) ->
      wc_instruction pc (Ibuiltin ef (BA arg :: nil) (BR res) succ)
  | wc_Ibuiltin_vote : forall ef arg1 arg2 arg3 res succ,
      is_vote_builtin ef ->
      is_red (col pc arg1) ->
      is_green (col pc arg2) ->
      is_blue (col pc arg3) ->
      is_white (col succ res) ->
      (forall r c, r <> res -> is_color (col pc r) c -> is_color (col succ r) c) ->
      wc_instruction pc (Ibuiltin ef (BA arg1 :: BA arg2 :: BA arg3 :: nil) (BR res) succ)
  | wc_Ibuiltin : forall ef args res succ,
      ~ is_smove_builtin ef ->
      ~ is_vote_builtin ef ->
      Forall (builtin_arg_forall (fun r => is_white (col pc r))) args ->
      builtin_res_forall (fun r => is_white (col succ r)) res ->
      (forall r c, ~ Exists (in_builtin_arg r) args ->
              is_color (col pc r) c -> is_color (col succ r) c) ->
      wc_instruction pc (Ibuiltin ef args res succ)
  | wc_Icond : forall cond args ifso ifnot,
      Forall (fun arg => is_white (col pc arg)) args ->
      wc_instruction pc (Icond cond args ifso ifnot)
  | wc_Ijumptable : forall arg tbl,
      is_white (col pc arg) ->
      wc_instruction pc (Ijumptable arg tbl)
  | wc_Ireturn : forall or,
      optionP (fun r => is_white (col pc r)) or ->
      wc_instruction pc (Ireturn or).

  Definition wc_code (c : code) : Prop :=
    forall pc i, c ! pc = Some i -> wc_instruction pc i.

  Record wc_function (f : function) : Prop :=
    mk_wc_function {
        wc_fn_params : Forall (fun param => col f.(fn_entrypoint) param = Some Red) f.(fn_params);
        wc_fn_code : wc_code f.(fn_code)
      }.

  (* TODO: extra conditions on the coloring, enforcing transfer
     consistency across instructions. Maybe a coloring validation pass
     before the color checker, so those extra conditions are an input
     assumption about [col] here. *)

End wc.

(* Inductive wc_fundef: fundef -> Prop := *)
(* | wc_fundef_external: forall ef, *)
(*     wc_fundef (External ef) *)
(* | wc_function_internal: forall col f, *)
(*     wc_function col f -> *)
(*     wc_fundef (Internal f). *)

Definition wc_program (p : program) : Prop :=
  forall i f, In (i, Gfun (Internal f)) (prog_defs p) -> exists col, wc_function col f.

Axiom infer_coloring : function -> option (node -> PTree.t color).

(* (* TODO: coloring validator. Might need coloring to be PMap or PTree *)
(*    instead of just a function, so that we can iterate over all the *)
(*    registers that are assigned a color at a given node. Probably will *)
(*    use PTree (the one that uses option). *) *)
(* Section coloring_validator. *)
(*   Variable col : node -> PTree.t color. *)
(*   (* Perform validation and transform into abstracted type (reg -> color) with  *) *)
(* End coloring_validator. *)
(* ^ why? I forget... *)

Definition inb (p : positive) (l : list positive) : bool :=
  existsb (fun x => Pos.eqb x p) l.

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

  Definition check_col_instr (pc : node) (instr : instruction) :=
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
          is_redb ((col succ) ! src) &&
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
    | Ibuiltin ef args res succ =>
        if is_smove_builtinb ef then
          match args, res with
          | BA arg :: nil, BR res' =>
              PTree_Properties.for_all (col pc)
                (fun r c => Pos.eqb r arg ||
                           Pos.eqb r res' ||
                             is_colorb ((col succ) ! r) c) &&
                if is_whiteb ((col pc) ! arg) then
                  is_pinkb ((col succ) ! arg) &&
                    is_greenb ((col succ) ! res')
                else
                  is_pinkb ((col pc) ! arg) &&
                    is_redb ((col succ) ! arg) &&
                    is_blueb ((col succ) ! res')
          | _, _ => false
          end
        else
          if is_vote_builtinb ef then
            match args, res with
            | BA arg1 :: BA arg2 :: BA arg3 :: nil, BR res' =>
                is_redb ((col pc) ! arg1) &&
                  is_greenb ((col pc) ! arg2) &&
                  is_blueb ((col pc) ! arg3) &&
                  is_whiteb ((col succ) ! res') &&
                  PTree_Properties.for_all (col pc)
                    (fun r c => Pos.eqb r res' || is_colorb ((col succ) ! r) c)
            | _, _ => false
            end
          else
            forallb (builtin_arg_forallb (fun r => is_whiteb ((col pc) ! r))) args &&
              builtin_res_forallb (fun r => is_whiteb ((col succ) ! r)) res &&
              PTree_Properties.for_all (col pc)
                (fun r c => existsb (in_builtin_argb r) args || is_colorb ((col succ) ! r) c)
    (* | Icond cond args ifso ifnot => *)
    (*     forallb (fun arg => is_whiteb ((col pc) ! arg)) args && *)
    | _ =>
        false
    end.

  (* | wc_Icond : forall cond args ifso ifnot, *)
  (*     Forall (fun arg => is_white (col pc arg)) args -> *)
  (*     wc_instruction pc (Icond cond args ifso ifnot) *)
  (* | wc_Ijumptable : forall arg tbl, *)
  (*     is_white (col pc arg) -> *)
  (*     wc_instruction pc (Ijumptable arg tbl) *)
  (* | wc_Ireturn : forall or, *)
  (*     optionP (fun r => is_white (col pc r)) or -> *)
  (*     wc_instruction pc (Ireturn or). *)
  
  Definition check_col_function (f : function) : bool :=
    forallb (fun param => is_colorb ((col f.(fn_entrypoint)) ! param) Red) f.(fn_params) &&
      PTree_Properties.for_all f.(fn_code) (fun pc instr => check_col_instr pc instr).

  Lemma not_in_inb x l :
    ~ In x l ->
    inb x l = true ->
    False.
  Proof.
    intros Hnotin Hinb.
    apply existsb_exists in Hinb.
    destruct Hinb as (y & Hin & Heq).
    apply Peqb_true_eq in Heq; subst; congruence.
  Qed.

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
      destruct_andb Hcheck Hargs.
      destruct_andb Hwhite Hred.
      rewrite forallb_forall in Hargs.
      rewrite PTree_Properties.for_all_correct in Hpres.
      constructor.
      + apply is_colorb_sound; auto.
      + apply is_colorb_sound; auto.
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
       + intros x c Hnotin Hneq Hx.
         apply Hpres in Hx.
         destruct_orb Hin Hx.
         { destruct_orb Hin Hx.
           - exfalso; eapply not_in_inb; eauto.
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
          intros r c Hnotex Hrc; apply Hpres in Hrc.
          destruct_orb H H.
          { apply Forall_Exists_neg in Hnotex.
            rewrite Forall_forall in Hnotex.
            apply existsb_exists in H.
            destruct H as (barg & Hin & Hin').
            apply Hnotex in Hin.
            apply in_builtin_argb_sound in Hin'; contradiction. }
          apply is_colorb_sound; auto.
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

  Theorem check_col_function_iff (f : function) :
    check_col_function f = true <-> wc_function (fun pc r => (col pc) ! r) f.
  Proof.
    split.
    - apply check_col_function_sound.
    - apply check_col_function_complete.
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
