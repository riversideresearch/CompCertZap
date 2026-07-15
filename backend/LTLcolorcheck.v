Require Import
  AST
  Builtins
  SharedFaultPolicy
  FaultPolicy
  CompCertZapUtils
  Errors
  Coqlib
  Events
  Integers
  LProofLiveness
  List
  Maps
  Registers
  LTL
  LTLcolor
  Values
  Locations
  Conventions1
.

Definition is_basicb (c : color) : bool :=
  match c with
  | Red | Green | Blue => true
  | _ => false
  end.

Lemma is_basicb_spec (c : color) :
  reflect (is_basic c) (is_basicb c).
Proof. destruct c; try (left; constructor); right; intro HC; inv HC. Qed.

Local Open Scope color_scope.


(*Definition proc_args_loc (args : list mreg) : Locset.t :=*)
(*  fold_left (fun acc el =>*)
(*    Locset.add (R el) acc*)
(*    ) args Locset.empty.*)

Fixpoint forallbi {A : Type} (f : A -> nat -> bool) (l : list A) (i : nat) : bool :=
  match l with
  | nil => true
  | a :: l0 => f a i && forallbi f l0 (Nat.succ i)
  end.

Parameter infer_coloring
  : function -> PMap.t (list (nat * Locset.t)) -> option (node -> nat -> loc -> color).
Locate Nat.succ.
Print Nat.succ.
Section color_checker.
  Variable lalive : PMap.t (list (nat * Locset.t)).
  Variable col : node -> nat -> loc -> color.


  Definition check_col_instr (pc : node) (instr : instruction) (plive : (nat * Locset.t)) : bool :=

    match instr with
    | Lop op args res =>
        if is_protectedb op then
          let loc_args := proc_args_loc args in
          forallb (fun arg => col pc (fst plive) (R arg) =? White) args  &&
          Locset.for_all (fun r => Locset.mem r loc_args ||
                        Locset.MF.eqb r (R res) ||
                        (col pc (fst plive) r =? col pc (Nat.succ (fst plive)) r)) (snd plive) &&
                        (col pc (Nat.succ (fst plive)) (R res) =? White)
        else
          is_basicb (col pc (Nat.succ (fst plive)) (R res)) &&
            forallb (fun arg => (col pc (fst plive) (R arg) =? col pc (Nat.succ (fst plive)) (R res)))
              args &&
            Locset.for_all (fun r => Locset.MF.eqb r (R res) || 
              (col pc (fst plive) r =? col pc (Nat.succ (fst plive)) r)) (snd plive)

    | Lload chunk addr args dst =>
        forallb (fun arg => col pc (fst plive) (R arg) =? White) args &&
          (col pc (Nat.succ (fst plive)) (R dst) =? White) &&
          let loc_args := proc_args_loc args in
          Locset.for_all (fun r => Locset.mem r loc_args ||
                  Locset.MF.eqb r (R dst) ||
                  (col pc (fst plive) r =? col pc (Nat.succ (fst plive)) r)) (snd plive)
    | Lstore chunk addr args src =>
        (col pc (fst plive) (R src) =? White) &&
        let loc_args := proc_args_loc args in
        Locset.for_all (fun r => Locset.mem r loc_args ||
                  Locset.MF.eqb r (R src) ||
                  (col pc (fst plive) r =? col pc (Nat.succ (fst plive)) r)) (snd plive)
    | Lcall sg ros =>
        let args := process_rargs (loc_arguments sg) in
        let res := loc_result sg in
        (match ros with
         | inl r => col pc (fst plive) (R r) =? White
         | inr _ => true
         end) &&
         Locset.for_all (fun arg => col pc (fst plive) arg =? White) args &&
         (match res with
          | One l => col pc (Nat.succ (fst plive)) (R l) =? White
          | Twolong l l' => (col pc (Nat.succ (fst plive)) (R l) =? White) &&
                            (col pc (Nat.succ (fst plive)) (R l') =? White)
          end) &&
          Locset.for_all (fun r => Locset.mem r args ||
                              (match res with
                               | One l => Locset.MF.eqb r (R l)
                               | Twolong l l' => (Locset.MF.eqb r (R l)) && (Locset.MF.eqb r (R l'))
                               end) ||
                               (match ros with
                                | inl r' => Locset.MF.eqb (R r') r
                                | inr _ => false
                                end) ||
                                (col pc (fst plive) r =? col pc (Nat.succ (fst plive)) r)) (snd plive)
    | Ltailcall sg ros =>
        let args := process_rargs (loc_arguments sg) in
        (match ros with
         | inl r => col pc (fst plive) (R r) =? White
         | inr _ => true
         end) &&
         Locset.for_all (fun arg => col pc (fst plive) arg =? White) args

    | Lbuiltin ef args res =>
        if is_green_smove_builtinb ef then
          match args, res with
          | BA arg :: nil, BR res' =>
              Locset.for_all (fun r => Locset.MF.eqb r arg ||
                          Locset.MF.eqb r (R res') ||
                          (col pc (fst plive) r =? col pc (Nat.succ (fst plive)) r)) (snd plive) &&
                  (col pc (fst plive) arg =? White) &&
                  (col pc (Nat.succ (fst plive)) arg =? Pink) &&
                  (col pc (Nat.succ (fst plive)) (R res') =? Green)
          | _, _ => false
          end
        else if is_blue_smove_builtinb ef then
          match args, res with
          | BA arg :: nil, BR res' =>
              Locset.for_all (fun r => Locset.MF.eqb r arg ||
                          Locset.MF.eqb r (R res') ||
                          (col pc (fst plive) r =? col pc (Nat.succ (fst plive)) r)) (snd plive) &&
                  (col pc (fst plive) arg =? Pink) &&
                  (col pc (Nat.succ (fst plive)) arg =? Red) &&
                  (col pc (Nat.succ (fst plive)) (R res') =? Blue)
          | _, _ => false
          end


        else if is_vote_builtinb ef then
          match args, res with
          | BA arg1 :: BA arg2 :: BA arg3 :: nil, BR res =>
              (col pc (fst plive) arg1 =? Red) &&
              (col pc (fst plive) arg2 =? Green) &&
              (col pc (fst plive) arg3 =? Blue) &&
              (col pc (Nat.succ (fst plive)) (R res) =? White) &&
              Locset.for_all (fun r =>
                    Locset.MF.eqb r (R res) || (col pc (fst plive) r =? col pc (Nat.succ (fst plive)) r))
                    (snd plive)
          | _, _ => false
          end
        else if builtin_can_replicate ef then
          match res with
          | BR res =>
              is_basicb (col pc (Nat.succ (fst plive)) (R res)) &&
              forallb (builtin_arg_forallb (fun r => col pc (fst plive) r =? 
                    col pc (Nat.succ (fst plive)) (R res))) args &&
              Locset.for_all (fun r =>
                    Locset.MF.eqb r (R res) ||
                    (col pc (fst plive) r =? col pc (Nat.succ (fst plive)) r)) (snd plive)
          | _ => false
          end
        else 
          forallb (builtin_arg_forallb (fun r => col pc (fst plive) r =? White)) args &&
            builtin_res_forallb (fun r => col pc (Nat.succ (fst plive)) (R r) =? White) res &&
            Locset.for_all (fun r =>
                    existsb (in_builtin_largb r) args ||
                    (match res with
                     | BR res' => Locset.MF.eqb r (R res')
                     | _ => false
                     end) ||
                     (col pc (fst plive) r =? col pc (Nat.succ (fst plive)) r)) (snd plive)
    | Lcond cond args s1 s2 =>
        let loc_args := proc_args_loc args in
        forallb (fun arg => col pc (fst plive) (R arg) =? White) args &&
        Locset.for_all (fun r => Locset.mem r loc_args ||
          (col pc (fst plive) r =? col s1 1 r) && (col pc (fst plive) r =? col s2 1 r)) (snd plive)
    | Ljumptable arg tbl =>
        (col pc (fst plive) (R arg) =? White) &&
          Locset.for_all (fun r => Locset.MF.eqb r (R arg) ||
              forallb (fun succ => col pc (fst plive) r =? col succ 1 r) tbl) (snd plive)
    | Lbranch s => true
    | Lreturn => true
                                    
    | _ => true
    end.

  Definition check_op_instr (pc : node) (instr : instruction) (op_plive : option (nat * Locset.t)) : bool :=
    match op_plive with
    | Some plive => check_col_instr pc instr plive
    | None => false
    end.


  Definition check_col_function (f: function) : bool :=
    let params := process_rargs (loc_arguments f.(fn_sig)) in
    Locset.for_all (fun param => col f.(fn_entrypoint) 1 param =? White) params &&
    PTree_Properties.for_all f.(fn_code) (fun pc instrs =>
      forallbi (fun inst i => check_op_instr pc inst (List.nth_error (PMap.get pc lalive) i))
       instrs O).

    Ltac destruct_andb H1 H2 :=
    match goal with
    | [ H: _ && _ = true |- _] => apply andb_prop in H; destruct H as [H1 H2]
    end.

      Ltac destruct_orb H1 H2 :=
    match goal with
    | [ H: _ || _ = true |- _] => apply orb_prop in H; destruct H as [H1 | H2]
    end.


      Ltac compat_bool_tac :=
    intros ?x ?y ?Hxy; subst; reflexivity.


Locate forallb_forall.
Locate Forall_forall.
Print Forall_forall.
Print Locset.
Print Locset.MF.
Print Loc.
Search (loc -> loc -> bool).
Print Locset.MSet.Raw.MX.eqb.
Print Locset.MSet.Raw.L.MO.
Print Locset.MSet.Raw.L.MO.eqb_alt.

Locate " + ".
Print sumbool.
Check sumbool.
Check Loc.eq.
Print Loc.diff.
Locate Loc.diff.
Locate Locset.Forall_forall.
Locate Locset.for_all_1.
Print Locset.for_all_1.
Locate Locset.mem.
Locate not_in_inb.
Print not_in_inb.
Print Locset.MSet.
Print Locset.MF.
Print Locset.X'.
Print Locset.E.
Print Locset.MSet.mem_spec.
Print typ_eq.
Print zeq.
Print Z.
Locate Z.
Print Loc.
Print Locset.MSet.Raw.L.MO.eqb.
Print Locset.MSet.Raw.L.MO.eq_dec.
  Lemma loc_in_not : forall l0 l1,
    Locset.X'.eq l0 l1 -> Locset.MF.eqb l0 l1 = true.
  Proof.
    intros. unfold Locset.MF.eqb. unfold Locset.X'.eq in H. rewrite H. 
    destruct (Locset.MF.eq_dec l1 l1) as [Heq | Hneq].
    - reflexivity.
    - exfalso. apply Hneq. reflexivity.
  Qed.

  Lemma loc_in_not2 : forall l0 l1,
    Locset.MSet.Raw.L.MO.eqb l0 l1 = true -> Locset.X'.eq l0 l1.
  Proof.
    intros l0 l1 H.
    unfold Locset.MSet.Raw.L.MO.eqb in H.
    destruct (Locset.MSet.Raw.L.MO.eq_dec l0 l1) as [Heq|Hneq].
    - assumption.
    - discriminate.
  Qed.


  Lemma lcheck_col_instr : forall (pc : node) (plive : (nat * Locset.t)) (instr : instruction),
    check_col_instr pc instr plive = true -> wc_instruction col pc plive instr.
  Proof.
    destruct instr; simpl; intro Hcheck.
    - destruct (is_protectedb_spec op).
      + (* protected *)
        destruct_andb Hcheck Hwhite.
        destruct_andb Hargs Hpres.
        rewrite forallb_forall in Hargs.
        apply Locset.for_all_2 in Hpres; [| compat_bool_tac].
        constructor; auto.
        * apply Forall_forall. intros. apply eqb_sound. apply Hargs. apply H.
        * intros l0 inl Hnotin Hneq.
          specialize (Hpres l0 inl). apply orb_prop in Hpres; destruct Hpres as [Hpres | Hpres].
          { apply orb_prop in Hpres; destruct Hpres as [Hpres | Hpres].
            ** exfalso. apply Hnotin. apply Locset.MF.mem_2. apply Hpres.
            ** exfalso. apply Hneq. apply loc_in_not2. apply Hpres.
               }
          ** apply eqb_sound. apply Hpres.
        * apply eqb_sound. apply Hwhite.
      + (* not protected *)
        destruct_andb Hcheck Hwhite.
        destruct_andb Hargs Hpres.
        rewrite forallb_forall in Hpres.
        apply Locset.for_all_2 in Hwhite; [| compat_bool_tac].
        apply wc_Lop_safe; auto.
        * destruct (is_basicb_spec (col pc (Nat.succ (fst plive)) (R res))); auto; congruence.
        * apply Forall_forall. intros. apply Hpres in H. apply eqb_sound. apply H.
        * intros l0 Hin.
          specialize (Hwhite l0 Hin). apply orb_prop in Hwhite; destruct Hwhite as [Hwhite | Hwhite].
          ** left. apply loc_in_not2. apply Hwhite.
          ** right. apply eqb_sound. apply Hwhite.
    - (* Lload *)
      destruct_andb Hcheck Hwhite.
      destruct_andb Hargs Hpres.
      rewrite forallb_forall in Hargs.
      apply Locset.for_all_2 in Hwhite; [| compat_bool_tac].
      apply wc_Lload; auto.
        * apply Forall_forall. intros. apply eqb_sound. apply Hargs in H. apply H.
        * apply eqb_sound. apply Hpres.
        * intros l0 Hin.
          specialize (Hwhite l0 Hin). apply orb_prop in Hwhite;
          destruct Hwhite as [Hwhite | Hwhite].
          { apply orb_prop in Hwhite; destruct Hwhite as [Hwhite | Hwhite].
            * left. apply Locset.MF.mem_2. apply Hwhite.
            * right. left. apply loc_in_not2. apply Hwhite.
          }
          right. right. apply eqb_sound. apply Hwhite.
    - admit.
    - admit.
    - (* Lstore *)
      destruct_andb Hcheck Hwhite.
      apply Locset.for_all_2 in Hwhite; [| compat_bool_tac].
      apply wc_Lstore; auto.
        * apply eqb_sound. apply Hcheck.
        * intros l0 Hin.
          specialize (Hwhite l0 Hin). apply orb_prop in Hwhite;
          destruct Hwhite as [Hwhite | Hwhite ].
          { apply orb_prop in Hwhite; destruct Hwhite as [Hwhite | Hwhite].
            * left. apply Locset.MF.mem_2. apply Hwhite.
            * right. left. apply loc_in_not2. apply Hwhite.
          }
          right. right. apply eqb_sound. apply Hwhite.
    - (* Lcall *)
      destruct_andb Hros HLloc.
      destruct_andb Hros Hres.
      destruct_andb Hros Hargs.
      apply Locset.for_all_2 in Hargs; [|compat_bool_tac].
      apply Locset.for_all_2 in HLloc; [|compat_bool_tac].
      apply wc_Lcall; auto.
        * intros. rewrite H in Hros. apply eqb_sound. apply Hros.
        * intros l0 Hin. specialize (Hargs l0 Hin). simpl in Hargs. apply eqb_sound. apply Hargs.
        * intros. left. intros. rewrite H in Hres. apply eqb_sound. apply Hres.
        * intros l0 Hin. specialize (HLloc l0 Hin). simpl in *.
          apply orb_prop in HLloc; destruct HLloc as [Hloc | Hcol].
          apply orb_prop in Hloc; destruct Hloc as [Hloc | HIros].
          apply orb_prop in Hloc; destruct Hloc as [Hloc | HIloc].
          ** left. apply Locset.MF.mem_2. apply Hloc.
          ** right. intros. left. intros. rewrite H in HIloc.
             apply loc_in_not2. apply HIloc.
          ** right. right. right. left. intros. rewrite H in HIros. apply loc_in_not2. apply HIros.
          ** right. right. right. right. apply eqb_sound. apply Hcol.
    - (* Ltailcall *)
      destruct_andb Hcheck HLoc.
      apply Locset.for_all_2 in HLoc; [|compat_bool_tac].
      apply wc_Ltailcall; auto.
        * intros. rewrite H in Hcheck. apply eqb_sound. apply Hcheck.
        * intros l0 Hin. specialize (HLoc l0 Hin). simpl in HLoc. apply eqb_sound.
          apply HLoc.
    - (* Lbuiltin *)
 



    
  Admitted.
  




 

End color_checker.



Definition check_function (f :function) : bool :=
  match LProofLiveness.analyze f with
  | Some live => 
      let alive := block_live_after f live in
      let lalive := block_inst_llafter f alive in
      match infer_coloring f lalive with
      | None => false
      | Some col => check_col_function lalive col f 
      end
  | None => false
  end.


Definition check_program (p :program) : bool :=
  forallb (fun def => match snd def with
                      | Gfun (Internal f) => check_function f
                      | _ => true
                      end) p.(prog_defs).

