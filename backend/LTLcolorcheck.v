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
Locate is_basic.
Definition is_basicb (c : color) : bool :=
  match c with
  | Green | Blue | Red  => true
  | _ => false
  end.

Lemma is_basicb_spec (c : color) :
  reflect (is_basic c) (is_basicb c).
Proof. destruct c; try (left; constructor); right; intro HC; inv HC. Qed.

Local Open Scope color_scope.



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
  (*Variable live : PMap.t (list Locset.t).*)
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
            Locset.for_all (fun r => 
            Locset.MF.eqb r (R res) || 
              (col pc (fst plive) r =? col pc (Nat.succ (fst plive)) r)) (snd plive)
    | Lgetstack sl ofs ty dst =>
        (match sl with
         | Local =>
            (col pc (Nat.succ (fst plive)) (R dst) =? col pc (fst plive) (S sl ofs ty))
         | Incoming =>
            (col pc (Nat.succ (fst plive)) (R dst) =? White)
         | _ => true
         end) &&
          Locset.for_all (fun r => Locset.MF.eqb r (S sl ofs ty) || Locset.MF.eqb r (R dst) ||
                          (col pc (fst plive) r =? col pc (Nat.succ (fst plive)) r)) (snd plive)

    | Lsetstack src sl ofs ty =>
        (match sl with
         | Local =>
            (col pc (Nat.succ (fst plive)) (S sl ofs ty) =? col pc (fst plive) (R src))
         | Outgoing =>
             (col pc (Nat.succ (fst plive)) (S sl ofs ty) =? White)
         | _ => true
         end) &&
        (if negb (Locset.mem (R src) (snd plive)) then
          (col pc (fst plive) (R src) =? col pc (Nat.succ (fst plive)) (R src))
        else 
          true
        ) &&
        Locset.for_all (fun r => Locset.MF.eqb r (S sl ofs ty) || Locset.MF.eqb r (R src) ||
                        (col pc (fst plive) r =? col pc (Nat.succ (fst plive)) r)) (snd plive)
      | Lsmove colr src dst =>
    if colr =? Green then
        (col pc (fst plive) src =? White) &&
        (col pc (Nat.succ (fst plive)) src =? Pink) &&
        (col pc (Nat.succ (fst plive))  dst =? Green) &&
        Locset.for_all (fun l => Locset.MF.eqb l src || Locset.MF.eqb l dst ||
              (col pc (fst plive) l =? col pc (Nat.succ (fst plive)) l)) (snd plive)
    else if colr =? Blue then
          (col pc (fst plive) src =? Pink) &&
          (col pc (Nat.succ (fst plive)) src =? Red) &&
          (col pc (Nat.succ (fst plive))  dst =? Blue) &&
          Locset.for_all (fun l => Locset.MF.eqb l src || Locset.MF.eqb l  dst ||

                (col pc (fst plive) l =? col pc (Nat.succ (fst plive)) l)) (snd plive)
    else if colr =? White then
        (col pc (fst plive) src =? White) &&
        (col pc (Nat.succ (fst plive)) dst =? White) &&
          Locset.for_all (fun l => Locset.MF.eqb l src || Locset.MF.eqb l  dst ||

                (col pc (fst plive) l =? col pc (Nat.succ (fst plive)) l)) (snd plive)
      else
        false

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
        if is_vote_builtinb ef then
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
                                    
    end.

  Definition check_op_instr (pc : node) (instr : instruction) (bb : list instruction) (op_plive : option (nat * Locset.t)) : bool :=
    match op_plive with
    | Some plive => check_col_instr pc instr plive
    | None => false
    end.

  Definition check_col_function (f: function) : bool :=
    let params := process_rargs (loc_arguments f.(fn_sig)) in
    Locset.for_all (fun param => col f.(fn_entrypoint) 1 param =? White) params &&
    (* This will give the function a bblock *)
    PTree_Properties.for_all f.(fn_code) (fun pc bb =>
    (* for each instr in the bb *)
        (List.forallb (fun inst => 
          (check_op_instr pc (snd inst) bb (List.nth_error (PMap.get pc lalive) (fst inst)))
        ) 
        (* now we fold to get a better structure with indices *)
        (snd 
          (fold_left 
            (fun acc el =>
              let '(index, sets) := acc in
              (Nat.succ index, (index, el) :: sets)
            )
          bb
          (O, nil)
          )
        )
      )
      ).


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
    - (* Lgetstack *)
      destruct_andb Hcheck Hloc.
      apply Locset.for_all_2 in Hloc; [| compat_bool_tac].
      destruct (sl) eqn:Hsl.
      + constructor.
        * apply eqb_sound. auto.
        * intros l0 Hin. specialize (Hloc l0 Hin). apply orb_prop in Hloc; destruct Hloc as [Hloc | Hloc'].
          apply orb_prop in Hloc; destruct Hloc as [Hloc | Hloc''].
          ** left. apply loc_in_not2. auto.
          ** right. left. apply loc_in_not2. auto.
          ** right. right. apply eqb_sound. auto.
      + constructor.
        * apply eqb_sound. auto.
        * intros l0 Hin. specialize (Hloc l0 Hin). apply orb_prop in Hloc; destruct Hloc as [Hloc | Hloc'].
          apply orb_prop in Hloc; destruct Hloc as [Hloc | Hloc''].
          ** left. apply loc_in_not2. auto.
          ** right. left. apply loc_in_not2. auto.
          ** right. right. apply eqb_sound. auto.
      + constructor.
        * exact I.
        * intros l0 Hin. specialize (Hloc l0 Hin). apply orb_prop in Hloc; destruct Hloc as [Hloc | Hloc'].
          apply orb_prop in Hloc; destruct Hloc as [Hloc | Hloc''].
          ** left. apply loc_in_not2. auto.
          ** right. left. apply loc_in_not2. auto.
          ** right. right. apply eqb_sound. auto.
    - (* Lsetstack *)
      destruct_andb Hcheck Hloc.
      destruct_andb Hcheck Hneg.
      apply Locset.for_all_2 in Hloc; [|compat_bool_tac].
      destruct (sl) eqn:Hsl.
      + constructor.
        * apply eqb_sound. auto.
        * intros. unfold not in *. destruct (Locset.mem (R src) (snd plive)) eqn:Ht.
          ** apply eqb_sound. simpl in Hneg. apply Locset.MSet.mem_spec in Ht.
             exfalso. apply H. auto. 
          ** simpl in *. apply eqb_sound. auto.
        * intros l0 Hin.
          specialize (Hloc l0 Hin). 
          apply orb_prop in Hloc; destruct Hloc as [Hloc | Hloc'].
          apply orb_prop in Hloc; destruct Hloc as [Hloc | Hloc''].
          ** left. apply loc_in_not2. auto.
          ** right. left. apply loc_in_not2. auto.
          ** right. right. apply eqb_sound. auto.
      + constructor.
        * exact I.
        * intros. unfold not in *. destruct (Locset.mem (R src) (snd plive)) eqn:Ht.
          ** apply eqb_sound. simpl in Hneg. apply Locset.MSet.mem_spec in Ht.
             exfalso. apply H. auto. 
          ** simpl in *. apply eqb_sound. auto.
        * intros l0 Hin.
          specialize (Hloc l0 Hin). 
          apply orb_prop in Hloc; destruct Hloc as [Hloc | Hloc'].
          apply orb_prop in Hloc; destruct Hloc as [Hloc | Hloc''].
          ** left. apply loc_in_not2. auto.
          ** right. left. apply loc_in_not2. auto.
          ** right. right. apply eqb_sound. auto.
      + constructor.
        * apply eqb_sound. auto.
        * intros. unfold not in *. destruct (Locset.mem (R src) (snd plive)) eqn:Ht.
          ** apply eqb_sound. simpl in Hneg. apply Locset.MSet.mem_spec in Ht.
             exfalso. apply H. auto. 
          ** simpl in *. apply eqb_sound. auto.
        * intros l0 Hin.
          specialize (Hloc l0 Hin). 
          apply orb_prop in Hloc; destruct Hloc as [Hloc | Hloc'].
          apply orb_prop in Hloc; destruct Hloc as [Hloc | Hloc''].
          ** left. apply loc_in_not2. auto.
          ** right. left. apply loc_in_not2. auto.
          ** right. right. apply eqb_sound. auto.
    - (* Lsmove *)
      destruct col0; simpl in *; try discriminate.
      + destruct_andb Hcheck Hloc.
        destruct_andb Hcheck Hcol'.
        destruct_andb Hcheck Hcol''.
        apply Locset.for_all_2 in Hloc; [|compat_bool_tac].
        apply wc_Lsmove_green; try apply eqb_sound; auto.
        * intros l0 Hin. specialize (Hloc l0 Hin).
          apply orb_prop in Hloc. destruct Hloc as [Hloc | Hloc].
          apply orb_prop in Hloc. destruct Hloc as [Hloc | Hloc].
          ** left. apply loc_in_not2. auto.
          ** right. left. apply loc_in_not2. auto.
          ** right. right. apply eqb_sound. auto.
      + destruct_andb Hcheck Hloc.
        destruct_andb Hcheck Hcol'.
        destruct_andb Hcheck Hcol''.
        apply Locset.for_all_2 in Hloc; [|compat_bool_tac].
        apply wc_Lsmove_blue; try apply eqb_sound; auto.
        * intros l0 Hin. specialize (Hloc l0 Hin).
          apply orb_prop in Hloc. destruct Hloc as [Hloc | Hloc].
          apply orb_prop in Hloc. destruct Hloc as [Hloc | Hloc].
          ** left. apply loc_in_not2. auto.
          ** right. left. apply loc_in_not2. auto.
          ** right. right. apply eqb_sound. auto.
      + destruct_andb Hcheck Hloc.
        destruct_andb Hcheck Hcol'.
        apply Locset.for_all_2 in Hloc; [|compat_bool_tac].
        apply wc_Lsmove_white; try apply eqb_sound; auto.
        * intros l0 Hin. specialize (Hloc l0 Hin).
          apply orb_prop in Hloc. destruct Hloc as [Hloc | Hloc].
          apply orb_prop in Hloc. destruct Hloc as [Hloc | Hloc].
          ** left. apply loc_in_not2. auto.
          ** right. left. apply loc_in_not2. auto.
          ** right. right. apply eqb_sound. auto.
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
      destruct (is_vote_builtinb_spec ef).
      {
        destruct args; try congruence.
        destruct b; try congruence.
        destruct args; try congruence.
        destruct b; try congruence.
        destruct args; try congruence.
        destruct b; try congruence.
        destruct args; try congruence.
        destruct res; try congruence.
        destruct_andb Hcol Hloc.
        destruct_andb Hcol Hcol'.
        destruct_andb Hcol Hcol''.
        destruct_andb Hcol Hcol'''.
        apply Locset.for_all_2 in Hloc; [|compat_bool_tac].
        apply wc_Lbuiltin_vote; auto.
        * apply eqb_sound. apply Hcol.
        * apply eqb_sound. apply Hcol'''.
        * apply eqb_sound. apply Hcol''.
        * apply eqb_sound. apply Hcol'.
        * intros l0 Hin. specialize (Hloc l0 Hin).
          apply orb_prop in Hloc; destruct Hloc as [Hloc | Hloc].
          + left. apply loc_in_not2. apply Hloc.
          + right. apply eqb_sound. apply Hloc.
      }
      destruct (builtin_can_replicate ef) eqn:Hcan.
      {
        destruct res; try congruence.
        destruct_andb Hbasic Hloc.
        destruct_andb Hbasic Hfcol.
        rewrite forallb_forall in Hfcol.
        apply Locset.for_all_2 in Hloc; [|compat_bool_tac].
        apply wc_Lbuiltin_safe; auto.
        * destruct (is_basicb_spec (col pc (Nat.succ (fst plive)) (R x))); auto; congruence.
        * apply Forall_forall. intros x0 Hin. apply Hfcol in Hin.
          apply builtin_arg_forallb_sound in Hin.
          eapply builtin_arg_forall_impl; eauto. simpl in *. intros. apply eqb_sound. auto.
        * intros l0 Hin. specialize (Hloc l0 Hin). simpl in *.
          apply orb_prop in Hloc; destruct Hloc as [Hloc | Hloc].
          + left. apply loc_in_not2. apply Hloc.
          + right. apply eqb_sound. apply Hloc.
      }
      {
        destruct_andb Hcheck Hloc.
        destruct_andb Hcheck Hres.
        rewrite forallb_forall in Hcheck.
        apply Locset.for_all_2 in Hloc; [|compat_bool_tac].
        constructor; auto.
        * apply Forall_forall. intros x Hin. apply Hcheck in Hin.
          apply builtin_arg_forallb_sound in Hin.
          eapply builtin_arg_forall_impl; eauto. simpl in *. intros. apply eqb_sound. auto.
        * apply builtin_res_forallb_sound in Hres.
          eapply builtin_res_forall_impl; eauto. simpl in *. intros. apply eqb_sound. auto.
        * intros l0 Hin. specialize (Hloc l0 Hin).
          apply orb_prop in Hloc; destruct Hloc as [Hloc | Hloc].
          apply orb_prop in Hloc; destruct Hloc as [Hloc | Hloc].
          + left. apply existsb_exists in Hloc.
            destruct Hloc as [x [Hinarg Hbool]].
            apply Exists_exists.
            exists x. split.
            ++ apply Hinarg.
            ++ apply in_builtin_largb_sound. apply Hbool.
          + right. left. intros. rewrite H in Hloc. apply loc_in_not2.
            apply Hloc.
          + right. right. apply eqb_sound. apply Hloc.
      }
    - (* Lbranch *)
      constructor.
    - (* Lcond *)
      destruct_andb Hargs Hloc.
      apply Locset.for_all_2 in Hloc; [|compat_bool_tac].
      constructor; auto.
        * apply Forall_forall. intros x Hin. apply eqb_sound. 
          rewrite forallb_forall in Hargs. apply Hargs in Hin.
          apply Hin.
        * intros l0 Hin. specialize (Hloc l0 Hin).
          apply orb_prop in Hloc; destruct Hloc as [Hloc | Hloc].
          ** left. apply Locset.MF.mem_2. apply Hloc.
          ** right. destruct_andb Hloc Hloc'. split.
             *** apply eqb_sound. auto.
             *** apply eqb_sound. auto.
    - (* Ljumptable *)
      destruct_andb Hcol Hloc.
      apply Locset.for_all_2 in Hloc; [|compat_bool_tac].
      apply wc_Ljumptable.
        * apply eqb_sound. apply Hcol.
        * intros x Hin. specialize (Hloc x Hin).
          apply orb_prop in Hloc; destruct Hloc as [Hloc | Hloc].
          ** left. apply loc_in_not2. apply Hloc.
          ** right. apply Forall_forall. intros. rewrite forallb_forall in Hloc.
             apply Hloc in H. apply eqb_sound; auto.
    - (* Lreturn *)
      constructor.
  Qed.

Lemma check_col_function_sound (f : function):
  forall live alive,
  LProofLiveness.analyze f = Some live ->
  block_live_after f live = alive ->
  block_inst_llafter f alive = lalive ->
  check_col_function f = true ->
  wc_function col f.
Proof.
  intros live alive Hlive Hblive Hbalive.
  destruct f; unfold check_col_function; simpl.
  intros H.
  apply andb_prop in H.
  destruct H as [Hparams Hcode].
  econstructor; simpl; eauto.
  - apply Locset.for_all_2 in Hparams; [|compat_bool_tac].
    intros l0 Hin. specialize (Hparams l0 Hin).
    simpl in *. apply eqb_sound. auto.
  - rewrite PTree_Properties.for_all_correct in Hcode.
    intros pc bb ilives ilive Hpc Hlalive.
    destruct bb.
    + apply Hcode in Hpc.
      apply Forall_forall.
      intros xlive Hin Hnth.
      rewrite forallb_forall in Hpc.
      specialize (Hpc  xlive Hin).
      apply lcheck_col_instr. simpl in *. auto.
    + apply Hcode in Hpc.
      apply Forall_forall. intros xlive Hin Hnth.
      rewrite forallb_forall in Hpc.
      specialize (Hpc xlive Hin). simpl in *.
      rewrite Hlalive in Hpc. simpl in *.
      apply lcheck_col_instr. rewrite Hnth in Hpc.
      auto.
Qed.



End color_checker.



Definition check_function (f :function) : bool :=
  match LProofLiveness.analyze f with
  | Some live => 
      (* Error check with option for these two vars*)
      let alive := block_live_after f live in
      let lalive := block_inst_llafter f alive in
      match infer_coloring f lalive with
      | None => false
      | Some col => check_col_function lalive col f 
      end
  | None => false
  end.

Lemma check_function_sound (f : function) :
  check_function f = true ->
  exists col, wc_function col f.
Proof.
  unfold check_function.
  destruct (analyze f) as [live|] eqn:Hlive; try congruence.
  destruct (block_live_after f) as [bla bla'] eqn:Hbla; try congruence.
  destruct (block_inst_llafter f) as [bila bila'] eqn:Hbila; try congruence.
  destruct (infer_coloring f) as [col|]; try congruence.
  intros Hcheck; exists col. eapply check_col_function_sound; eassumption.
Qed.


Definition check_program (p :program) : bool :=
  forallb (fun def => match snd def with
                      | Gfun (Internal f) => check_function f
                      | _ => true
                      end) p.(prog_defs).


Lemma check_program_sound (p : program):
  check_program p = true -> wc_program p.
Proof.
  intros Hp i f Hin.
  unfold check_program in Hp.
  rewrite forallb_forall in Hp.
  apply Hp in Hin.
  destruct f; simpl in *; auto.
  apply check_function_sound; auto.
Qed.
