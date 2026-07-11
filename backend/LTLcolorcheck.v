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
  RTLcolor
  Values
  Locations
  Conventions1
.

Definition is_basicb (c : color) : bool :=
  match c with
  | Red | Green | Blue => true
  | _ => false
  end.

Local Open Scope color_scope.


Definition proc_args_loc (args : list mreg) : Locset.t :=
  fold_left (fun acc el =>
    Locset.add (R el) acc
    ) args Locset.empty.

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



  Definition process_rargs (rp : list (rpair loc)) : Locset.t :=
    fold_left (fun acc x =>
      match x with
      | One l => Locset.add l acc
      | Twolong l l' => Locset.add l (Locset.add l acc)
      end
        ) rp Locset.empty.


  Definition check_col_instr (pc : node) (instr : instruction) (op_plive : option (nat * Locset.t)) : bool :=
    match op_plive with
    | Some plive =>
      match instr with
      | Lop op args res =>
          if is_protectedb op then
            forallb (fun arg => col pc (fst plive) (R arg) =? White) args  &&
            let loc_args := proc_args_loc args in
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
      end
    | None => false
    end.



  Definition check_col_function (f: function) : bool :=
    let params := process_rargs (loc_arguments f.(fn_sig)) in
    Locset.for_all (fun param => col f.(fn_entrypoint) 1 param =? White) params &&
    PTree_Properties.for_all f.(fn_code) (fun pc instrs =>
      forallbi (fun inst i => check_col_instr pc inst (List.nth_error (PMap.get pc lalive) i))
       instrs O).

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

