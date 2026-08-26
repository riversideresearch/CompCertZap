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
  Values
  Locations
  Conventions1
.

(*Inductive color : Type :=*)
(*  | Red*)
(*  | Green*)
(*  | Blue*)
(*  | White*)
(*  | Pink*)
(*      .*)
(*Definition eqb (c1 c2 : color) : bool :=*)
(*  match c1, c2 with*)
(**)
(*  | Red, Red => true*)
(*  | Green, Green => true*)
(*  | Blue, Blue => true*)
(*  | White, White => true*)
(*  | Pink, Pink => true*)
(*  | _, _ => false*)
(*  end.*)


Declare Scope color_scope.

Infix "=?" := eqb (at level 70, no associativity) : color_scope.


Local Open Scope color_scope.

Lemma eqb_spec (c1 c2 : color) : reflect (c1 = c2) (c1 =? c2).
Proof. destruct c1, c2; simpl; try left; auto; right; congruence. Qed.



Lemma eqb_sound (c1 c2 : color) :
  c1 =? c2 = true -> c1 = c2.
Proof. destruct (eqb_spec c1 c2); congruence. Qed.


Definition proc_args_loc (args : list mreg) : Locset.t :=
  fold_left (fun acc el =>
    Locset.add (R el) acc
    ) args Locset.empty.

Definition process_rargs (rp : list (rpair loc)) : Locset.t :=
  fold_left (fun acc x =>
    match x with
    | One l => Locset.add l acc
    | Twolong l l' => Locset.add l (Locset.add l acc)
    end
      ) rp Locset.empty.



Inductive is_basic : color -> Prop :=
  | is_basic_red    : is_basic Red
  | is_basic_green  : is_basic Green
  | is_basic_blue   : is_basic Blue.


Search (Locset.elt -> Locset.t -> Prop).
Check Locset.mem.
Check Locset.In.
Check Locset.MF.eqb.
Search (loc -> loc -> Prop).
Print Locset.X'.eq.
Locate "||".
Check or.
Print or.
Locate in_builtin_arg.
Check In.
Section lwc.
  Variable lalive : PMap.t (list (nat * Locset.t)).
  Variable col : node -> nat -> loc -> color.

  Inductive wc_instruction (pc :node) (plive : (nat * Locset.t)) : instruction -> Prop :=
    | wc_Lop_protected : forall op args res,
        is_protected op ->
        Forall (fun arg => col pc (fst plive) (R arg) = White) args ->
        Locset.For_all (fun r => ~ (Locset.In r (proc_args_loc args)) -> ~ (Locset.X'.eq r (R res)) ->
                              (col pc (fst plive) r = col pc (Nat.succ (fst plive)) r)) (snd plive) ->
        col pc (Nat.succ (fst plive)) (R res) = White ->
        wc_instruction pc plive (Lop op args res)
    | wc_Lop_safe : forall op args res,
        ~ is_protected op ->
        is_basic (col pc (Nat.succ (fst plive)) (R res)) ->
        Forall (fun arg => (col pc (fst plive) (R arg) = col pc (Nat.succ (fst plive)) (R res))) args ->
        Locset.For_all (fun r => or (Locset.X'.eq r (R res))
                      (col pc (fst plive) r = col pc (Nat.succ (fst plive)) r)) (snd plive) ->
        wc_instruction pc plive (Lop op args res)
    | wc_Lgetstack : forall sl ofs ty dst,
        (match sl with
         | Local => 
              col pc (Nat.succ (fst plive)) (R dst) = col pc (fst plive) (S sl ofs ty)
         | Incoming => 
             col pc (Nat.succ (fst plive)) (R dst) = White 
         | _ => True
         end) ->
        Locset.For_all (fun r => or (Locset.X'.eq r (S sl ofs ty)) (or (Locset.X'.eq r (R dst))
            (col pc (fst plive) r = col pc (Nat.succ (fst plive)) r))) (snd plive) ->
        wc_instruction pc plive (Lgetstack sl ofs ty dst)
    | wc_Lsetstack : forall src sl ofs ty,
        (match sl with
         | Local =>
             col pc (Nat.succ (fst plive)) (S sl ofs ty) = col pc (fst plive) (R src)
         | Outgoing =>
             col pc (Nat.succ (fst plive)) (S sl ofs ty) = White
         | _ => True
         end) ->
         ( ~ Locset.In (R src) (snd plive) -> col pc (fst plive) (R src) = col pc (Nat.succ (fst plive)) (R src)) ->
        Locset.For_all (fun r => or (Locset.X'.eq r (S sl ofs ty)) (or (Locset.X'.eq r (R src))
            (col pc (fst plive) r = col pc (Nat.succ (fst plive)) r))) (snd plive) ->
        wc_instruction pc plive (Lsetstack src sl ofs ty)
    | wc_Lsmove_green : forall colr src dst,
        col pc (fst plive) src = White ->
        col pc (Nat.succ (fst plive)) src = Pink ->
        col pc (Nat.succ (fst plive)) dst = Green ->
        Locset.For_all (fun r => or (Locset.X'.eq r src) (or (Locset.X'.eq r dst)
              (col pc (fst plive) r = col pc (Nat.succ (fst plive)) r))) (snd plive) ->
              wc_instruction pc plive (Lsmove colr src dst)
    | wc_Lsmove_blue : forall colr src dst,
        col pc (fst plive) src = Pink ->
        col pc (Nat.succ (fst plive)) src = Red ->
        col pc (Nat.succ (fst plive)) dst = Blue ->
        Locset.For_all (fun r => or (Locset.X'.eq r src) (or (Locset.X'.eq r dst)
              (col pc (fst plive) r = col pc (Nat.succ (fst plive)) r))) (snd plive) ->
              wc_instruction pc plive (Lsmove colr src dst)
    | wc_Lsmove_white : forall colr src dst,
        col pc (fst plive) src = White ->
        col pc (Nat.succ (fst plive)) dst = White ->
        Locset.For_all (fun r => or (Locset.X'.eq r src) (or (Locset.X'.eq r dst)
              (col pc (fst plive) r = col pc (Nat.succ (fst plive)) r))) (snd plive) ->
              wc_instruction pc plive (Lsmove colr src dst)
    | wc_Lload : forall chunk addr args dst,
        Forall (fun arg => col pc (fst plive) (R arg) = White) args ->
        col pc (Nat.succ (fst plive)) (R dst) = White ->
        Locset.For_all (fun r => or (Locset.In r (proc_args_loc args)) 
                        (or (Locset.X'.eq r (R dst)) (col pc (fst plive) r = col pc (Nat.succ (fst plive)) r)))
                        (snd plive) ->
        wc_instruction pc plive (Lload chunk addr args dst)
    | wc_Lstore : forall chunk addr args src,
        col pc (fst plive) (R src) = White ->
        Locset.For_all (fun r => or (Locset.In r (proc_args_loc args)) (or (Locset.X'.eq r (R src))
                                                            (col pc (fst plive) r = col pc (Nat.succ (fst plive)) r))) (snd plive) ->
        wc_instruction pc plive (Lstore chunk addr args src)
    | wc_Lcall : forall sig ros,
        (forall r, ros = inl r -> col pc (fst plive) (R r) = White) ->
        Locset.For_all (fun r => col pc (fst plive) r = White) (process_rargs (loc_arguments sig))  ->
          (forall l l', or (loc_result sig = One l -> col pc (Nat.succ (fst plive)) (R l) = White) 
            (loc_result sig = Twolong l l' -> col pc (Nat.succ (fst plive)) (R l) = White -> 
                col pc (Nat.succ (fst plive)) (R l') = White)
          ) ->
        Locset.For_all (fun r => or (Locset.In r (process_rargs (loc_arguments sig)))
          (forall l l', or (loc_result sig = One l -> Locset.X'.eq r (R l))
            (or (loc_result sig = Twolong l l' -> Locset.X'.eq r (R l) -> Locset.X'.eq r (R l'))
                (or (forall r', ros = inl r' -> Locset.X'.eq (R r') r)
                    (col pc (fst plive) r = col pc (Nat.succ (fst plive)) r)
                )
            )
          )
        ) 
        (snd plive) ->
        wc_instruction pc plive (Lcall sig ros)
    | wc_Ltailcall : forall sig ros,
        (forall r, ros = inl r -> col pc (fst plive) (R r) = White) ->
        Locset.For_all (fun r => col pc (fst plive) r = White) (process_rargs (loc_arguments sig)) ->
        wc_instruction pc plive (Ltailcall sig ros)
    | wc_Lbuiltin_smove_green : forall ef arg res,
        is_green_smove_builtin ef ->
        (Locset.X'.eq arg (R res) ->
          col pc (Nat.succ (fst plive)) (R res) = Green) ->
          (~ (Locset.X'.eq arg (R res)) ->
          col pc (fst plive) arg = White /\
          col pc (Nat.succ (fst plive)) arg = Pink /\
          col pc (Nat.succ (fst plive)) (R res) = Green) ->
        Locset.For_all (fun r => or (Locset.X'.eq r arg) (or (Locset.X'.eq r (R res))
                          (col pc (fst plive) r = col pc (Nat.succ (fst plive)) r))) (snd plive) ->
        wc_instruction pc plive (Lbuiltin ef (BA arg :: nil) (BR res))
    | wc_Lbuiltin_smove_blue : forall ef arg res,
        is_blue_smove_builtin ef ->
        (Locset.X'.eq arg (R res) ->
          col pc (Nat.succ (fst plive)) (R res) = Blue) ->
          (~ (Locset.X'.eq arg (R res)) ->
          col pc (fst plive) arg = Pink /\
          col pc (Nat.succ (fst plive)) arg = Red /\
          col pc (Nat.succ (fst plive)) (R res) = Blue) ->

        Locset.For_all (fun r => or (Locset.X'.eq r arg) (or (Locset.X'.eq r (R res))
                          (col pc (fst plive) r = col pc (Nat.succ (fst plive)) r))) (snd plive) ->
        wc_instruction pc plive (Lbuiltin ef (BA arg :: nil) (BR res))
    | wc_Lbuiltin_vote : forall ef arg1 arg2 arg3 res,
        is_vote_builtin ef ->
        col pc (fst plive) arg1 = Red ->
        col pc (fst plive) arg2 = Green ->
        col pc (fst plive) arg3 = Blue ->
        col pc (Nat.succ (fst plive)) (R res) = White ->
        Locset.For_all (fun r => or (Locset.X'.eq r (R res)) (col pc (fst plive) r =
          col pc (Nat.succ (fst plive)) r)) (snd plive) ->
        wc_instruction pc plive (Lbuiltin ef (BA arg1 :: BA arg2 :: BA arg3 :: nil) (BR res))
    | wc_Lbuiltin_safe : forall ef args res,
        builtin_can_replicate ef = true ->
        is_basic (col pc (Nat.succ (fst plive)) (R res)) ->
        Forall (builtin_arg_forall (fun r => col pc (fst plive) r =
          col pc (Nat.succ (fst plive)) (R res))) args ->
        Locset.For_all (fun r => or (Locset.X'.eq r (R res)) (col pc (fst plive) r =
          col pc (Nat.succ (fst plive)) r)) (snd plive) ->
        wc_instruction pc plive (Lbuiltin ef args (BR res))
    | wc_Lbuiltin : forall ef args res,
        ~ is_vote_builtin ef ->
        builtin_can_replicate ef = false ->
        Forall (builtin_arg_forall (fun r => col pc (fst plive) r = White)) args ->
        builtin_res_forall (fun r => col pc (Nat.succ (fst plive)) (R r) = White) res ->
        Locset.For_all (fun r => or (Exists (in_builtin_arg r) args)
          (or (forall x, res = BR x -> Locset.X'.eq r (R x))
            (col pc (fst plive) r = col pc (Nat.succ (fst plive)) r)
          )) (snd plive) ->
        wc_instruction pc plive (Lbuiltin ef args res)
    | wc_Lbranch : forall s,
        wc_instruction pc plive (Lbranch s)
    | wc_Lcond : forall cond args s1 s2, 
        Forall (fun arg => col pc (fst plive) (R arg) = White) args ->
        Locset.For_all (fun r => or (Locset.In r (proc_args_loc args))
        ((col pc (fst plive) r = col s1 1 r) /\ (col pc (fst plive) r = col s2 1 r))) (snd plive) ->
        wc_instruction pc plive (Lcond cond args s1 s2)
    | wc_Ljumptable : forall arg tbl,
        col pc (fst plive) (R arg) = White ->
        Locset.For_all (fun r => or (Locset.X'.eq r (R arg))
          (Forall (fun succ => col pc (fst plive) r = col succ 1 r) tbl)) (snd plive) ->
          wc_instruction pc plive (Ljumptable arg tbl)
    | wc_Lreturn :
        wc_instruction pc plive (Lreturn).

  Definition wc_code (c : code) : Prop :=
    forall pc bb ilives ilive, 
    c ! pc = Some bb ->
    PMap.get pc lalive = ilives ->
    Forall (fun el => 
      List.nth_error ilives (fst el) = Some ilive ->
      wc_instruction pc ilive (snd el) 
    )
    (snd 
    (fold_left
    (fun acc el =>
        let '(index, sets) := acc in
        (Nat.succ index, (index, el) :: sets)
    )
    bb
    (O, nil)
    )).



End lwc.

Inductive wc_function col : function -> Prop :=
  lwc_function : forall f live alive lalive params,
    LProofLiveness.analyze f = Some live ->
    block_live_after f live = alive ->
    block_inst_llafter f alive = lalive ->
    process_rargs (loc_arguments f.(fn_sig)) = params ->
    Locset.For_all (fun param => col f.(fn_entrypoint) 1%nat param = White) params ->
    wc_code lalive col f.(fn_code) ->
    wc_function col f.

Definition lwc_fundef (fd :fundef) : Prop :=
  match fd with
  | Internal f => exists col, wc_function col f
  | External _ => True
  end.

Definition wc_program (p : program) : Prop :=
  forall i fd, In (i, Gfun fd) (prog_defs p) -> lwc_fundef fd.
    
