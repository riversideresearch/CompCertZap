Require Import Coqlib.
Require Import Lattice.
Require Import Maps.
Require Import AST.
Require Import Events.
Require Import Op.
Require Import Registers.
Require Import CompCertZapUtils.
Require Import LTL.
Require Import Kildall.
Require Import Locations.

(* Helper definitions (identical to Liveness.v). *)

Notation loc_live := Locset.add.
Notation loc_dead := Locset.remove.

(*
 Add the optional location to the live set, if it exists
 *)
Definition loc_option_live (or: option loc) (lv: Locset.t) :=
  match or with
  | None => lv
  | Some r => loc_live r lv
  end.

Definition loc_sum_live (ros : mreg + ident) (lv: Locset.t) :=
  match ros with
  | inl r => loc_live (R r) lv
  | inr s => lv
  end.

Fixpoint mreg_list_live (mrl : list mreg) (lv : Locset.t) {struct mrl} : Locset.t :=
  match mrl with
  | nil => lv
  | r1 :: mrs => mreg_list_live mrs (loc_live (R r1) lv)
  end.

Fixpoint mreg_list_dead (mrl : list mreg) (lv : Locset.t) {struct mrl} : Locset.t :=
  match mrl with
  | nil => lv
  | r1 :: mrs => mreg_list_dead mrs (loc_dead (R r1) lv)
  end.

Fixpoint loc_list_live (llv : list loc) (lv : Locset.t) {struct llv} : Locset.t :=
  match llv with
  | nil => lv
  | h :: t => loc_list_live t (loc_live h lv)
  end.

Fixpoint loc_dead_res (llv : builtin_res loc) (lv : Locset.t) {struct llv} : Locset.t :=
  match llv with
  | BR l => loc_dead l lv
  | _ => lv
  end.


Definition transf_in (ins : instruction) (after: Locset.t) : Locset.t :=
  match ins with
  | Lop op args res => mreg_list_live args (loc_dead (R res) after)
  | Lload chunk addr args dst => mreg_list_live args (loc_dead (R dst) after)
  | Lgetstack sl ofs ty dst => loc_live (S sl ofs ty) (loc_dead (R dst) after)
  | Lsetstack src sl ofs ty => loc_live (R src) (loc_dead (S sl ofs ty) after)
  | Lsmove col src dst => loc_live src (loc_dead dst after)
  | Lstore chunk addr args src => mreg_list_live args (loc_live (R src) after)
  | Lcall sg ros => loc_sum_live ros after
  | Ltailcall sg ros => loc_sum_live ros Locset.empty
  | Lbuiltin ef args res => loc_list_live (params_of_builtin_args args)
      (match res with
       | BR x => loc_dead (R x) after
       | _ => after
       end
       )
  | Lbranch s => after
  | Lcond cond args s1 s2 => mreg_list_live args after
  | Ljumptable arg tbl => loc_live (R arg) after
  | Lreturn => after
  end.

Fixpoint transf_instr (instr : list instruction) (after: Locset.t) : Locset.t :=
  match instr with
  | nil => after
  | h :: t => transf_in h (transf_instr t after)
  end.

Definition transf_instr_sets (instrs : list instruction) (after : Locset.t) : list (nat * Locset.t) :=
  let start := length instrs in
  snd (
    snd
      (fold_right
         (fun instr acc =>
            let '(current_after, (index, sets)) := acc in
            let before := transf_in instr current_after in
            (before, (Nat.pred index, (index, before) :: sets))
         )
         (after, (start, nil))
         instrs)).


Definition transfer
  (f: function) (pc: node) (after: Locset.t) : Locset.t :=
  match f.(fn_code)!pc with
  | None =>
      Locset.empty
  | Some bb =>
      transf_instr bb after
  end.

Module LocsetLat := LFSet(Locset).
Module DS := Backward_Dataflow_Solver(LocsetLat)(NodeSetBackward).      

Definition analyze (f: function): option (PMap.t Locset.t) :=
  DS.fixpoint f.(fn_code) successors_block (transfer f).


Definition live_after_block (live_before : PMap.t Locset.t) (succs : list node) : Locset.t :=
  List.fold_left (fun acc s => Locset.union acc (PMap.get s live_before)) succs Locset.empty.

Definition block_live_after
    (f : function)
    (live_before : PMap.t Locset.t)
    : PMap.t Locset.t :=
  fold_left
    (fun acc entry =>
       match entry with
       | (pc, block) =>
           let after :=
             live_after_block
               live_before
               (successors_block block)

           in

           PMap.set pc after acc
       end)
    (PTree.elements f.(fn_code))
    (PMap.init Locset.empty).

Definition block_inst_llafter (f : function) (live_after : PMap.t Locset.t) : PMap.t (list (nat * Locset.t)) :=
  fold_left
    (fun acc node =>
      match node with
      | (pc, block) =>
          let llafter :=
              (*Definition transf_instr_sets (instrs : list instruction) (after : Locset.t) : list Locset.t :=*)
              transf_instr_sets block (PMap.get pc live_after)
          in
          PMap.set pc llafter acc
      end)
      (PTree.elements f.(fn_code))
      (PMap.init nil).
