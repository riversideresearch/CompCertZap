Require Import Coqlib.
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
Print slot.
Print mreg.
Print loc.
Print reg.
Print OrderedLoc.
Check ident.
(*
 Add the optional location to the live set, if it exists
 *)
Definition loc_option_live (or: option loc) (lv: Locset.t) :=
  match or with
  | None => lv
  | Some r => loc_live r lv
  end.

(*Print sum.*)
(*Check (mreg + ident)%type.*)
(*Check (mreg + ident).*)
Print loc.
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

Fixpoint transf_instr (instr : list instruction) (after: Locset.t) : Locset.t :=
  match instr with
  | nil => after
  | h :: t => 
      match h with
      | Lop op args res => mreg_list_live args (loc_dead (R res) (transf_instr t after))
      | Lload chunk addr args dst => mreg_list_live args (loc_dead (R dst) (transf_instr t after))
      | Lgetstack sl ofs ty dst => loc_live (S sl ofs ty) (loc_dead (R dst) (transf_instr t after))
      | Lsetstack src sl ofs ty => loc_live (R src) (loc_dead (S sl ofs ty) (transf_instr t after))
      | Lstore chunk addr args src => mreg_list_live args (loc_live (R src) (transf_instr t after))
      | Lcall sg ros => loc_sum_live ros (transf_instr t after)
      | _ => after
      end 
  end.

Definition transfer
  (f: function) (pc: node) (after: Locset.t) : Locset.t :=
  match f.(fn_code)!pc with
  | None =>
      Locset.empty
  | Some bb =>
      transf_instr bb after
  end.
      
