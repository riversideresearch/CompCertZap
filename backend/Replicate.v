Require Import
  AST
  Coqlib
  Errors
  Maps
  Op
  Ordered
  Registers
  RTL
  RTLgen
.
Import ListNotations.

Definition sync (rm : PMap.t reg) (r : reg) (start : node) : mon node :=
  let shadow_r := PMap.get r rm in
  do n <- reserve_instr;
  do next <- reserve_instr;
  do _ <- update_instr start (Iop Oor [r; shadow_r] r n);
  do _ <- update_instr n (Iop Oor [r; shadow_r] shadow_r next);
  ret next.

Fixpoint sync_regs (rm : PMap.t reg) (regs : list reg) (start : node)
  : mon node :=
  match regs with
  | [] => ret start
  | r :: rs =>
      do next <- sync rm r start;
      sync_regs rm rs next
  end.

Fixpoint builtin_args_regs (args : list (builtin_arg reg)) : list reg :=
  match args with
  | [] => []
  | BA r :: rest => r :: builtin_args_regs rest
  | _ :: rest => builtin_args_regs rest
  end.

Definition args_of_instruction (instr : instruction) : list reg :=
  match instr with
  | Inop _ => []
  | Iop _ args _ _ => args
  | Iload _  _ args _ _ => args
  | Istore _ _ args _ _ => args
  | Icall _ _ args _ _ => args
  | Itailcall _ _ args => args
  | Ibuiltin _ args _ _ => builtin_args_regs args
  | Icond _ args _ _ => args
  | Ijumptable arg _ => [arg]
  | Ireturn (Some r) => [r]
  | Ireturn None => []
  end.

Definition reg_of_builtin_res (res : builtin_res reg) : option reg :=
  match res with
  | BR r => Some r
  | _ => None
  end.

Definition res_of_instruction (instr : instruction) : option reg :=
  match instr with
  | Iop _ _ dst _ => Some dst
  | Iload _ _ _ dst _ => Some dst
  | Icall _ _ _ dst _ => Some dst
  (* | Itailcall _ _ _ ? *)
  | Ibuiltin _ _ res _ => reg_of_builtin_res res
  | _ => None
  end.

Definition copy_to_shadow (rm : PMap.t reg) (r : reg) (next : node) : mon node :=
  add_instr (Iop Omove [r] (PMap.get r rm) next).

Definition transf_instr (rm : PMap.t reg) (ni : node * instruction)
  : mon unit :=
  let (pc, instr) := ni in
  match instr with
  | Iop op args dst _next =>
      do n <- reserve_instr;
      do _ <- update_instr pc (Iop op
                                (List.map (fun arg => PMap.get arg rm) args)
                                (PMap.get dst rm)
                                n);
      update_instr n instr
  | _ =>
      do n <- sync_regs rm (args_of_instruction instr) pc;
      do m <- match res_of_instruction instr with
             | Some res => copy_to_shadow rm res n
             | _ => ret n
             end;
      update_instr m instr
  end.

Fixpoint iterM {A : Type} (f : A -> mon unit) (l : list A) : mon unit :=
  match l with
  | [] => ret tt
  | x :: xs =>
      do _ <- f x;
      iterM f xs
  end.

Fixpoint foldM {A B : Type} (f : A -> B -> mon A) (l : list B) (a0 : A) : mon A :=
  match l with
  | [] => ret a0
  | x :: xs =>
      do y <- f a0 x;
      foldM f xs y
  end.

Definition transf_code (rm : PMap.t reg) (c : code) : mon unit :=
  iterM (transf_instr rm) (PTree.elements c).

Module PSet := FSetAVL.Make(OrderedPositive).

Fixpoint PSet_of_list (l : list positive) : PSet.t :=
  match l with
  | [] => PSet.empty
  | p :: ps => PSet.add p (PSet_of_list ps)
  end.

Fixpoint list_union (l : list PSet.t) : PSet.t :=
  match l with
  | [] => PSet.empty
  | x :: xs => PSet.union x (list_union xs)
  end.

Definition instr_regs (i : instruction) : PSet.t :=
  match i with
  | Inop s => PSet.empty
  | Iop op args res s => PSet_of_list args
  | Iload chunk addr args dst s => PSet_of_list args
  | Istore chunk addr args src s => PSet_of_list args
  | Icall sig (inl r) args res s => PSet_of_list args
  | Icall sig (inr id) args res s => PSet_of_list args
  | Itailcall sig (inl r) args => PSet_of_list args
  | Itailcall sig (inr id) args => PSet_of_list args
  | Ibuiltin ef args res s => PSet_of_list (builtin_args_regs args)
  | Icond cond args ifso ifnot => PSet_of_list args
  | Ijumptable arg tbl => PSet.singleton arg
  | Ireturn None => PSet.empty
  | Ireturn (Some arg) => PSet.singleton arg
  end.

(* Definition PSet_of_option (x : option positive) : PSet.t := *)
(*   match x with *)
(*   | Some p => PSet.singleton p *)
(*   | None => PSet.empty *)
(*   end. *)

(* Definition instr_regs (i : instruction) : PSet.t := *)
(*   match i with *)
(*   | Inop s => PSet.empty *)
(*   | Iop op args res s => PSet.union (PSet_of_list args) (PSet.singleton res) *)
(*   | Iload chunk addr args dst s => *)
(*       PSet.union (PSet_of_list args) (PSet.singleton dst) *)
(*   | Istore chunk addr args src s => *)
(*       PSet.union (PSet_of_list args) (PSet.singleton src) *)
(*   | Icall sig (inl r) args res s => *)
(*       PSet.union (PSet_of_list args) (PSet.singleton res) *)
(*   | Icall sig (inr id) args res s => *)
(*       PSet.union (PSet_of_list args) (PSet.singleton res) *)
(*   | Itailcall sig (inl r) args => PSet_of_list args *)
(*   | Itailcall sig (inr id) args => PSet_of_list args *)
(*   | Ibuiltin ef args res s => *)
(*       PSet.union (PSet_of_list (builtin_args_regs args)) *)
(*         (PSet_of_option (reg_of_builtin_res res)) *)
(*   | Icond cond args ifso ifnot => PSet_of_list args *)
(*   | Ijumptable arg tbl => PSet.singleton arg *)
(*   | Ireturn None => PSet.empty *)
(*   | Ireturn (Some arg) => PSet.singleton arg *)
(*   end. *)

Definition code_regs (c : code) : PSet.t :=
  PTree.fold (fun rs _ instr => PSet.union rs (instr_regs instr)) c PSet.empty.

Fixpoint copy_params (rm : PMap.t reg) (params : list reg) (next : node)
  : mon node :=
  match params with
  | [] => ret next
  | r :: rs =>
      do n <- copy_to_shadow rm r next;
      copy_params rm rs n
  end.

Definition transf_fun (f : function) : mon node :=
  let all_regs := PSet.union
                    (PSet_of_list f.(fn_params))
                    (code_regs f.(fn_code)) in
  do rm <- foldM (fun rm r =>
                   do shadow_r <- new_reg;
                   ret (PMap.set r shadow_r rm)
            ) (PSet.elements all_regs) (PMap.init xH);
  do entry_point <- copy_params rm f.(fn_params) f.(fn_entrypoint);
  do _ <- transf_code rm f.(fn_code);
  ret entry_point.

Program Definition initial_state (f : function) : state :=
  mkstate
    (max_reg_function f + 1)
    (max_pc_function f + 1)
    (PTree.empty instruction)
    _.

Definition transf_fun' (f : function) : function :=
  match transf_fun f (initial_state f) with
  | Error err => f
  | OK entrypoint s _ => {| fn_sig := f.(fn_sig);
                           fn_params := f.(fn_params);
                           fn_stacksize := f.(fn_stacksize);
                           fn_code := s.(st_code);
                           fn_entrypoint := entrypoint |}
  end.

Definition transf_function (f: function) : Errors.res function :=
  Errors.OK (transf_fun' f).

Definition transf_fundef (fd: fundef) : Errors.res fundef :=
  AST.transf_partial_fundef transf_function fd.

Definition transf_program (p: program) : Errors.res program :=
  transform_partial_program transf_fundef p.
