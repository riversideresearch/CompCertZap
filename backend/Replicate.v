(** * Add redundancy to RTL *)

(** In a nutshell, per function:

  1) reserve two shadow registers for each function parameter and
  register that appear in the body,

  2) begin new code with instructions that copy the function
  parameters into their shadow copies,

  3) for each IOp instruction in the original code, emit two
  additional corresponding instructions in the two shadow worlds,

  4) for all other instructions, emit preceding code to majority vote
  their arguments (leaving the voted results in the regular world
  registers) and then the regular instruction only. Then, if the
  instruction has a result register, emit a move from the result
  register to its shadow registers.

  We use the state+error monad from [backend/RTLgen.v]. Each function
  in the program is translated by a separate monadic computation that
  builds up the result program in the [fn_code] field of the state.
  *)

Require Import
  AST
  Coqlib
  Errors
  Integers
  Maps
  Op
  Ordered
  Registers
  RTL
  RTLgen
  RTLtyping
.
Import ListNotations.

(** Emit instructions for majority voting registers [r1], [r2], and
    [r3], storing the result in [r1] and leaving the contents of [r2]
    and [r3] the same.

    [re] is the register typing context of the original function. [pc]
    is the node at which the emitted instructions should
    begin. Reserves and returns the node at which subsequent
    instructions should continue.  *)
Definition maj_vote (re : regenv) (r1 r2 r3 : reg) (pc : node)
  : mon node :=
  do comp <- match re r1 with
            | Tint => ret Ccomp
            | Tlong => ret Ccompl
            | Tsingle => ret Ccompfs
            | Tfloat => ret Ccompf
            | Tany32 => error (MSG "unexpected Tany32 instruction at pc: "
                                :: POS pc :: nil)
            | Tany64 => error (MSG "unexpected Tany64 instruction at pc: "
                                :: POS pc :: nil)
            end;
  do n1 <- reserve_instr;
  do n2 <- reserve_instr;
  do succ <- reserve_instr;
  do _ <- update_instr pc (Icond (comp Ceq) [r1; r2] succ n1);
  do _ <- update_instr n1 (Icond (comp Ceq) [r2; r3] n2 succ);
  do _ <- update_instr n2 (Iop Omove [r2] r1 succ);
  ret succ.

(** Emit code for majority voting the list of registers [reg]. [re] is
    the register typing context of the original function. [rm] (the
    replication map) maps registers to their corresponding shadow
    registers. [pc] is the node at which the emitted instructions
    should begin. Reserves and returns the node at which subsequent
    instructions should continue. *)
Fixpoint maj_vote_regs (re : regenv) (rm : PMap.t (reg * reg)) (regs : list reg) (pc : node)
  : mon node :=
  match regs with
  | [] => ret pc
  | r1 :: rs =>
      let (r2, r3) := PMap.get r1 rm in
      do succ <- maj_vote re r1 r2 r3 pc;
      maj_vote_regs re rm rs succ
  end.

(** Pull out registers from builtin_args. *)
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

Definition succ_of_instruction (instr : instruction) : option node :=
  match instr with
  | Inop succ => Some succ
  | Iop _ _ _ succ => Some succ
  | Iload _ _ _ _ succ => Some succ
  | Istore _ _ _ _ succ => Some succ
  | Icall _ _ _ _ succ => Some succ
  | Ibuiltin _ _ _ succ => Some succ
  | _ => None
  end.

(** Change [instr] to jump to [new_succ]. *)
Definition change_succ (new_succ : node) (instr : instruction) : instruction :=
  match instr with
  | Inop _ => Inop new_succ
  | Iop op args dst _ => Iop op args dst new_succ
  | Iload chunk addr args dst _ => Iload chunk addr args dst new_succ
  | Istore chunk addr args src _ => Istore chunk addr args src new_succ
  | Icall sig fn args dst _ => Icall sig fn args dst new_succ
  | Ibuiltin ef args dst _ => Ibuiltin ef args dst new_succ
  | _ => instr
  end.

(** Insert instruction at [pc] to move contents of [r] to its shadow
    copy and then jump to [succ].  *)
Definition copy_to_shadows
  (rm : PMap.t (reg * reg)) (r1 : reg) (pc : node) (succ : node)
  : mon unit :=
  let (r2, r3) := PMap.get r1 rm in
  do n <- reserve_instr;
  do _ <- update_instr pc (Iop Omove [r1] r2 n);
  update_instr n (Iop Omove [r1] r3 succ).

(** Generate fault-tolerant instruction sequence corresponding to the
    input instruction. [re] is the register typing context of the
    original function. [rm] (the replication map) maps registers to
    their corresponding shadow registers. *)
Definition transf_instr (re : regenv) (rm : PMap.t (reg * reg)) (ni : node * instruction)
  : mon unit :=
  let (pc, instr) := ni in
  match instr with
  (* For data operations, simply execute the instruction in the
     regular and two shadow worlds. *)
  | Iop op args dst _succ =>
      do n1 <- reserve_instr;
      do n2 <- reserve_instr;
      do _ <- update_instr pc (Iop op
                                (List.map (fun arg => fst (PMap.get arg rm)) args)
                                (fst (PMap.get dst rm))
                                n1);
      do _ <- update_instr n1 (Iop op
                                (List.map (fun arg => snd (PMap.get arg rm)) args)
                                (snd (PMap.get dst rm))
                                n2);
      update_instr n2 instr
  (* For other instructions, majority vote the argument registers and
     then execute the instruction only in the regular world. For
     instructions with result registers, copy the result into its
     shadow register. *)
  | _ =>
      do n <- maj_vote_regs re rm (args_of_instruction instr) pc;
      match res_of_instruction instr, succ_of_instruction instr with
      | Some res, Some succ =>
          do m <- reserve_instr;
          do _ <- update_instr n (change_succ m instr);
          copy_to_shadows rm res m succ
      | _, _ => update_instr n instr
      end
  end.

(** Monadic iteration. *)
Fixpoint iterM {A : Type} (f : A -> mon unit) (l : list A) : mon unit :=
  match l with
  | [] => ret tt
  | x :: xs =>
      do _ <- f x;
      iterM f xs
  end.

(** Monadic fold. *)
Fixpoint foldM {A B : Type} (f : A -> B -> mon A) (l : list B) (a0 : A)
  : mon A :=
  match l with
  | [] => ret a0
  | x :: xs =>
      do y <- f a0 x;
      foldM f xs y
  end.

(** Transform function code by transforming the instructions. *)
Definition transf_code (re : regenv) (rm : PMap.t (reg * reg)) (c : code)
  : mon unit :=
  iterM (transf_instr re rm) (PTree.elements c).

(** Sets of positives. *)
Module PSet := FSetAVL.Make(OrderedPositive).

Definition list_union (l : list PSet.t) : PSet.t :=
  fold_left PSet.union l PSet.empty.

Definition PSet_of_list (l : list positive) : PSet.t :=
  list_union (List.map PSet.singleton l).

Definition PSet_of_option (x : option positive) : PSet.t :=
  match x with
  | Some p => PSet.singleton p
  | None => PSet.empty
  end.

(** All registers that appear in an instruction (arguments or
    destination). *)
Definition instr_regs (i : instruction) : PSet.t :=
  match i with
  | Inop s => PSet.empty
  | Iop op args res s => PSet.union (PSet_of_list args) (PSet.singleton res)
  | Iload chunk addr args dst s =>
      PSet.union (PSet_of_list args) (PSet.singleton dst)
  | Istore chunk addr args src s =>
      PSet.union (PSet_of_list args) (PSet.singleton src)
  | Icall sig (inl r) args res s =>
      PSet.union (PSet_of_list args) (PSet.singleton res)
  | Icall sig (inr id) args res s =>
      PSet.union (PSet_of_list args) (PSet.singleton res)
  | Itailcall sig (inl r) args => PSet_of_list args
  | Itailcall sig (inr id) args => PSet_of_list args
  | Ibuiltin ef args res s =>
      PSet.union (PSet_of_list (builtin_args_regs args))
        (PSet_of_option (reg_of_builtin_res res))
  | Icond cond args ifso ifnot => PSet_of_list args
  | Ijumptable arg tbl => PSet.singleton arg
  | Ireturn None => PSet.empty
  | Ireturn (Some arg) => PSet.singleton arg
  end.

(** All registers that appear in the given code. *)
Definition code_regs (c : code) : PSet.t :=
  PTree.fold (fun rs _ instr => PSet.union rs (instr_regs instr)) c PSet.empty.

(** Generate instructions to copy contents of registers [params] to
    their corresponding shadow registers. [succ] is the node to jump
    to after copying. Reserves and returns the node at which copying
    starts (to become the new entry point of the function). *)
Fixpoint copy_params (rm : PMap.t (reg * reg)) (params : list reg) (succ : node)
  : mon node :=
  match params with
  | [] => ret succ
  | r :: rs =>
      do n <- reserve_instr;
      do _ <- copy_to_shadows rm r n succ;
      copy_params rm rs n
  end.

(** Generate fault-tolerant version of function [f]. [re] should be
    the typing context that resulted from typechecking [f].

    1) Gather all registers that are used by the function,
    2) reserve shadow registers for each,
    3) emit preamble code that copies the function's parameters to
       their shadow registers,
    4) translate the function body
    5) return the new entry point node for the function (since new
       instructions were inserted at the front).
*)
Definition transf_fun (re : regenv) (f : function) : mon node :=
  let all_regs := PSet.union
                    (PSet_of_list f.(fn_params))
                    (code_regs f.(fn_code)) in
  do rm <- foldM (fun rm r1 =>
                   do r2 <- new_reg;
                   do r3 <- new_reg;
                   ret (PMap.set r1 (r2, r3) rm)
            ) (PSet.elements all_regs) (PMap.init (xH, xH));
  do entry_point <- copy_params rm f.(fn_params) f.(fn_entrypoint);
  do _ <- transf_code re rm f.(fn_code);
  ret entry_point.

(** Initialize the generator state with [st_nextreg] and [st_nextnode]
    greater than all of the registers and nodes appearing in the
    original function. This ensures that we can reuse the old param
    registers, nodes, and instructions as-is since all of our new
    registers and nodes won't collide with them. *)
Program Definition initial_state (f : function) : state :=
  mkstate
    (max_reg_function f + 1)
    (max_pc_function f + 1)
    (PTree.empty instruction)
    _.

(** Run [transf_fun] on [f] with the appropriate initial state. *)
Definition transf_fun' (re : regenv) (f : function) : Errors.res function :=
  match transf_fun re f (initial_state f) with
  | Error err => Errors.Error err
  | OK entrypoint s _ => Errors.OK {| fn_sig := f.(fn_sig);
                                    fn_params := f.(fn_params);
                                    fn_stacksize := f.(fn_stacksize);
                                    fn_code := s.(st_code);
                                    fn_entrypoint := entrypoint |}
  end.

Definition transf_function (f : function) : Errors.res function :=
  Errors.bind (type_function f) (fun re => transf_fun' re f).

Definition transf_fundef (fd : fundef) : Errors.res fundef :=
  AST.transf_partial_fundef transf_function fd.

Definition transf_program (p : program) : Errors.res program :=
  transform_partial_program transf_fundef p.
