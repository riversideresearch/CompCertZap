(** * Add dual-modular redundancy (DMR) to RTL *)

(** In a nutshell, per function:

  1) reserve a shadow register for each function parameter and each
  register that appears in the body,

  2) begin new code with instructions that copy the function
  parameters into their shadow copies,

  3) for each Iop and Iload instruction in the original code, emit an
  additional corresponding instruction in the shadow world,

  4) for all other instructions, emit preceding code to compare their
  arguments and then execute the main world instruction
  only. Afterware, if the instruction has a result register, emit a
  move from the result register to its shadow register.

  We use the state+error monad from [backend/RTLgen.v]. Each function
  in the program is translated by a separate monadic computation that
  builds up the result code in the [fn_code] field of the state.
*)

Require Import
  AST
  Builtins2
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
  Liveness
.
Import ListNotations.

Local Open Scope string_scope.

Definition smove_sig_of_typ (ty : typ) : option (string * replicate_builtin) :=
  match ty with
  | Tint => Some ("__smove_int", BI_smove_int)
  | Tlong => Some ("__smove_long", BI_smove_long)
  | Tsingle => Some ("__smove_single", BI_smove_single)
  | Tfloat => Some ("__smove_float", BI_smove_float)
  | _ => None
  end.

Definition smove (ty : typ) (src dst : reg)
  : option (node -> instruction) :=
  match smove_sig_of_typ ty with
  | None => None
  | Some (nm, kind) =>
      Some (Ibuiltin (EF_builtin nm (replicate_builtin_sig kind))
              [BA src] (BR dst))
  end.

Definition check_sig_of_typ (ty : typ) : option (string * replicate_builtin) :=
  match ty with
  | Tint => Some ("__check_int", BI_check_int)
  | Tlong => Some ("__check_long", BI_check_long)
  | Tsingle => Some ("__check_single", BI_check_single)
  | Tfloat => Some ("__check_float", BI_check_float)
  | _ => None
  end.

Definition check_of_typ (ty : typ) (r1 r2 : reg)
  : option (node -> instruction) :=
  match check_sig_of_typ ty with
  | None => None
  | Some (nm, kind) =>
      Some (Ibuiltin (EF_builtin nm (replicate_builtin_sig kind))
              [BA r1; BA r2] BR_none)
  end.

(** Emit instructions for comparing register [r1] with its shadow copy [r2].

    [re] is the register type environment of the original
    function. [pc] is the node label where the emitted checkpoint
    should begin. Reserves and returns the node label from which
    subsequent instructions should continue.
*)
Definition check (re : regenv) (r1 r2 : reg) (pc : node)
  : mon node :=
  match check_of_typ (re r1) r1 r2 with
  | None =>
      error (MSG "DMR.v:check: unexpected Tany32 or Tany64" :: POS pc :: nil)
  | Some chk =>
      do succ <- reserve_instr;
      do _ <- update_instr pc (chk succ);
      ret succ
  end.

(** Emit code for checking the list of registers [regs]. [re] is the
    register type environment of the original function. [rm] (the
    replication map) maps registers to their corresponding shadow
    registers. [pc] is the node at which the emitted instructions
    should begin. Reserves and returns the node at which subsequent
    instructions should continue.
 *)
(* TODO: swap order here, so that this is tail recursive? I don't
   think it really matters either way. *)
(* Fixpoint check_regs *)
(*   (re : regenv) (rm : PMap.t reg) (regs : list reg) (pc : node) *)
(*   : mon node := *)
(*   match regs with *)
(*   | [] => ret pc *)
(*   | r1 :: rs => *)
(*       do succ <- check_regs re rm rs pc; *)
(*       check re r1 (rm # r1) succ *)
(*   end. *)

Fixpoint check_regs
  (re : regenv) (rm : PMap.t reg) (regs : list reg) (pc : node)
  : mon node :=
  match regs with
  | [] => ret pc
  | r1 :: rs =>
      do succ <- check re r1 (rm # r1) pc;
      check_regs re rm rs succ
  end.

Fixpoint regs_of_builtin_arg (arg : builtin_arg reg) : list reg :=
  match arg with
  | BA r => [r]
  | BA_splitlong hi lo => regs_of_builtin_arg hi ++ regs_of_builtin_arg lo
  | BA_addptr a1 a2 => regs_of_builtin_arg a1 ++ regs_of_builtin_arg a2
  | _ => []
  end.

(** Pull out registers from builtin_args. *)
Fixpoint regs_of_builtin_args (args : list (builtin_arg reg)) : list reg :=
  match args with
  | [] => []
  | ba :: rest => regs_of_builtin_arg ba ++ regs_of_builtin_args rest
  end.

Definition regs_of_fn (fn : reg + ident) : list reg :=
  match fn with
  | inl r => [r]
  | inr _ => []
  end.

Definition args_of_instruction (instr : instruction) : list reg :=
  match instr with
  | Inop _ => []
  | Iop _ args _ _ => args
  | Iload _  _ args _ _ => args
  | Istore _ _ args src _ => src :: args
  | Icall _ fn args _ _ => regs_of_fn fn ++ args
  | Itailcall _ fn args => regs_of_fn fn ++ args
  | Ibuiltin _ args _ _ => regs_of_builtin_args args
  | Icond _ args _ _ => args
  | Ijumptable arg _ => [arg]
  | Ireturn (Some r) => [r]
  | Ireturn None => []
  end.

(** This ignores the recursive cases because according to
    [exec_Ibuiltin] (specifically [regmap_setres]) the result is used
    only in the [BR] case.  *)
Definition reg_of_builtin_res (res : builtin_res reg) : option reg :=
  match res with
  | BR r => Some r
  | _ => None
  end.

Definition res_of_instruction (instr : instruction) : option reg :=
  match instr with
  | Iop _ _ res _ => Some res
  | Iload _ _ _ res _ => Some res
  | Icall _ _ _ res _ => Some res
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

(** Modify [instr] to jump to [new_succ]. *)
Definition change_succ (instr : instruction) (new_succ : node) : instruction :=
  match instr with
  | Inop _ => Inop new_succ
  | Iop op args dst _ => Iop op args dst new_succ
  | Iload chunk addr args dst _ => Iload chunk addr args dst new_succ
  | Istore chunk addr args src _ => Istore chunk addr args src new_succ
  | Icall sig fn args dst _ => Icall sig fn args dst new_succ
  | Ibuiltin ef args dst _ => Ibuiltin ef args dst new_succ
  | _ => instr
  end.

(** Insert instructions at [pc] to move contents of [r] to its shadow
    copies and then jump to [succ]. *)
Definition copy_to_shadows
  (rm : PMap.t reg) (ty : typ) (r1 : reg) (pc : node) (succ : node)
  : mon unit :=
  match smove ty r1 (rm # r1) with
  | Some mov => update_instr pc (mov succ)
  | _ => error (MSG "DMR.v:copy_to_shadows: unexpected Tany32 or Tany64"
                 :: POS pc :: nil)
  end.

Fixpoint copy_all_to_shadows
  (re : regenv) (rm : PMap.t reg) (rs : list reg) (succ : node)
  : mon node :=
  match rs with
  | [] => ret succ
  | r :: rs' =>
      do n <- reserve_instr;
      do _ <- copy_to_shadows rm (re r) r n succ;
      copy_all_to_shadows re rm rs' n
  end.

(** Generate fault-tolerant instruction sequence corresponding to the
    input instruction. [re] is the register typing context of the
    original function. [rm] (the replication map) maps registers to
    their corresponding shadow registers. *)
Definition transf_instr
  (re : regenv) (rm : PMap.t reg) (ni : node * instruction)
  : mon unit :=
  let (pc, instr) := ni in
  match instr with
  | Inop n =>
      update_instr pc (Inop n)
  (* For data operations, simply execute the instruction in the
     regular and shadow worlds. *)
  | Iop op args dst _succ =>
      do n <- reserve_instr;
      do _ <- update_instr pc
               (Iop op
                  (List.map (fun arg => rm # arg) args)
                  (rm # dst)
                  n);
      update_instr n instr
  (* For other instructions, check the argument registers and then
     execute the instruction only in the regular world. For
     instructions with result registers (Icall and Ibuiltin), copy the
     result to its shadow register. *)
  | _ =>
      do n <- check_regs re rm (args_of_instruction instr) pc;
      match res_of_instruction instr, succ_of_instruction instr with
      | Some res, Some succ =>
          do m <- reserve_instr;
          do _ <- copy_to_shadows rm (re res) res m succ;
          update_instr n (change_succ instr m)
      | _, _ => update_instr n instr
      end
  end.

(** Monadic iteration. *)
Fixpoint iterM {A : Type} (f : A -> mon unit) (l : list A) : mon unit :=
  match l with
  | [] => ret tt
  | x :: xs =>
      do _ <- iterM f xs;
      f x
  end.

(** Monadic iteration (tail recursive). *)
Fixpoint iterM' {A : Type} (f : A -> mon unit) (l : list A) : mon unit :=
  match l with
  | [] => ret tt
  | x :: xs =>
      do _ <- f x;
      iterM' f xs
  end.

(** Monadic fold. *)
Fixpoint foldM {A B : Type} (f : A -> B -> mon A) (l : list B) (a : A)
  : mon A :=
  match l with
  | [] => ret a
  | x :: xs =>
      do a' <- foldM f xs a;
      f a' x
  end.

(** Monadic fold (tail recursive). *)
Fixpoint foldM' {A B : Type} (f : A -> B -> mon A) (l : list B) (a : A)
  : mon A :=
  match l with
  | [] => ret a
  | x :: xs =>
      do a' <- f a x;
      foldM' f xs a'
  end.

(** Transform function code by transforming the instructions. *)
Definition transf_code (re : regenv) (rm : PMap.t reg) (c : code)
  : mon unit :=
  iterM' (transf_instr re rm) (rev' (PTree.elements c)).

Definition Regset_of_list (l : list positive) : Regset.t  :=
  fold_right (fun acc p => Regset.add acc p) Regset.empty l.

Definition Regset_of_option (x : option positive) : Regset.t :=
  match x with
  | Some p => Regset.singleton p
  | None => Regset.empty
  end.

(** All registers that appear in an instruction (arguments or
    destination). *)
(* TODO: relate to instr_uses and instr_defined? *)
Definition instr_regs (i : instruction) : Regset.t :=
  match i with
  | Inop _ => Regset.empty
  | Iop _ args res _ =>
      Regset.union (Regset_of_list args) (Regset.singleton res)
  | Iload _ _ args dst _ =>
      Regset.union (Regset_of_list args) (Regset.singleton dst)
  | Istore _ _ args src _ =>
      Regset.union (Regset_of_list args) (Regset.singleton src)
  | Icall _ (inl r) args res _ =>
      Regset.union (Regset_of_list (r :: args)) (Regset.singleton res)
  | Icall _ _ args res _ =>
      Regset.union (Regset_of_list args) (Regset.singleton res)
  | Itailcall _ (inl r) args => Regset_of_list (r :: args)
  | Itailcall _ _ args => Regset_of_list args
  | Ibuiltin _ args res _ =>
      Regset.union (Regset_of_list (regs_of_builtin_args args))
        (Regset_of_option (reg_of_builtin_res res))
  | Icond _ args _ _ => Regset_of_list args
  | Ijumptable arg _ => Regset.singleton arg
  | Ireturn (Some arg) => Regset.singleton arg
  | Ireturn None => Regset.empty
  end.

(** All registers that appear in the given code (used in
    instructions). *)
Definition code_regs (c : code) : Regset.t :=
  PTree.fold (fun rs _ instr => Regset.union rs (instr_regs instr)) c Regset.empty.

Definition all_regs (params : list reg) (c : code) : Regset.t :=
  Regset.union (Regset_of_list params) (code_regs c).

Definition all_regs_list (params : list reg) (c : code) : list reg :=
  Regset.elements (all_regs params c).

(** All registers that appear in the given function (params + regs
    used in instructions). *)
Definition fun_regs (f : function) : Regset.t :=
  all_regs f.(fn_params) f.(fn_code).

Definition fun_regs_list (f : function) : list positive :=
  all_regs_list f.(fn_params) f.(fn_code).

Definition max_reg (regs : Regset.t) :=
  match Regset.max_elt regs with
  | Some p => p
  | None => 1%positive
  end.

(** Build replication map (mapping each register to a pair of
    corresponding shadow registers) for function [f]. *)
Definition replication_map (f : function) : mon (PMap.t reg) :=
  foldM' (fun rm r1 =>
           do r2 <- new_reg;
           ret (PMap.set r1 r2 rm)
    ) (rev' (fun_regs_list f)) (PMap.init xH).

(** Compute registers that are live-in at the entry point of [f]. *)
Definition live_regs (f : function) : mon Regset.t :=
  match Liveness.analyze f with
  | Some m => let pc := fn_entrypoint f in
             ret (transfer f pc (m !! pc))
  | None => error (MSG "Replicate.v:live_regs: liveness analysis failed" :: nil)
  end.

(** Compute the list of registers that need to be copied to their
    shadows in the function prologue: take the intersection of live
    registers with registers appearing in the code (to trivially know
    that everything in the resulting set is a register that appears in
    the code, without having to reason about the liveness analysis
    itself), and then subtract the function's parameters. *)
Definition live_regs_to_copy (f : function) : mon (list reg) :=
  do live <- live_regs f;
  ret (Regset.elements (Regset.diff
                          (Regset.inter live (code_regs f.(fn_code)))
                          (Regset_of_list f.(fn_params)))).

(** Tail-recursive list append. *)
Definition app' {A : Type} (l1 l2 : list A) : list A :=
  rev_append (rev' l1) l2.

(** Generate fault-tolerant version of function [f]. [re] should be
    the register type environment that resulted from typechecking [f].

    1) Gather all registers that are used by the function,
    2) reserve shadow registers for each,
    3) emit preamble code that copies the function's parameters to
       their shadow registers,
    4) translate the function body
    5) return the new entry point node for the function (since new
       instructions were inserted at the front).
*)
Definition transf_fun (re : regenv) (f : function)
  : mon node :=
  do rm <- replication_map f;
  do live <- live_regs_to_copy f;
  do entry_point <- copy_all_to_shadows re rm (app' live f.(fn_params))
                     f.(fn_entrypoint);
  do _ <- transf_code re rm f.(fn_code);
  ret entry_point.

(** Initialize the generator state with [st_nextreg] and [st_nextnode]
    greater than all of the registers and nodes appearing in the
    original function. This ensures that we can reuse the old param
    registers, nodes, and instructions without modification and any
    new registers and nodes won't collide with them. *)
Program Definition init_state (f : function) : state :=
  mkstate
    (max_reg (fun_regs f) + 1)
    (max_pc_function f + 1)
    (PTree.empty instruction)
    _.

(** Run [transf_fun] on [f] with the appropriate initial state. *)
Definition transf_fun' (re : regenv) (f : function) : Errors.res function :=
  match transf_fun re f (init_state f) with
  | Error err => Errors.Error err
  | OK entrypoint s _ => Errors.OK {| fn_sig := f.(fn_sig);
                                    fn_params := f.(fn_params);
                                    fn_stacksize := f.(fn_stacksize);
                                    fn_code := s.(st_code);
                                    fn_entrypoint := entrypoint; |}
  end.

(** Transform a function [f]:

    1) typecheck the function to obtain the register type environment [re],

    2) Call [transf_fun'] with [re] on [f].
*)
Definition transf_function (f : function) : Errors.res function :=
  Errors.bind (type_function f) (fun re => transf_fun' re f).

Definition transf_fundef (fd : fundef) : Errors.res fundef :=
  AST.transf_partial_fundef transf_function fd.

Definition transf_program (p : program) : Errors.res program :=
  transform_partial_program transf_fundef p.

(* Definition transf_program (p : program) : Errors.res program := *)
(*   Errors.OK p. *)
