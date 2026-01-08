(** * Add triple-modular redundancy to RTL *)

(** In a nutshell, per function:

  1) reserve two shadow registers for each function parameter and
  register that appears in the body,

  2) begin new code with instructions that copy the function
  parameters into their shadow copies,

  3) for each Iop and Iload instruction in the original code, emit two
  additional corresponding instructions in the two shadow worlds,

  4) for all other instructions, emit preceding code to majority vote
  their arguments (leaving the voted results in the regular world
  registers) and then the regular instruction only. Then, if the
  instruction has a result register, emit a move from the result
  register to its shadow registers.

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

Definition green_smove_sig_of_typ (ty : typ) : option (string * replicate_builtin) :=
  match ty with
  | Tint => Some ("__builtin_smove_int_green", BI_smove_int_green)
  | Tlong => Some ("__builtin_smove_long_green", BI_smove_long_green)
  | Tsingle => Some ("__builtin_smove_single_green", BI_smove_single_green)
  | Tfloat => Some ("__builtin_smove_float_green", BI_smove_float_green)
  | _ => None
  end.

Definition blue_smove_sig_of_typ (ty : typ) : option (string * replicate_builtin) :=
  match ty with
  | Tint => Some ("__builtin_smove_int_blue", BI_smove_int_blue)
  | Tlong => Some ("__builtin_smove_long_blue", BI_smove_long_blue)
  | Tsingle => Some ("__builtin_smove_single_blue", BI_smove_single_blue)
  | Tfloat => Some ("__builtin_smove_float_blue", BI_smove_float_blue)
  | _ => None
  end.

Definition green_smove (ty : typ) (src dst : reg)
  : option (node -> instruction) :=
  match green_smove_sig_of_typ ty with
  | None => None
  | Some (nm, kind) =>
      Some (Ibuiltin (EF_builtin nm (replicate_builtin_sig kind))
              [BA src] (BR dst))
  end.

Definition blue_smove (ty : typ) (src dst : reg)
  : option (node -> instruction) :=
  match blue_smove_sig_of_typ ty with
  | None => None
  | Some (nm, kind) =>
      Some (Ibuiltin (EF_builtin nm (replicate_builtin_sig kind))
              [BA src] (BR dst))
  end.

Definition maj_vote_sig_of_typ (ty : typ) : option (string * replicate_builtin) :=
  match ty with
  | Tint => Some ("__builtin_vote_int", BI_vote_int)
  | Tlong => Some ("__builtin_vote_long", BI_vote_long)
  | Tsingle => Some ("__builtin_vote_single", BI_vote_single)
  | Tfloat => Some ("__builtin_vote_float", BI_vote_float)
  | _ => None
  end.

Definition maj_vote_of_typ (ty : typ) (r1 r2 r3 : reg)
  : option (node -> instruction) :=
  match maj_vote_sig_of_typ ty with
  | None => None
  | Some (nm, kind) =>
      Some (Ibuiltin (EF_builtin nm (replicate_builtin_sig kind))
              [BA r1; BA r2; BA r3] (BR r1))
  end.

(** Emit instructions for majority voting registers [r1], [r2], and
    [r3], storing the result in [r1] and leaving the contents of [r2]
    and [r3] unchanged.

    [re] is the register typing context of the original function. [pc]
    is the node at which the emitted instructions should
    begin. Reserves and returns the node at which subsequent
    instructions should continue.
*)
Definition maj_vote (re : regenv) (r1 r2 r3 : reg) (pc : node)
  : mon node :=
  match maj_vote_of_typ (re r1) r1 r2 r3 with
  | None => error (MSG "Replicate.v:maj_vote: unexpected Tany32 or Tany64"
                    :: POS pc :: nil)
  | Some vote =>
      do succ <- reserve_instr;
      do _ <- update_instr pc (vote succ);
      ret succ
  end.

(** Emit code for majority voting the list of registers [reg]. [re] is
    the register typing context of the original function. [rm] (the
    replication map) maps registers to their corresponding shadow
    registers. [pc] is the node at which the emitted instructions
    should begin. Reserves and returns the node at which subsequent
    instructions should continue. *)
Fixpoint maj_vote_regs
  (re : regenv) (rm : PMap.t (reg * reg)) (regs : list reg) (pc : node)
  : mon node :=
  match regs with
  | [] => ret pc
  | r1 :: rs =>
      do succ <- maj_vote_regs re rm rs pc;
      let (r2, r3) := rm # r1 in
      maj_vote re r1 r2 r3 succ
  end.

(** Insert instructions at [pc] to move contents of [r] to its shadow
    copies and then jump to [succ]. *)
Definition copy_to_shadows
  (rm : PMap.t (reg * reg)) (ty : typ) (r1 : reg) (pc : node) (succ : node)
  : mon unit :=
  let (r2, r3) := rm # r1 in
  match (green_smove ty r1 r2, blue_smove ty r1 r3) with
  | (Some mov1, Some mov2) =>
      do n <- reserve_instr;
      do _ <- update_instr pc (mov1 n);
      update_instr n (mov2 succ)
  | _ => error (MSG "Replicate.v:maj_vote: unexpected Tany32 or Tany64"
                 :: POS pc :: nil)
  end.

Fixpoint copy_all_to_shadows
  (re : regenv) (rm : PMap.t (reg * reg)) (rs : list reg) (succ : node)
  : mon node :=
  match rs with
  | [] => ret succ
  | r :: rs' =>
      do n <- reserve_instr;
      do _ <- copy_to_shadows rm (re r) r n succ;
      copy_all_to_shadows re rm rs' n
  end.

(* Definition can_replicate_instr (instr : instruction) : bool := *)
(*   match instr with *)
(*   | Iop op _ _ _ => *)
(*       match op with *)
(*       | Odiv | Odivu | Omod | Omodu => false *)
(*       | _ => true *)
(*       end *)
(*   (* TODO: return true for some builtins *) *)
(*   | _ => false *)
(*   end. *)

(* Definition replicate_instruction (instr : instruction) : mon unit := *)
(*   ret tt. *)

(** Generate fault-tolerant instruction sequence corresponding to the
    input instruction. [re] is the register typing context of the
    original function. [rm] (the replication map) maps registers to
    their corresponding shadow registers. *)
Definition transf_instr
  (re : regenv) (rm : PMap.t (reg * reg)) (ni : node * instruction)
  : mon unit :=
  let (pc, instr) := ni in
  match instr with
  | Inop n =>
      update_instr pc (Inop n)
  | Iop op args dst _succ =>
      if is_protectedb op then
        do n <- maj_vote_regs re rm (dedup (args_of_instruction instr)) pc;
        match res_of_instruction instr, succ_of_instruction instr with
        | Some res, Some succ =>
            do m <- reserve_instr;
            do _ <- copy_to_shadows rm (re res) res m succ;
            update_instr n (change_succ instr m)
        | _, _ => update_instr n instr
        end
      else
        do n1 <- reserve_instr;
        do n2 <- reserve_instr;
        do _ <- update_instr pc
                 (Iop op
                    (List.map (fun arg => fst (rm # arg)) args)
                    (fst (rm # dst))
                    n1);
        do _ <- update_instr n1
                 (Iop op
                    (List.map (fun arg => snd (rm # arg)) args)
                    (snd (rm # dst))
                    n2);
        update_instr n2 instr
  (* For other instructions, majority vote the argument registers and
     then execute the instruction only in the regular world. For
     instructions with result registers (Icall and Ibuiltin), copy the
     result into its shadow registers. *)
  | _ =>
      do n <- maj_vote_regs re rm (dedup (args_of_instruction instr)) pc;
      match res_of_instruction instr, succ_of_instruction instr with
      | Some res, Some succ =>
          do m <- reserve_instr;
          do _ <- copy_to_shadows rm (re res) res m succ;
          update_instr n (change_succ instr m)
      | _, _ => update_instr n instr
      end
  end.

(* (** Generate fault-tolerant instruction sequence corresponding to the *)
(*     input instruction. [re] is the register typing context of the *)
(*     original function. [rm] (the replication map) maps registers to *)
(*     their corresponding shadow registers. *) *)
(* Definition transf_instr *)
(*   (re : regenv) (rm : PMap.t (reg * reg)) (ni : node * instruction) *)
(*   : mon unit := *)
(*   let (pc, instr) := ni in *)
(*   match instr with *)
(*   | Inop n => *)
(*       update_instr pc (Inop n) *)
(*   (* For data operations, simply execute the instruction in the *)
(*      regular and two shadow worlds. *) *)
(*   (* TODO: treat most builtins like this, except certain ones like *)
(*      malloc, memcpy, etc. *) *)
(*   | Iop op args dst _succ => *)
(*       match op with *)
(*       | Odiv | Odivu | Omod | Omodu => *)
(*                                 do n <- maj_vote_regs re rm (args_of_instruction instr) pc; *)
(*                                 match res_of_instruction instr, succ_of_instruction instr with *)
(*                                 | Some res, Some succ => *)
(*                                     do m <- reserve_instr; *)
(*                                     do _ <- copy_to_shadows rm (re res) res m succ; *)
(*                                     update_instr n (change_succ instr m) *)
(*                                 | _, _ => update_instr n instr *)
(*                                 end *)
(*       | _ =>                     *)
(*           do n1 <- reserve_instr; *)
(*           do n2 <- reserve_instr; *)
(*           do _ <- update_instr pc *)
(*                    (Iop op *)
(*                       (List.map (fun arg => fst (rm # arg)) args) *)
(*                       (fst (rm # dst)) *)
(*                       n1); *)
(*           do _ <- update_instr n1 *)
(*                    (Iop op *)
(*                       (List.map (fun arg => snd (rm # arg)) args) *)
(*                       (snd (rm # dst)) *)
(*                       n2); *)
(*           update_instr n2 instr *)
(*       end *)
(*   (* For other instructions, majority vote the argument registers and *)
(*      then execute the instruction only in the regular world. For *)
(*      instructions with result registers (Icall and Ibuiltin), copy the *)
(*      result into its shadow registers. *) *)
(*   | _ => *)
(*       do n <- maj_vote_regs re rm (args_of_instruction instr) pc; *)
(*       match res_of_instruction instr, succ_of_instruction instr with *)
(*       | Some res, Some succ => *)
(*           do m <- reserve_instr; *)
(*           do _ <- copy_to_shadows rm (re res) res m succ; *)
(*           update_instr n (change_succ instr m) *)
(*       | _, _ => update_instr n instr *)
(*       end *)
(*   end. *)

(** Transform function code by transforming the instructions. *)
Definition transf_code (re : regenv) (rm : PMap.t (reg * reg)) (c : code)
  : mon unit :=
  iterM (transf_instr re rm) (PTree.elements c).

(** Build replication map (mapping each register to a pair of
    corresponding shadow registers) for a function with parameters
    [params] and code body [c]. *)
Definition replication_map (f : function) : mon (PMap.t (reg * reg)) :=
  foldM (fun rm r1 =>
           do r2 <- new_reg;
           do r3 <- new_reg;
           ret (PMap.set r1 (r2, r3) rm)
    ) (fun_regs_list f) (PMap.init (xH, xH)).

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
  | OK entrypoint s _ => Errors.OK {| fn_sig := f.(fn_sig)
                                   ; fn_params := f.(fn_params)
                                   ; fn_stacksize := f.(fn_stacksize)
                                   ; fn_code := s.(st_code)
                                   ; fn_entrypoint := entrypoint |}
  end.

(** Transform a function [f]:

    1) typecheck the function to obtain the register typing context [re],

    2) Call [transf_fun'] with [re] on [f].
*)
Definition transf_function (f : function) : Errors.res function :=
  Errors.bind (type_function f) (fun re => transf_fun' re f).

Definition transf_fundef (fd : fundef) : Errors.res fundef :=
  AST.transf_partial_fundef transf_function fd.

Definition transf_program (p : program) : Errors.res program :=
  transform_partial_program transf_fundef p.
