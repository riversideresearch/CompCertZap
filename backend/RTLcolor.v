Require Import
  AST
  Errors
  Coqlib
  (* Events *)
  (* Globalenvs *)
  Integers
  List
  Maps
  Registers
  RTL
  Values
.

Definition optionP {A : Type} (pred : A -> Prop) (o : option A) : Prop :=
  match o with
  | None => True
  | Some a => pred a
  end.

(** TODO: need color to be position dependent. Clear is a temporary
    color that gets reset to red after a use. So, red registers are
    variously red or clear throughout the function, but green and blue
    registers never change colors. *)

Inductive color : Type :=
| Red
| Green
| Blue
| Clear
.

Inductive is_basic : color -> Prop :=
| is_basic_red : is_basic Red
| is_basic_green : is_basic Green
| is_basic_blue : is_basic Blue
.

Inductive is_red : color -> Prop :=
| is_red_red : is_red Red.

Inductive is_clear : color -> Prop :=
| is_clear_clear : is_clear Clear.

Section wc_instruction.
  Variable col : reg -> color.

  (** An instruction is well-colored wrt. coloring [col]. *)
  Inductive wc_instruction : instruction -> Prop :=
  | wc_Inop : forall succ, wc_instruction (Inop succ)
  | wc_Iop : forall op args res succ,
      is_basic (col res) ->
      Forall (fun arg => col arg = col res) args ->
      wc_instruction (Iop op args res succ)
  | wc_Iload : forall chunk addr args res succ,
      Forall (fun arg => is_clear (col arg)) args ->
      is_red (col res) ->
      wc_instruction (Iload chunk addr args res succ)
  | wc_Istore : forall chunk addr args src succ,
      is_clear (col src) ->
      Forall (fun arg => is_clear (col arg)) args ->
      wc_instruction (Istore chunk addr args src succ)
  | wc_Icall : forall sig fn args res succ,
      Forall (fun arg => is_clear (col arg)) args ->
      is_red (col res) ->
      wc_instruction (Icall sig fn args res succ)
  | wc_Itailcall : forall sig fn args,
      Forall (fun arg => is_clear (col arg)) args ->
      wc_instruction (Itailcall sig fn args)
  (* | wc_Ibuiltin : TODO *)
  | wc_Icond : forall cond args ifso ifnot,
      Forall (fun arg => is_clear (col arg)) args ->
      wc_instruction (Icond cond args ifso ifnot)
  | wc_Ijumptable : forall arg tbl,
      is_clear (col arg) ->
      wc_instruction (Ijumptable arg tbl)
  | wc_Ireturn : forall or,
      optionP (fun r => is_clear (col r)) or ->
      wc_instruction (Ireturn or)
  .

(*   | Iop: operation -> list reg -> reg -> node -> instruction *)
(*   | Iload: memory_chunk -> addressing -> list reg -> reg -> node -> instruction *)
(*   | Istore: memory_chunk -> addressing -> list reg -> reg -> node -> instruction *)
(*   | Icall: signature -> reg + ident -> list reg -> reg -> node -> instruction *)
(*   | Itailcall: signature -> reg + ident -> list reg -> instruction *)
(*   | Ibuiltin: external_function -> list (builtin_arg reg) -> builtin_res reg -> node -> instruction *)
(*   | Icond: condition -> list reg -> node -> node -> instruction *)
(*   | Ijumptable: reg -> list node -> instruction *)
(*   | Ireturn: option reg -> instruction. *)

End wc_instruction.

Section wc_function.
  Variable col : node -> reg -> color.

  Definition wc_code (c : code) : Prop :=
    forall pc i, c ! pc = Some i -> wc_instruction (col pc) i.

  Record wc_function (f : function) : Prop :=
    mk_wc_function {
        wc_fn_params : Forall (fun param => col f.(fn_entrypoint) param = Red) f.(fn_params);
        wc_fn_code : wc_code f.(fn_code)
      }.

  (* TODO: extra conditions on the coloring, enforcing transfer
     consistency across instructions. Maybe a coloring validation pass
     before the color checker, so those extra conditions are an input
     assumption about [col] here. *)
  
End wc_function.

(* Inductive wc_fundef: fundef -> Prop := *)
(* | wc_fundef_external: forall ef, *)
(*     wc_fundef (External ef) *)
(* | wc_function_internal: forall col f, *)
(*     wc_function col f -> *)
(*     wc_fundef (Internal f). *)

Definition wc_program (p : program) : Prop :=
  forall i f, In (i, Gfun (Internal f)) (prog_defs p) -> exists col, wc_function col f.

Axiom infer_coloring : function -> option (node -> reg -> color).

Section color_checker.
  Variable col : node -> reg -> color.

  (* Coq is too clever about telling whether this definition depends
     on col. *)
  Definition check_col_function (f : function) : bool :=
    match col 1%positive 1%positive with
    | Red => true
    | _ => false
    end.

  Lemma check_col_function_sound (f : function) :
    check_col_function f = true -> wc_function col f.
  Admitted.

  (* Maybe not necessary but should be true anyway. *)
  Lemma check_col_function_complete (f : function) :
    wc_function col f -> check_col_function f = true.
  Admitted.

  Theorem check_col_function_iff (f : function) :
    check_col_function f = true <-> wc_function col f.
  Proof.
    split.
    - apply check_col_function_sound.
    - apply check_col_function_complete.
  Qed.

End color_checker.

Definition check_function (f : function) : bool :=
  match infer_coloring f with
  | None => false
  | Some col => check_col_function col f
  end.

Lemma check_function_sound (f : function) :
  check_function f = true -> exists col, wc_function col f.
Proof.
  unfold check_function.
  destruct (infer_coloring f) as [col|]; try congruence.
  intro Hcheck; exists col.
  apply check_col_function_sound; assumption.
Qed.

(* check_function_complete not possible because we don't assume
   anything about infer_coloring. *)

Definition check_program (p : program) : bool :=
  forallb (fun def => match snd def with
                   | Gfun (Internal f) => check_function f
                   | _ => true
                   end) p.(prog_defs).

Lemma check_program_sound (p : program) :
  check_program p = true -> wc_program p.
Proof.
  intros Hp i f Hin.
  unfold check_program in Hp.
  rewrite forallb_forall in Hp.
  apply Hp in Hin.
  apply check_function_sound; auto.
Qed.
