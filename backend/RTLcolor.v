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

(* Inductive is_basic_color : color -> Prop := *)
(* | is_basic_color_red : is_basic_color Red *)
(* | is_basic_color_green : is_basic_color Green *)
(* | is_basic_color_blue : is_basic_color Blue *)
(* . *)

(* Inductive is_basic : option color -> Prop := *)
(* | is_basic_c : forall c, *)
(*     is_basic_color c -> *)
(*     is_basic (Some c). *)

Inductive is_basic : color -> Prop :=
| is_basic_red : is_basic Red
| is_basic_green : is_basic Green
| is_basic_blue : is_basic Blue.

Inductive is_basic' : option color -> Prop :=
| is_basic'_basic : forall c,
    is_basic c ->
    is_basic' (Some c).

(* Inductive is_basic : option color -> Prop := *)
(* | is_basic_red : is_basic (Some Red) *)
(* | is_basic_green : is_basic (Some Green) *)
(* | is_basic_blue : is_basic (Some Blue). *)

(* Inductive is_red : option color -> Prop := *)
(* | is_red_red : is_red (Some Red). *)

(* Inductive is_clear : option color -> Prop := *)
(* | is_clear_clear : is_clear (Some Clear). *)

(* Definition has_color (col : reg -> option color) (r : reg) (c : color) : Prop := *)
(*   match col r with *)
(*   | None => False *)
(*   | Some c' => c = c' *)
(*   end. *)

Inductive is_color : option color -> color -> Prop :=
| is_color_c : forall c,
    is_color (Some c) c.

Definition is_red (c : option color) : Prop :=
  is_color c Red.

Definition is_clear (c : option color) : Prop :=
  is_color c Clear.

Section wc.
  Variable col : node -> reg -> option color.

  (** An instruction is well-colored wrt. coloring [col]. *)
  Inductive wc_instruction (pc : node) : instruction -> Prop :=
  | wc_Inop : forall succ, wc_instruction pc (Inop succ)
  | wc_Iop : forall op args res succ,
      is_basic' (col pc res) ->
      Forall (fun arg => col pc arg = col succ res) args ->
      (forall r c, is_color (col pc r) c -> is_color (col succ r) c) ->
      wc_instruction pc (Iop op args res succ)
  | wc_Iload : forall chunk addr args res succ,
      Forall (fun arg => is_clear (col pc arg) /\ is_red (col succ arg)) args ->
      is_red (col succ res) ->
      (forall r c, ~ In r args -> r <> res ->
              is_color (col pc r) c -> is_color (col succ r) c) ->
      wc_instruction pc (Iload chunk addr args res succ)
  | wc_Istore : forall chunk addr args src succ,
      is_clear (col pc src) ->
      is_red (col succ src) ->
      Forall (fun arg => is_clear (col pc arg) /\ is_red (col succ arg)) args ->
      wc_instruction pc (Istore chunk addr args src succ)
  | wc_Icall : forall sig fn args res succ,
      Forall (fun arg => is_clear (col pc arg)) args ->
      is_red (col succ res) ->
      wc_instruction pc (Icall sig fn args res succ)
  | wc_Itailcall : forall sig fn args,
      Forall (fun arg => is_clear (col pc arg)) args ->
      wc_instruction pc (Itailcall sig fn args)
  (* | wc_Ibuiltin : TODO *)
  | wc_Icond : forall cond args ifso ifnot,
      Forall (fun arg => is_clear (col pc arg)) args ->
      wc_instruction pc (Icond cond args ifso ifnot)
  | wc_Ijumptable : forall arg tbl,
      is_clear (col pc arg) ->
      wc_instruction pc (Ijumptable arg tbl)
  | wc_Ireturn : forall or,
      optionP (fun r => is_clear (col pc r)) or ->
      wc_instruction pc (Ireturn or).

  Definition wc_code (c : code) : Prop :=
    forall pc i, c ! pc = Some i -> wc_instruction pc i.

  Record wc_function (f : function) : Prop :=
    mk_wc_function {
        wc_fn_params : Forall (fun param => col f.(fn_entrypoint) param = Some Red) f.(fn_params);
        wc_fn_code : wc_code f.(fn_code)
      }.

  (* TODO: extra conditions on the coloring, enforcing transfer
     consistency across instructions. Maybe a coloring validation pass
     before the color checker, so those extra conditions are an input
     assumption about [col] here. *)

End wc.

(* Inductive wc_fundef: fundef -> Prop := *)
(* | wc_fundef_external: forall ef, *)
(*     wc_fundef (External ef) *)
(* | wc_function_internal: forall col f, *)
(*     wc_function col f -> *)
(*     wc_fundef (Internal f). *)

Definition wc_program (p : program) : Prop :=
  forall i f, In (i, Gfun (Internal f)) (prog_defs p) -> exists col, wc_function col f.

Axiom infer_coloring : function -> option (node -> reg -> option color).

(* TODO: coloring validator. Might need coloring to be PMap or PTree
   instead of just a function, so that we can iterate over all the
   registers that are assigned a color at a given node. Probably will
   use PTree (the one that uses option). *)

Section coloring_validator.
  Variable col : node -> PTree.t color.
  (* Perform validation and transform into abstracted type (reg -> color) with  *)
End coloring_validator.

Section color_checker.
  Variable col : node -> reg -> option color.

  (* Coq is too clever about telling whether this definition depends
     on col. *)
  Definition check_col_function (f : function) : bool :=
    match col 1%positive 1%positive with
    | Some Red => true
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
