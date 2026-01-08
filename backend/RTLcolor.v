Require Import
  AST
  Errors
  Coqlib
  Events
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

(** The color of a register isn't necessarily the same at all points
    in a function. White is a temporary color that gets reset to red
    after a use (or pink then red in the case of smoves). So, red
    registers are variously red or white/pink throughout the function,
    but green and blue registers stay green and blue respectively
    (unless they are reused with a different color by assigning to
    them the result of a differently-colored computation). *)

Inductive color : Type :=
| Red
| Green
| Blue
| White
| Pink
.

Lemma color_eq: forall (c1 c2 : color), { c1 = c2 } + { c1 <> c2 }.
Proof. decide equality. Defined.

Definition eqb (c1 c2 : color) : bool :=
  match c1, c2 with
  | Red, Red => true
  | Green, Green => true
  | Blue, Blue => true
  | White, White => true
  | Pink, Pink => true
  | _, _ => false
  end.

Declare Scope color_scope.

Infix "=?" := eqb (at level 70) : color_scope.

Local Open Scope color_scope.

Lemma eqb_spec (c1 c2 : color) : reflect (c1 = c2) (c1 =? c2).
Proof. destruct c1, c2; simpl; try left; auto; right; congruence. Qed.

Definition eqb' (oc1 oc2 : option color) : bool :=
  match oc1, oc2 with
  | Some c1, Some c2 => c1 =? c2
  | None, None => true
  | _, _ => false
  end.

Lemma eqb'_spec (oc1 oc2 : option color) : reflect (oc1 = oc2) (eqb' oc1 oc2).
Proof.
  destruct oc1, oc2; try (right; congruence); simpl.
  - destruct (eqb_spec c c0); subst.
    + left; reflexivity.
    + right; intro HC; inv HC; congruence.
  - left; reflexivity.
Qed.

Lemma eqb'_sound (oc1 oc2 : option color) :
  eqb' oc1 oc2 = true ->
  oc1 = oc2.
Proof. destruct (eqb'_spec oc1 oc2); congruence. Qed.

Inductive is_basic : color -> Prop :=
| is_basic_red : is_basic Red
| is_basic_green : is_basic Green
| is_basic_blue : is_basic Blue.

Inductive is_basic' : option color -> Prop :=
| is_basic'_basic : forall c,
    is_basic c ->
    is_basic' (Some c).

Definition is_color (x : option color) (c : color) : Prop := x = Some c.
Notation is_white x := (is_color x White).
Notation is_pink x := (is_color x Pink).
Notation is_red x := (is_color x Red).
Notation is_green x := (is_color x Green).
Notation is_blue x := (is_color x Blue).

Section wc.
  Variable col : node -> reg -> option color.

  (** An instruction is well-colored wrt. coloring [col].

      We include in these rules consistency constraints asserting that
      colors are preserved from the instruction to its successor,
      except certain things like the argument and result registers of
      the current instruction. This is necessary for maintaining the
      simulation environment in RTLtolerant.v, though they could be
      factored out of this definition into a separate judgement. *)

  Inductive wc_instruction (pc : node) : instruction -> Prop :=
  | wc_Inop : forall succ,
      (forall r c, col pc r = Some c -> col succ r = Some c) ->
      wc_instruction pc (Inop succ)
  | wc_Iop_safe : forall op args res succ,
      ~ is_protected op ->
      is_basic' (col succ res) ->
      Forall (fun arg => col pc arg = col succ res) args ->
      (forall r c, r <> res -> col pc r = Some c -> col succ r = Some c) ->
      wc_instruction pc (Iop op args res succ)
  | wc_Iop_protected : forall op args res succ,
      is_protected op ->
      Forall (fun arg => is_white (col pc arg)) args ->
      is_white (col succ res) ->
      (forall r c, ~ In r args -> r <> res ->
              is_color (col pc r) c -> is_color (col succ r) c) ->
      wc_instruction pc (Iop op args res succ)
  | wc_Iload : forall chunk addr args res succ,
      Forall (fun arg => is_white (col pc arg)) args ->
      is_white (col succ res) ->
      (forall r c, ~ In r args -> r <> res ->
              is_color (col pc r) c -> is_color (col succ r) c) ->
      wc_instruction pc (Iload chunk addr args res succ)
  | wc_Istore : forall chunk addr args src succ,
      is_white (col pc src) ->
      Forall (fun arg => is_white (col pc arg)) args ->
      (forall r c, ~ In r args -> r <> src ->
              is_color (col pc r) c -> is_color (col succ r) c) ->
      wc_instruction pc (Istore chunk addr args src succ)
  | wc_Icall : forall sig fn args res succ,
      (forall r, fn = inl r -> is_white (col pc r)) ->
      Forall (fun arg => is_white (col pc arg)) args ->
      is_white (col succ res) ->
      (forall r c, ~ In r args -> r <> res -> (forall r', fn = inl r' -> r <> r') ->
              is_color (col pc r) c -> is_color (col succ r) c) ->
      wc_instruction pc (Icall sig fn args res succ)
  | wc_Itailcall : forall sig fn args,
      (forall r, fn = inl r -> is_white (col pc r)) ->
      Forall (fun arg => is_white (col pc arg)) args ->
      wc_instruction pc (Itailcall sig fn args)
  | wc_Ibuiltin_smove_green : forall ef arg res succ,
      is_green_smove_builtin ef ->
      is_white (col pc arg) ->
      is_pink (col succ arg) ->
      is_green (col succ res) ->
      (forall r c, r <> arg -> r <> res ->
              is_color (col pc r) c -> is_color (col succ r) c) ->
      wc_instruction pc (Ibuiltin ef (BA arg :: nil) (BR res) succ)
  | wc_Ibuiltin_smove_blue : forall ef arg res succ,
      is_blue_smove_builtin ef ->
      is_pink (col pc arg) ->
      is_red (col succ arg) ->
      is_blue (col succ res) ->
      (forall r c, r <> arg -> r <> res ->
              is_color (col pc r) c -> is_color (col succ r) c) ->
      wc_instruction pc (Ibuiltin ef (BA arg :: nil) (BR res) succ)
  | wc_Ibuiltin_vote : forall ef arg1 arg2 arg3 res succ,
      is_vote_builtin ef ->
      is_red (col pc arg1) ->
      is_green (col pc arg2) ->
      is_blue (col pc arg3) ->
      is_white (col succ res) ->
      (forall r c, r <> res ->
              is_color (col pc r) c -> is_color (col succ r) c) ->
      wc_instruction pc (Ibuiltin ef (BA arg1 :: BA arg2 :: BA arg3 :: nil) (BR res) succ)
  | wc_Ibuiltin : forall ef bargs bres succ,
      ~ is_green_smove_builtin ef ->
      ~ is_blue_smove_builtin ef ->
      ~ is_vote_builtin ef ->
      Forall (builtin_arg_forall (fun r => is_white (col pc r))) bargs ->
      builtin_res_forall (fun r => is_white (col succ r)) bres ->
      (forall r c, ~ Exists (in_builtin_arg r) bargs ->
              (forall x, bres = BR x -> r <> x) ->
              is_color (col pc r) c -> is_color (col succ r) c) ->
      wc_instruction pc (Ibuiltin ef bargs bres succ)
  | wc_Icond : forall cond args ifso ifnot,
      Forall (fun arg => is_white (col pc arg)) args ->
      (forall r c, ~ In r args -> is_color (col pc r) c ->
              is_color (col ifso r) c /\ is_color (col ifnot r) c) ->
      wc_instruction pc (Icond cond args ifso ifnot)
  | wc_Ijumptable : forall arg tbl,
      is_white (col pc arg) ->
      (forall r c, r <> arg -> is_color (col pc r) c ->
              Forall (fun succ => is_color (col succ r) c) tbl) ->
      wc_instruction pc (Ijumptable arg tbl)
  | wc_Ireturn : forall or,
      optionP (fun r => is_white (col pc r)) or ->
      wc_instruction pc (Ireturn or).

  Definition wc_code (c : code) : Prop :=
    forall pc i, c ! pc = Some i -> wc_instruction pc i.

  Record wc_function (f : function) : Prop :=
    mk_wc_function {
        wc_fn_params : Forall (fun param => col f.(fn_entrypoint) param = Some White)
                         f.(fn_params);
        wc_fn_code : wc_code f.(fn_code)
      }.

End wc.

(* Definition wc_program (p : program) : Prop := *)
(*   forall i f, In (i, Gfun (Internal f)) (prog_defs p) -> exists col, wc_function col f. *)

Definition wc_fundef (fd : fundef) : Prop :=
  match fd with
  | Internal f => exists col, wc_function col f
  | External _ => True
  end.

Definition wc_program (p : program) : Prop :=
  forall i fd, In (i, Gfun fd) (prog_defs p) -> wc_fundef fd.
