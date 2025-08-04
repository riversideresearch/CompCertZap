Require Import
  AST
  (* Coqlib *)
  (* Events *)
  (* Globalenvs *)
  List
  Maps
  Registers
  RTL
  Values
.

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

Inductive basic_color : color -> Prop :=
| basic_red : basic_color Red
| basic_green : basic_color Green
| basic_blue : basic_color Blue
.

Section wc.
  (** Everything in this section is wrt. a given register coloring [col]. *)
  Variable col : node -> reg -> color.
  
  (** An instruction is well-colored wrt. coloring [col]. *)
  Inductive wc_instruction : instruction -> Prop :=
  | wc_Inop : forall succ, wc_instruction (Inop succ)
  (* | wc_Iop *)
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

  Definition wc_code (c : code) : Prop :=
    forall pc i, c ! pc = Some i -> wc_instruction i.

  Record wc_function (f : function) : Prop :=
    mk_wc_function {
        wc_fn_params : Forall (fun param => col f.(fn_entrypoint) param = Red) f.(fn_params);
        wc_fn_code : wc_code f.(fn_code)
      }.
  
  Inductive wc_fundef: fundef -> Prop :=
  | wc_fundef_external: forall ef,
      wc_fundef (External ef)
  | wc_function_internal: forall f,
      wc_function f ->
      wc_fundef (Internal f).

  Definition wc_program (p : program) : Prop :=
    forall i f, In (i, Gfun f) (prog_defs p) -> wc_fundef f.
End wc.

Axiom infer_coloring : function -> option (reg -> color).

Section color_checker.
  Variable col : node -> reg -> color.

  Definition check_function (f : function) : bool := false.

  Lemma check_function_sound (f : function) :
    check_function f = true -> wc_function col f.
  Admitted.

  Lemma check_function_complete (f : function) :
    wc_function col f -> check_function f = true.
  Admitted.

  Theorem check_function_iff (f : function) :
    check_function f = true <-> wc_function col f.
  Proof.
    split.
    - apply check_function_sound.
    - apply check_function_complete.
  Qed.
  
End color_checker.
