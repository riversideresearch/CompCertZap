Require Import
  Errors
  Events
  Globalenvs
  Linking
  List
  Registers
  Replicate
  RTL
  Smallstep
.
Import ListNotations.

Definition fstate := (RTL.state * list bool)%type.

Inductive next : fstate -> fstate -> Prop :=
  next_State : forall stk f sp pc rs m stk' f' sp' pc' rs' m' bs,
      next (State stk f sp pc rs m, bs)
        (State stk' f' sp' pc' rs' m', bs).
(* TODO: Callstate and Returnstate *)

(* Inductive state : Type := *)
(*   | State: *)
(*       forall (stack: list stackframe) (**r call stack *) *)
(*              (f: function)            (**r current function *) *)
(*              (sp: val)                (**r stack pointer *) *)
(*              (pc: node)               (**r current program point in [c] *) *)
(*              (rs: regset)             (**r register state *) *)
(*              (m: mem),                (**r memory state *) *)
(*       state *)
(*   | Callstate: *)
(*       forall (stack: list stackframe) (**r call stack *) *)
(*              (f: fundef)              (**r function to call *) *)
(*              (args: list val)         (**r arguments to the call *) *)
(*              (m: mem),                (**r memory state *) *)
(*       state *)
(*   | Returnstate: *)
(*       forall (stack: list stackframe) (**r call stack *) *)
(*              (v: val)                 (**r return value for the call *) *)
(*              (m: mem),                (**r memory state *) *)
(*       state. *)

Inductive faults_wf : fstate -> Prop :=
| faults_wf_State : forall frame stk f sp pc rs m b bs,
    faults_wf (State stk f sp pc rs m, bs) ->
    faults_wf (State (frame :: stk) f sp pc rs m, b :: bs).
(* TODO: Callstate and Returnstate *)

Inductive zap : fstate -> fstate -> Prop :=
  zap_reg : forall s s', zap s s'.

Section fstep.
  Variable ge : genv.

  Inductive fstep : fstate -> trace -> fstate -> Prop :=
  | astep_step : forall s s' bs bs' t,
      RTL.step ge s t s' ->
      next (s, bs) (s', bs') ->
      fstep (s, bs) t (s', bs').

  Inductive fstar : fstate -> trace -> RTL.state -> Prop :=
  | fstar_refl: forall s bs,
      fstar (s, bs) E0 s
  | fstar_step: forall s1 t1 s2 t2 s3 bs1 t,
      (forall s1' bs1', zap (s1, bs1) (s1', bs1') ->
                   exists bs2, fstep (s1', bs1') t1 (s2, bs2) ->
                          fstar (s2, bs2) t2 s3) ->
      t = t1 ** t2 ->
      fstar (s1, bs1) t s3.

  Inductive fplus : fstate -> trace -> RTL.state -> Prop :=
    fplus_left: forall s1 t1 s2 t2 s3 bs1 t,
        (forall s1' bs1', zap (s1, bs1) (s1', bs1') ->
                     exists bs2, fstep (s1', bs1') t1 (s2, bs2) ->
                            fstar (s2, bs2) t2 s3) ->
        t = t1 ** t2 ->
        fplus (s1, bs1) t s3.

End fstep.

  (* Theorem step_simulation s1 t s2 : *)
  (*   step ge s1 t s2 -> *)
  (*   forall ts1, *)
  (*     match_states s1 ts1 -> *)
  (*     exists ts2, plus step tge ts1 t ts2 /\ match_states s2 ts2. *)

Definition match_prog (prog tprog: program) :=
  match_program (fun cu f tf => transf_fundef f = OK tf) eq prog tprog.

Section FAULT_TOLERANCE.
  Variable prog: program.
  Variable tprog: program.
  Hypothesis TRANSF: match_prog prog tprog.
  Let ge := Genv.globalenv prog.
  Let tge := Genv.globalenv tprog.
  
  Variable match_states : RTL.state -> fstate -> Prop.
  
  Theorem fstep_simulation (s1 s2 : RTL.state) (t : trace) :
    RTL.step ge s1 t s2 ->
    forall ts1 bs1,
      faults_wf (ts1, bs1) ->
      match_states s1 (ts1, bs1) ->
      exists ts2 bs2, fplus tge (ts1, bs1) t ts2 /\ match_states s2 (ts2, bs2).
  Admitted.

End FAULT_TOLERANCE.

(* TODO: prove that the above implies the original soundness step
   simulation. Also do something else to validate the definition, to
   show that it captures what we think it does. It should maybe imply
   some property that has an easy intuitive meaning. *)
