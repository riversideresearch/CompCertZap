Require Import
  AST
  Errors
  Events
  Globalenvs
  Linking
  List
  Maps
  Registers
  Replicate
  Replicatespec
  (* Replicateproof *)
  RTL
  RTLtyping
  Smallstep
  Values
.
Import ListNotations.

Definition fstate := (RTL.state * list bool)%type.

(** Describes how normal execution affects the fault state. A function
    from the first three arguments (initial RTL state and its fault
    state, and final RTL state) to the final fault state. *)
Inductive next : fstate -> fstate -> Prop :=
| next_State : forall stk f sp pc rs m stk' f' sp' pc' rs' m' bs,
    next (State stk f sp pc rs m, bs) (State stk' f' sp' pc' rs' m', bs)
(* | next_Callstate : forall stk f args m stk' f' args' m' bs, *)
(*     next (Callstate stk f args m, bs) (Callstate stk' f' args' m', bs) *)
(* | next_Returnstate : forall stk v m stk' v' m' *)
(*     next (Callstate stk f args m, bs) (Callstate stk' f' args' m', bs) *)
.
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

(* Inductive faults_wf : fstate -> Prop := *)
(* | faults_wf_State : forall frame stk f sp pc rs m b bs, *)
(*     faults_wf (State stk f sp pc rs m, bs) -> *)
(*     faults_wf (State (frame :: stk) f sp pc rs m, b :: bs). *)
(* (* TODO: Callstate and Returnstate *) *)

(** Zap relation *)
Inductive zap : fstate -> fstate -> Prop :=
  (* Assign arbitrary value to arbitrary register. *)
  zap_reg : forall stk f sp pc rs m bs r v,
      zap (State stk f sp pc rs m, false :: bs)
        (State stk f sp pc (rs # r <- v) m, true :: bs).

Section fstep.
  Variable ge : genv.

  (** Step relation lifted to states augmented with fault state. Uses
      the [next] relation to allow normal execution to affect the
      fault state (e.g., pushing/popping the fault budget stack). *)
  Inductive fstep : fstate -> trace -> fstate -> Prop :=
  | fstep_step : forall s s' bs bs' t,
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

(* Definition match_fstate (s1 s2 : RTL.state) (bs : list bool) : Prop := *)
(*   match_states s1 s2 /\ *)
(*     True. *)
(* TODO: match_regsets depends on top of bs. Include faults_wf here.  *)

(* TODO: refactor this as described in liveness2 branch? (generalize
   reg_used to an arbitrary predicate to enable easier induction). *)
Definition match_regsets
  (params : list reg) (c : code) (rm : replmap) (rs rs' : regset) (b : bool) : Prop :=
    forall r1, reg_used params c r1 ->
          forall r2 r3 : reg,
            rm # r1 = (r2, r3) ->
            if b then
              rs # r1 = rs' # r1 /\
                rs # r1 = rs' # r2 /\
                rs # r1 = rs' # r3
            else
              (rs # r1 = rs' # r1 /\
                 rs # r1 = rs' # r2) \/
                (rs # r1 = rs' # r1 /\
                   rs # r1 = rs' # r3) \/
                (rs # r1 = rs' # r2 /\
                   rs # r1 = rs' # r3).

Inductive match_stackframes : list stackframe -> list stackframe -> list bool -> signature -> Prop :=
| match_stackframes_nil : forall sig b,
    sig.(sig_res) = Xint ->
    match_stackframes [] [] [b] sig
| match_stackframes_cons :
  forall stk tstk sig re rm res1 f tf sp pc rs trs res2 res3 n b bs
    (* Well-typed *)
    (WT_FN : wt_function f re)
    (WT_RS : wt_regset re rs)
    (WT_RES : re res1 = proj_sig_res sig)
    (* Match *)
    (FUN : match_function re rm f tf)
    (REGS : match_regsets f.(fn_params) f.(fn_code) rm rs trs b)
    (RM_WF : rm_wf rm (fun_regs_list f)),
    reg_used_in_code f.(fn_code) res1 ->
    rm # res1 = (res2, res3) ->
    smoveR tf.(fn_code) (re res1) res1 res2 res3 n pc ->
    match_stackframes stk tstk bs (fn_sig f) ->
    match_stackframes
      (Stackframe res1 f sp pc rs :: stk)
      (Stackframe res1 tf sp n trs :: tstk) (b :: bs) sig.

Inductive match_states : RTL.state -> fstate -> Prop :=
| match_regular_states :
  forall stk tstk f tf sp pc rs rs' m re rm b bs
    (* Well-typed *)
    (WT_FN: wt_function f re)
    (WT_RS: wt_regset re rs)
    (* Match *)
    (STACKS: match_stackframes stk tstk (b :: bs) (fn_sig f))
    (FUN : match_function re rm f tf)
    (REGS : match_regsets f.(fn_params) f.(fn_code) rm rs rs' b),
    match_states (State stk f sp pc rs m) (State tstk tf sp pc rs' m, (b :: bs))
| match_call_states :
  forall stk tstk f tf args m bs
    (* Well-typed *)
    (WT_ARGS: Val.has_type_list args (proj_sig_args (funsig f)))
    (* Match *)
    (STACKS: match_stackframes stk tstk bs (funsig f))
    (FUN : match_fundef f tf),
    match_states (Callstate stk f args m) (Callstate tstk tf args m, bs)
| match_return_states :
  forall sig stk tstk v m bs
    (* Well-typed *)
    (WT_RES : Val.has_type v (proj_sig_res sig))
    (* Match *)
    (STACKS: match_stackframes stk tstk bs sig),
    match_states (Returnstate stk v m) (Returnstate tstk v m, bs).

Section FAULT_TOLERANCE.
  Variable prog: program.
  Variable tprog: program.
  Hypothesis TRANSF: match_prog prog tprog.
  Let ge := Genv.globalenv prog.
  Let tge := Genv.globalenv tprog.
  
  (* Variable match_states : RTL.state -> fstate -> Prop. *)
  
  Theorem fstep_simulation (s1 s2 : RTL.state) (t : trace) :
    RTL.step ge s1 t s2 ->
    forall ts1 bs1,
      match_states s1 (ts1, bs1) ->
      exists ts2 bs2, fplus tge (ts1, bs1) t ts2 /\ match_states s2 (ts2, bs2).
  Admitted.

End FAULT_TOLERANCE.

(* TODO: prove that the above implies the original soundness step
   simulation. Also do something else to validate the definition, to
   show that it captures what we think it does. It should maybe imply
   some property that has an easy intuitive meaning. *)
