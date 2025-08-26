Require Import Coqlib.
Require Import AST.
Require Import Csyntax.

Inductive is_vote_builtin : external_function -> Prop :=
| is_vote_int : forall sg,
    is_vote_builtin (EF_builtin "__builtin_vote_int" sg)
| is_vote_long : forall sg,
    is_vote_builtin (EF_builtin "__builtin_vote_long" sg)
| is_vote_single : forall sg,
    is_vote_builtin (EF_builtin "__builtin_vote_single" sg)
| is_vote_float : forall sg,
    is_vote_builtin (EF_builtin "__builtin_vote_float" sg).

Fixpoint no_votes_expr (e : expr) : Prop :=
  match e with
  | Efield l _f _ty => no_votes_expr l
  | Evalof l _ty => no_votes_expr l
  | Ederef r _ty => no_votes_expr r
  | Eaddrof l _ty => no_votes_expr l
  | Eunop _op r _ty => no_votes_expr r
  | Ebinop _op r1 r2 _ty => no_votes_expr r1 /\ no_votes_expr r2
  | Ecast r _ty => no_votes_expr r
  | Eseqand r1 r2 _ty => no_votes_expr r1 /\ no_votes_expr r2
  | Eseqor r1 r2 _ty => no_votes_expr r1 /\ no_votes_expr r2
  | Econdition r1 r2 r3 _ty =>
      no_votes_expr r1 /\ no_votes_expr r2 /\ no_votes_expr r3
  | Eassign l r _ty => no_votes_expr l /\ no_votes_expr r
  | Eassignop _op l r _tyres _ty => no_votes_expr l /\ no_votes_expr r
  | Epostincr _id l _ty => no_votes_expr l
  | Ecomma r1 r2 _ty => no_votes_expr r1 /\ no_votes_expr r2   
  | Ecall r1 rargs _ty => no_votes_expr r1 /\ no_votes_exprlist rargs
  | Ebuiltin ef _tyargs _rargs _ty => ~ is_vote_builtin ef
  | Eparen r _tycast _ty => no_votes_expr r
  | _ => True
  end
with
no_votes_exprlist (el : exprlist) : Prop :=
  match el with
  | Enil => True
  | Econs e rl => no_votes_expr e /\ no_votes_exprlist rl
  end.

Inductive no_votes_statement : statement -> Prop :=
| no_votes_Sskip : no_votes_statement Sskip
| no_votes_Sdo : forall e,
    no_votes_expr e ->
    no_votes_statement (Sdo e)
| no_votes_Ssequence : forall s1 s2,
    no_votes_statement s1 ->
    no_votes_statement s2 ->
    no_votes_statement (Ssequence s1 s2)
| no_votes_Sifthenelse : forall e s1 s2,
    no_votes_expr e ->
    no_votes_statement s1 ->
    no_votes_statement s2 ->
    no_votes_statement (Sifthenelse e s1 s2)
| no_votes_Swhile : forall e s,
    no_votes_expr e ->
    no_votes_statement s ->
    no_votes_statement (Swhile e s)
| no_votes_Sdowhile : forall e s,
    no_votes_expr e ->
    no_votes_statement s ->
    no_votes_statement (Sdowhile e s)
| no_votes_Sfor : forall s1 e s2 s3,
    no_votes_statement s1 ->
    no_votes_expr e ->
    no_votes_statement s2 ->
    no_votes_statement s3 ->
    no_votes_statement (Sfor s1 e s2 s3)
| no_votes_Sbreak : no_votes_statement Sbreak
| no_votes_Scontinue : no_votes_statement Scontinue
| no_votes_Sreturn_None :
  no_votes_statement (Sreturn None)
| no_votes_Sreturn_Some : forall e,
    no_votes_expr e ->
    no_votes_statement (Sreturn (Some e))
| no_vote_Sswitch : forall e ls,
    no_votes_expr e ->
    no_votes_labeled_statements ls ->
    no_votes_statement (Sswitch e ls)
| no_votes_Slabel : forall lbl s,
    no_votes_statement s ->
    no_votes_statement (Slabel lbl s)
| no_votes_Sgoto : forall lbl,
    no_votes_statement (Sgoto lbl)

with no_votes_labeled_statements : labeled_statements -> Prop :=
| no_votes_LSnil : no_votes_labeled_statements LSnil
| no_votes_LScons : forall oz s ls,
    no_votes_statement s ->
    no_votes_labeled_statements ls ->
    no_votes_labeled_statements (LScons oz s ls).

Inductive no_votes_fundef : Csyntax.fundef -> Prop :=
| no_votes_Internal : forall f,
    no_votes_statement f.(fn_body) ->
    no_votes_fundef (Ctypes.Internal f)
| no_votes_external : forall ef argtys retty cc,
    no_votes_fundef (Ctypes.External ef argtys retty cc).

Inductive no_votes_globdef : globdef (Ctypes.fundef Csyntax.function) Ctypes.type -> Prop :=
| no_votes_Gfun : forall fd,
    no_votes_fundef fd ->
    no_votes_globdef (Gfun fd)
| no_votes_Gvar : forall v,
    no_votes_globdef (Gvar v).

Inductive no_votes : Csyntax.program -> Prop :=
| no_votes_program : forall defs public main types comp_env comp_env_eq,
    Forall (fun id_def => no_votes_globdef (snd id_def)) defs ->
    no_votes {| Ctypes.prog_defs := defs
              ; Ctypes.prog_public := public
              ; Ctypes.prog_main := main
              ; Ctypes.prog_types := types
              ; Ctypes.prog_comp_env := comp_env
              ; Ctypes.prog_comp_env_eq := comp_env_eq |}.
