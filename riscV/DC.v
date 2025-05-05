Require Import Coqlib.
Require Import Lens.
Require Import BoolEqual.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Unityping.
Require Import Events.
Require Import Globalenvs.
Require Import Builtins.
Require Import Smallstep.
Require Import Locations.
Require Stacklayout.
Require Import Conventions.
Require Import Asm.
Require Asmgen.

Definition node : Type := positive.

(** All registers except [PC]. *)
Inductive reg : Type :=
| RI (_ : ireg)	(**r integer register *)
| RF (_ : freg).	(**r floating point register *)

Definition reg_beq : forall l1 l2 : reg, bool.
Proof.
  generalize ireg_eq freg_eq typ_eq Ptrofs.eq_dec. boolean_equality.
Defined.

Definition reg_eq : forall l1 l2 : reg, {l1 = l2} + {l1 <> l2}.
Proof. decidable_equality_from reg_beq. Defined.

(*
Variant kind : Type :=
| Kmv	(**r register colors vary *)
| Ksp	(**r callee slots have fixed colors, register colors vary *)
| Kfp	(**r caller slots are red, register colors vary *)
| Kflow	(**r control flow inputs must be red *)
| Kcomp	(**r computations within a color must be consistent *)
.

Variant instruction : Type :=

(** Moves *)
| Smv (rd rs : ireg) (s : node)	(**r integer to integer *)
| Sfmv (rd rs : freg) (s : node)	(**r FP to FP *)
| Sfmvxs (rd : ireg) (rs : freg) (s : node)	(**r single to integer *)
| Sfmvsx (rd : freg) (rs : ireg) (s : node)	(**r integer to single *)
| Sfmvxd (rd : ireg) (rs : freg) (s : node)	(**r double to integer *)
| Sfmvdx (rd : freg) (rs : ireg) (s : node)	(**r integer to double *)

(** Stack access *)
| Sgetstack (ofs : ptrofs) (ty : typ) (dst : reg) (s : node)
| Ssetstack (src : reg) (ofs : ptrofs) (ty : typ) (s : node)
| Sgetparam (ofs : ptrofs) (ty : typ) (dst : reg) (s : node)

(** Unconditional jumps. Links are to RA. *)
| Sj_l (s : node)
| Sj_s (symb : ident) (sg : signature)
| Sj_r (r : ireg) (sg : signature)
| Sjal_s (symb : ident) (sg : signature)
| Sjal_r (r : ireg) (sg : signature)

(** Conditional branches *)
| Sbeqw (rs1 rs2: ireg0) (ifso ifnot : node)	(**r branch-if-equal *)
| Sbnew (rs1 rs2: ireg0) (ifso ifnot : node)	(**r branch-if-not-equal signed *)
.

Definition code : Type := PTree.t instruction.

#[projections(primitive)]
Record state : Type := State {
  st_next : node;
  st_code : code;
  st_lab : PMap.t node;	(**r from [Plabel] *)
  st_wf_pc (pc : positive) : Plt pc st_next \/ st_code!pc = None;
}.

*)

(**
This is a pretty good sketch for decompilation. TODO:

- Decompile smoves and majority votes.

- Figure out if we can fix <<fn_link_ofs>> statically (as written) or
if we want to insist dynamically that all FP initializations use the
same offset or if we want to ignore the offset.

- In the monad, drop <<res>>. We just need backtracking.

- In the monad, add a counter of instructions consumed and use it to
build a control flow graph.
*)

Reserved Infix "$" (at level 65, right associativity).
Local Notation "f $ x" := (f x) (only parsing).
Local Notation FP := X30.
Local Notation TMP := X31.


Definition M (A : Type) : Type := code -> res (option (code * A)).

Definition ret {A} (x : A) : M A := fun c => OK (Some (c, x)).
Definition error {A} (e : errmsg) : M A := fun _ => Error e.
Definition backtrack {A} : M A := fun _ => OK None.
Definition orelse {A} (m : M A) (b : unit -> M A) : M A :=
  fun c =>
  match m c with
  | OK (Some _) as ret => ret
  | OK None => b tt c
  | Error e => Error e
  end.
Definition get : M code := fun c => OK (Some (c, c)).
Definition put (c : code) : M unit := fun _ => OK (Some (c, tt)).
Definition bind {A B} (m : M A) (f : A -> M B) : M B :=
  fun c =>
  match m c with
  | OK (Some (c, x)) => f x c
  | OK None => OK None
  | Error e => Error e
  end.
Definition fmap {A B} (f : A -> B) (m : M A) : M B :=
  fun c =>
  match m c with
  | OK (Some (c, x)) => OK (Some (c, f x))
  | OK None => OK None
  | Error e => Error e
  end.
Definition ap {A B} (f : M (A -> B)) (x : M A) : M B :=
  fun c =>
  match f c with
  | OK (Some (c, f)) =>
    match x c with
    | OK (Some (c, x)) => OK (Some (c, f x))
    | OK None => OK None
    | Error e => Error e
    end
  | OK None => OK None
  | Error e => Error e
  end.

#[global] Arguments ret _ & _ _ : assert.
#[global] Arguments orelse _ & _ _ _ : assert.
#[global] Arguments bind _ _ & _ _ _ : assert.
#[global] Arguments fmap _ _ & _ _ _ : assert.
#[global] Arguments ap _ _ & _ _ _ : assert.

Declare Scope mon_scope.
Delimit Scope mon_scope with mon.
#[global] Bind Scope mon_scope with M.

Reserved Notation "'assertion' A ; B" (at level 200, A at level 100, B at level 200).
Notation "'assertion' A ; B" := (if A then B else backtrack) : mon_scope.

Reserved Infix "<|>"  (at level 60, right associativity).
Notation "A <|> B" := (orelse A (fun _ => B%mon)) : mon_scope.

(*
Reserved Notation "''do'' X <- A ; B" (at level 200, X binder).
<<binder>>, <<closed binder>> don't work.
*)
Reserved Notation "''do'' X <- A ; B"
  (at level 200, X name, A at level 100, B at level 200).
Notation "'do' X <- A ; B" := (bind A (fun X => B%mon)) (only parsing) : mon_scope.
Reserved Infix ">>=" (at level 60, right associativity).
Infix ">>=" := bind : mon_scope.

Reserved Infix "<$>" (at level 61, left associativity).
Infix "<$>" := fmap : mon_scope.

Reserved Infix "<*>" (at level 61, left associativity).
Infix "<*>" := ap : mon_scope.

(** Match any instruction, or backtrack *)
Definition instr : M (instruction) :=
  fun c =>
  match c with
  | nil => OK None
  | i :: c => OK (Some (c, i))
  end.

(**
A parser for [Asmgen.indexed_memory_access].

Lots of backtracking: We aim for simplicity rather than efficiency.
*)

#[projections(primitive)]
Record ima {A : Type} : Type := IMA {
  ima_type : typ;
  ima_reg : reg;	(**v destination (load) or source (store) *)
  ima_base : ireg;
  ima_ofs : A;
}.
#[global] Arguments ima : clear implicits.
#[global] Arguments IMA {_} _ _ _ _ : assert.
Add Printing Constructor ima.

Definition _ima_base {A} : ima A -l> ireg := {|
  lens_view r := r.(ima_base);
  lens_over f r := IMA r.(ima_type) r.(ima_reg) (f r.(ima_base)) r.(ima_ofs);
|}.
Definition _ima_ofs {A B : Type} : lens (ima A) (ima B) A B := {|
  lens_view r := r.(ima_ofs);
  lens_over f r := IMA r.(ima_type) r.(ima_reg) r.(ima_base) (f r.(ima_ofs));
|}.

Definition imm64_pair (hi lo : int64) : int64 :=
  Int64.add (Int64.sign_ext 32 (Int64.shl hi (Int64.repr 12))) lo.
Definition imm32_pair (hi lo : int) : int :=
  Int.add (Int.shl hi (Int.repr 12)) lo.

Section indexed_memory_access.
  Context (op : instruction -> M (ima offset)).

  Definition ima_imm_single : M (ima ptrofs) :=
    do r <- (instr >>= op);
    match r.(ima_ofs) with
    | Ofsimm ofs => ret (r # .[_ima_ofs <- ofs])%lens
    | _ => backtrack
    end.
  Definition ima_imm64_pair : M (ima ptrofs) :=
    do hi <- instr;
    do lo <- instr;
    do r <- instr >>= op;
    assertion ireg_eq r.(ima_base) TMP;
    match hi, lo, r.(ima_ofs) with
    | Pluil TMP hi, Paddl TMP (X base) TMP, Ofsimm lo =>
      let ofs := Ptrofs.of_int64 (imm64_pair hi (Ptrofs.to_int64 lo)) in
      ret (IMA r.(ima_type) r.(ima_reg) base ofs)
    | _, _, _ => backtrack
    end.
  Definition ima_imm64_large : M (ima ptrofs) :=
    do imm <- instr;
    do add <- instr;
    do r <- (instr >>= op);
    assertion ireg_eq r.(ima_base) TMP;
    match imm, add, r.(ima_ofs) with
    | Ploadli TMP imm, Paddl TMP (X base) TMP, Ofsimm ofs =>
      assertion Ptrofs.eq ofs Ptrofs.zero;
      ret (IMA r.(ima_type) r.(ima_reg) base (Ptrofs.of_int64 imm))
    | _, _, _ => backtrack
    end.
  Definition ima_imm32_pair : M (ima ptrofs) :=
    do hi <- instr;
    do lo <- instr;
    do r <- (instr >>= op);
    assertion ireg_eq r.(ima_base) TMP;
    match hi, lo, r.(ima_ofs) with
    | Pluiw TMP hi, Paddw TMP (X base) TMP, Ofsimm lo =>
      let ofs := Ptrofs.of_int (imm32_pair hi (Ptrofs.to_int lo)) in
      ret (IMA r.(ima_type) r.(ima_reg) base ofs)
    | _, _, _ => backtrack
    end.
  Definition indexed_memory_access : M (ima ptrofs) :=
    if Archi.ptr64
    then ima_imm_single <|> ima_imm64_pair <|> ima_imm64_large
    else ima_imm_single <|> ima_imm32_pair.
End indexed_memory_access.

Definition loadind : M (ima ptrofs) :=
  indexed_memory_access $ fun i =>
  match i with
  | Plw rd ra ofs => ret (IMA Tint (RI rd) ra ofs)
  | Pld rd ra ofs => ret (IMA Tlong (RI rd) ra ofs)
  | Pfls rd ra ofs => ret (IMA Tsingle (RF rd) ra ofs)
  | Pfld rd ra ofs => ret (IMA Tfloat (RF rd) ra ofs)
  | Plw_a rd ra ofs => ret (IMA Tany32 (RI rd) ra ofs)
  | Pld_a rd ra ofs => ret (IMA Tany64 (RI rd) ra ofs)
  | Pfld_a rd ra ofs => ret (IMA Tany64 (RF rd) ra ofs)
  | _ => backtrack
  end.

Definition storeind : M (ima ptrofs) :=
  indexed_memory_access $ fun i =>
  match i with
  | Psw rs ra ofs => ret (IMA Tint (RI rs) ra ofs)
  | Psd rs ra ofs => ret (IMA Tlong (RI rs) ra ofs)
  | Pfss rs ra ofs => ret (IMA Tsingle (RF rs) ra ofs)
  | Pfsd rs ra ofs => ret (IMA Tfloat (RF rs) ra ofs)
  | Psw_a rs ra ofs => ret (IMA Tany32 (RI rs) ra ofs)
  | Psd_a rs ra ofs => ret (IMA Tany64 (RI rs) ra ofs)
  | Pfsd_a rs ra ofs => ret (IMA Tany64 (RF rs) ra ofs)
  | _ => backtrack
  end.

Definition loadind_ptr : M (ima ptrofs) :=
  indexed_memory_access $ fun i =>
  if Archi.ptr64 then
    match i with
    | Pld rd ra ofs => ret (IMA Tlong (RI rd) ra ofs)
    | _ => backtrack
    end
  else
    match i with
    | Plw rd ra ofs => ret (IMA Tint (RI rd) ra ofs)
    | _ => backtrack
    end.

Definition storeind_ptr : M (ima ptrofs) :=
  indexed_memory_access $ fun i =>
  if Archi.ptr64 then
    match i with
    | Psd rs ra ofs => ret (IMA Tlong (RI rs) ra ofs)
    | _ => backtrack
    end
  else
    match i with
    | Psw rs ra ofs => ret (IMA Tint (RI rs) ra ofs)
    | _ => backtrack
    end.

Variant special_instr : Type :=
| Sgetstack (ofs : ptrofs) (ty : typ) (dst : reg)
| Ssetstack (src : reg) (ofs : ptrofs) (ty : typ)
| Sgetparam (ofs : ptrofs) (ty : typ) (dst : reg).

Definition getstack : M special_instr :=
  do r <- loadind;
  assertion ireg_eq r.(ima_base) SP;
  ret (Sgetstack r.(ima_ofs) r.(ima_type) r.(ima_reg)).

Definition setstack : M special_instr :=
  do r <- storeind;
  assertion ireg_eq r.(ima_base) SP;
  ret (Ssetstack r.(ima_reg) r.(ima_ofs) r.(ima_type)).

Definition getparam_fp : M special_instr :=
  do r <- loadind;
  assertion ireg_eq r.(ima_base) FP;
  ret (Sgetparam r.(ima_ofs) r.(ima_type) r.(ima_reg)).
Definition getparam_nofp (fn_link_ofs : ptrofs) : M special_instr :=
  do r <- loadind_ptr;
  assertion ireg_eq r.(ima_base) SP;
  assertion reg_eq r.(ima_reg) (RI FP);
  assertion Ptrofs.eq r.(ima_ofs) fn_link_ofs;
  getparam_fp.
Definition getparam (fn_link_ofs : ptrofs) : M special_instr :=
  getparam_fp <|> getparam_nofp fn_link_ofs.

Definition special (fn_link_ofs : ptrofs) : M special_instr :=
  getstack <|> setstack <|> getparam fn_link_ofs.

Variant abstract_instr : Type :=
| Special (i : special_instr)
| Compute (i : instruction)	(* TODO: side-cond: <<i>> not special *)
.

Definition abstract (fn_link_ofs : ptrofs) : M abstract_instr :=
  (Special <$> special fn_link_ofs)
  <|> (Compute <$> instr).

Definition abstract_code (fn_link_ofs : ptrofs) : M code :=
  (*
  TODO: This can be a fuel-based fixpoint (|code|) or we may be able
  to use CompCert's iterators library.
  *)
  ret nil.

(** Thoughts on side-conditions... *)

Variant maj_vote_builtin : replicate_builtin -> Prop :=
| maj_vote_builtin_int : maj_vote_builtin BI_vote_int
| maj_vote_builtin_long : maj_vote_builtin BI_vote_long
| maj_vote_builtin_single : maj_vote_builtin BI_vote_single
| maj_vote_builtin_float : maj_vote_builtin BI_vote_float.

Variant maj_vote (i : instruction) : Prop :=
| maj_vote_intro name sg args res f :
  i = Pbuiltin (EF_runtime name sg) args res ->
  lookup_builtin_function name sg = Some (BI_replicate f) ->
  maj_vote_builtin f ->
  maj_vote i.

Definition maj_voteb (i : instruction) : bool :=
  match i with
  | Pbuiltin (EF_runtime name sg) _ _ =>
    match lookup_builtin_function name sg with
    | Some f =>
      match f with
      | BI_replicate f =>
        match f with
        | BI_vote_int | BI_vote_long | BI_vote_single | BI_vote_float => true
        | _ => false
        end
      | _ => false
      end
    | None => false
    end
  | _ => false
  end.

Lemma maj_voteP i : reflect (maj_vote i) (maj_voteb i).
Proof.
  Local Ltac destruct_type ty :=
    lazymatch goal with
    | H : ty |- _ => destruct H; try discriminate
    end.
  destruct (maj_voteb _) eqn:Hi; constructor; unfold maj_voteb in Hi.
  { destruct i; try discriminate.
    destruct_type external_function.
    destruct (lookup_builtin_function _ _) eqn:?; try discriminate.
    destruct_type builtin_function.
    destruct_type replicate_builtin.
    all: econstructor; eauto.
    all: constructor. }
  { destruct i; try discriminate.
    all: inversion_clear 1 as [????? Hi' Hlookup Hvote]; try discriminate.
    inv Hi'. rewrite Hlookup in Hi.
    destruct_type replicate_builtin.
    all: inv Hvote. }
Qed.

Definition maj_vote_dec i := reflect_dec _ _ (maj_voteP i).
(*
Approach:

syntax :=
| getparam
| getstack | setstack
| maj_vote
| smove
| other (i : instruction) (~ getparam i) ... (~ maj_vote i) (~ smove i)
.

where other carries evidence that <<i>> isn't one of the special instructions.

Better might be

special ::=
| getparam
| getstack | setstack
| maj_vote
| smove

is_special : instruction -> option special

syntax ::= special | other (i : instruction) (is_special i = None)

*)

Inductive location : Type :=
| IR (_ : ireg)	(**r integer register *)
| FR (_ : freg)	(**r floating point register *)
| S (_ : ptrofs) (_ : typ)	(**r callee stack frame, offset from SP *)
| F (_ : ptrofs) (_ : typ)	(**r caller stack frame, offset from FP *)
.

Definition location_beq : forall l1 l2 : location, bool.
Proof.
  generalize ireg_eq freg_eq typ_eq Ptrofs.eq_dec. boolean_equality.
Defined.

Definition location_eq : forall l1 l2 : location, {l1 = l2} + {l1 <> l2}.
Proof. decidable_equality_from location_beq. Defined.

Module LEq.
  Definition t := location.
  Definition eq := location_eq.
End LEq.

Module LM := EMap(LEq).
