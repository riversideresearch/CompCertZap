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
Require Import Regcode.

Local Unset Elimination Schemes.

Local Close Scope asm.

(** * Sketch symbolic evaluation *)

(** ** Expressions *)

Inductive kind : Type :=
| Kptrofs
| Kval
| Kblock
| Kmem
| Kpair (_ _ : kind).

Fixpoint interp_kind (k : kind) : Type :=
  match k with
  | Kptrofs => ptrofs
  | Kval => val
  | Kblock => block
  | Kmem => mem
  | Kpair k1 k2 => interp_kind k1 * interp_kind k2
  end.

Declare Scope kind_scope.
Delimit Scope kind_scope with kind.
#[global] Bind Scope kind_scope with kind.

Infix "*" := Kpair : kind_scope.

Inductive expr : kind -> Type :=
(**
Offsets are syntactic because <<eval_offset>> can get stuck in
<<low_half>>. (This may not be necessary.)
*)
| Ptrofs (ofs : ptrofs) : expr Kptrofs
| Offset (ofs : offset) : expr Kptrofs

(** Values *)
| Val (v : val) : expr Kval
| Offsetptr (e : expr Kval) (ofs : expr Kptrofs) : expr Kval
| Loadv (chunk : memory_chunk) (m : expr Kmem) (addr : expr Kval) : expr Kval
| Addl (v1 v2 : expr Kval) : expr Kval

(** Memory blocks *)
| Block (b : block) : expr Kblock

(** Memories *)
| Mem (m : mem) : expr Kmem
| Storev (chunk : memory_chunk) (m : expr Kmem) (addr v : expr Kval) : expr Kmem
| Alloc (m : expr Kmem) (lo hi : Z) : expr (Kmem * Kblock)
| Free (m : expr Kmem) (b : expr Kblock) (lo hi : Z) : expr Kmem

(** Pairs *)
| Pair {k1 k2} (e1 : expr k1) (e2 : expr k2) : expr (k1 * k2)
| Fst {k1 k2} (e : expr (k1 * k2)) : expr k1
| Snd {k1 k2} (e : expr (k1 * k2)) : expr k2
.

Declare Scope expr_scope.
Delimit Scope expr_scope with expr.
#[global] Bind Scope expr_scope with expr.

Infix "+" := Addl : expr_scope.
Notation "( x , y , .. , z )" := (Pair .. (Pair x y) .. z) : expr_scope.

Notation vexpr := (expr Kval).
Notation bexpr := (expr Kblock).
Notation mexpr := (expr Kmem).

Definition obind_else {A B} (m : option A) (f : A -> res B) (e : unit -> res B) : res B :=
  match m with
  | Some x => f x
  | None => e tt
  end.
#[global] Arguments obind_else _ _ !_ _ _ / : simpl nomatch, assert.

Delimit Scope error_monad_scope with res.
Notation "'letr' X <- A ; B" := (bind A (fun X => B))
  (at level 200, X binder, A at level 100, B at level 200) : error_monad_scope.
Notation "'leto' X <- A 'else' E ; B" := (obind_else A (fun X => B) (fun _ => E))
  (at level 200, X binder, A at level 100, B, E at level 200) : error_monad_scope.

Definition interp_expr (ge : genv) :=
fix interp_expr {k} (e : expr k) : res (interp_kind k) :=
  match e in expr k return res (interp_kind k) with
  | Ptrofs ofs => OK ofs
  | Offset ofs => OK (eval_offset ge ofs)
  | Val v => OK v
  | Offsetptr e eofs =>
    letr v <- interp_expr e;
    letr ofs <- interp_expr eofs;
    OK (Val.offset_ptr v ofs)
  | Loadv chunk em eaddr =>
    letr m <- interp_expr em;
    letr addr <- interp_expr eaddr;
    leto v <- Mem.loadv chunk m addr else Error (msg "Mem.loadv");
    OK v
  | Addl e1 e2 =>
    letr v1 <- interp_expr e1;
    letr v2 <- interp_expr e2;
    OK (Val.addl v1 v2)
  | Block b => OK b
  | Mem m => OK m
  | Storev chunk em eaddr ev =>
    letr m <- interp_expr em;
    letr addr <- interp_expr eaddr;
    letr v <- interp_expr ev;
    leto m <- Mem.storev chunk m addr v else Error (msg "Mem.storev");
    OK m
  | Alloc em lo hi =>
    letr m <- interp_expr em;
    OK (Mem.alloc m lo hi)
  | Free em eb lo hi =>
    letr m <- interp_expr em;
    letr b <- interp_expr eb;
    leto m <- Mem.free m b lo hi else Error (msg "Mem.free");
    OK m
  | Pair e1 e2 =>
    letr v1 <- interp_expr e1;
    letr v2 <- interp_expr e2;
    OK (v1, v2)
  | Fst e => letr v <- interp_expr e; OK (fst v)
  | Snd e => letr v <- interp_expr e; OK (snd v)
  end%res.
#[global] Arguments interp_expr _ _ !_ / : simpl nomatch, assert.

(** ** First order logic *)

Inductive pred : Type :=
| pred_true
| pred_and (P1 P2 : pred)
| pred_impl (P1 P2 : pred)
| pred_forall {k} (P : interp_kind k -> pred)
| pred_eq {k} (e1 e2 : expr k)
| pred_neq {k} (e1 e2 : expr k)
.

Declare Scope pred_scope.
Delimit Scope pred_scope with pred.
#[global] Bind Scope pred_scope with pred.

Infix "/\" := pred_and : pred_scope.
Infix "->" := pred_impl : pred_scope.
Infix "=" := pred_eq : pred_scope.
Infix "<>" := pred_neq : pred_scope.

Definition interp_pred (ge : genv) :=
fix interp_pred (p : pred) : Prop :=
  match p with
  | pred_true => True
  | pred_and P1 P2 => interp_pred P1 /\ interp_pred P2
  | pred_impl P1 P2 => interp_pred P1 -> interp_pred P2
  | pred_forall P => forall x, interp_pred (P x)
  | pred_eq e1 e2 =>
    forall v1 v2,
    interp_expr ge e1 = OK v1 ->
    interp_expr ge e2 = OK v2 ->
    v1 = v2
  | pred_neq e1 e2 =>
    forall v1 v2,
    interp_expr ge e1 = OK v1 ->
    interp_expr ge e2 = OK v2 ->
    v1 <> v2
  end.
#[global] Arguments interp_pred _ !_ / : simpl nomatch, assert.

(** ** Symbolic execution *)

(**
NOTE: The FT TAL paper builds on such static expressions with

- closing substitutions `S` for value and memory expressions

- `Δ |- E₁ = E₂` judgmental equality

- `Ψ |- n : b` flexibly typing numerals `n` as base type `int` or the type of values at address `n` in memory

- `Ψ; Δ |-^z v : t` value typing

- `Ψ; Θ |- ir => RT` instruction typing

As we embed FOL inside Coq's logic, we need neither expression
contexts Δ nor substitutions S.

We would need memory contexts Ψ to establish memory safety, but
CompCert establishes memory safety by other means. (We benefit from
the guards and properties baked into CompCert's type [mem].)

We need register contexts Γ (the following type [regset]) tracking a
register's color, base type, and symbolic value. Base types <<base ≈
option state>> record, for registers housing code pointers, branch
preconditions. (CompCert's types serve little purpose at this level,
as RISC-V registers have fixed types.)
*)

Inductive color :=
| R | G | B	(* replicated *)
| W.	(* unreplicated/shared *)

Definition color_beq : forall c1 c2 : color, bool.
Proof. boolean_equality. Defined.

Definition color_eq : forall c1 c2 : color, {c1 = c2} + {c1 <> c2}.
Proof. decidable_equality_from color_beq. Defined.

(*
We do not want to work this way.
We need a per-PC assignment of colors to registers.

Module CEq.
  Definition t := color.
  Definition eq := color_eq.
  Definition default := W.
End CEq.
Module CU := UniSolver(CEq).

Definition colorenv : Type := CU.typenv.

Definition initial : colorenv := CU.initial.

Definition set (e : colorenv) (r : preg) (c : color) : res colorenv :=
  CU.set e (encode_preg r) c.

Definition unify (e : colorenv) (r1 r2 : preg) : res (bool * colorenv) :=
  CU.move e (encode_preg r1) (encode_preg r2).

Open Scope error_monad_scope.
Definition my_env : res colorenv :=
  letr e <- set initial X1 G;
  letr '(_, e) <- unify e X1 X2;
  letr e <- set e X2 B;
  OK e.

Compute decode_preg 5.
Compute my_env.
*)

#[projections(primitive)]
Record reg' {base : Type} : Type := Reg {
  r_color : color;	(**r color *)
  r_type : base;	(**r base type *)
  r_val : vexpr;	(**r symbolic value *)
}.
Add Printing Constructor reg'.
#[global] Arguments reg' : clear implicits.
#[global] Arguments Reg {_} _ _ _ : assert.

Definition regset' (base : Type) : Type := Pregmap.t (reg' base).

(**
State accumulated while examining a function's code, serving also as
branch preconditions.
*)
#[projections(primitive)]
Record state' {base : Type} : Type := State {
  state_regs : regset' base;	(**r register types *)
  state_mem : mexpr;	(**r symbolic memory *)
}.
Add Printing Constructor state'.
#[global] Arguments state' : clear implicits.
#[global] Arguments State {_} _ _ : assert.

Inductive base : Type :=
| Code (pre : state' base)	(**r branch target precondition *)
| Ref (b : base)	(** placeholder for reference types at reg,offset *)
| Other.	(**r other value *)
#[global] Arguments base : clear implicits.

Notation reg := (reg' base).
Notation regset := (regset' base).
Notation state := (state' base).

Definition reg_undef : reg :=
  Reg W Other (Val Vundef).
Definition regset_empty : regset :=
  Pregmap.init reg_undef.
Definition state_empty : state :=
  State regset_empty (Mem Mem.empty).

Definition _color : reg -l> color := {|
  lens_view r := r.(r_color);
  lens_over f r := Reg (f r.(r_color)) r.(r_type) r.(r_val);
|}.
Definition _type : reg -l> base := {|
  lens_view r := r.(r_type);
  lens_over f r := Reg r.(r_color) (f r.(r_type)) r.(r_val);
|}.
Definition _val : reg -l> vexpr := {|
  lens_view r := r.(r_val);
  lens_over f r := Reg r.(r_color) r.(r_type) (f r.(r_val));
|}.

Definition _preg (r : preg) : regset -l> reg := {|
  lens_view rs := rs r;
  lens_over f rs := Pregmap.set r (f (rs r)) rs;
|}.
Definition _ireg (r : ireg) : regset -l> reg := _preg (IR r).
Definition _freg (r : freg) : regset -l> reg := _preg (FR r).
Definition _ireg0w (r : ireg0) : regset -l> reg :=
  match r with
  | X0 => lens_const (Reg W Other (Val (Vint Int.zero)))
  | X r => _ireg r
  end.
Definition _ireg0l (r : ireg0) : regset -l> reg :=
  match r with
  | X0 => lens_const (Reg W Other (Val (Vlong Int64.zero)))
  | X r => _ireg r
  end.

Definition _regs : state -l> regset := {|
  lens_view s := s.(state_regs);
  lens_over f s := {|
    state_regs := f s.(state_regs);
    state_mem := s.(state_mem);
  |};
|}.
Definition _mem : state -l> mexpr := {|
  lens_view s := s.(state_mem);
  lens_over f s := {|
    state_regs := s.(state_regs);
    state_mem := f s.(state_mem);
  |};
|}.

(*
Check lens_view _color (lens_view (_ireg X3) (lens_view _regs state_empty)).
Check (state_empty.[_regs].[_ireg X3].[_color])%lens.

Check lens_set _color R regtype_undef.
Check (regtype_undef # .[_color <- R])%lens.

Check lens_compose _regs (lens_compose (_ireg X3) _color).
Check (_regs \; _ireg X3 \; _color)%lens.
Check (state_empty # .[_regs \; _ireg X3 \; _color <- R])%lens.
*)

Local Open Scope lens_scope.

Variant outcome : Type :=
| Next (rs : regset) (m : mexpr)
| Stuck.

(*
TODO: Dispense with <<nextinstr>> if we don't do anything meaningful
with the PC's value.
*)
Definition nextinstr (rs : regset) : regset :=
  rs # .[_preg PC \; _val <- Offsetptr rs.[_preg PC \; _val] (Ptrofs Ptrofs.one)].

Definition exec_load (chunk : memory_chunk) (rs : regset) (m : mexpr)
    (d : preg) (a : ireg) (ofs : offset) : outcome :=
  let a := rs.[_ireg a] in
  (*
  TODO (TYPING): This base type is wrong. We want to check that
  register <<a>> offset by <<ofs>> has type <<ref t>>. Then, we can
  set the destination register's type to <<t>>.
  *)
  let t := Other in	(* this is wrong *)
  let v := Loadv chunk m (Offsetptr a.(r_val) (Offset ofs)) in
  Next (nextinstr (rs # .[_preg d <- Reg a.(r_color) t v])) m.

Definition exec_instr (f : function) (i : instruction)
    (rs : regset) (m : mexpr) : outcome :=
  match i with
  | Pmv d s => Next (nextinstr (rs # .[_ireg d <- rs.[_ireg s]])) m

  | Paddil d s i =>
    let s := rs.[_ireg0l s] in
    let v := Addl s.(r_val) (Val (Vlong i)) in
    Next (nextinstr (rs # .[_preg d <- Reg s.(r_color) Other v])) m

  | Pld d a ofs => exec_load Mint64 rs m d a ofs

  | _ => Stuck
  end.

STOP.
Print state'.
Print regset'.
Print regtype'.
Print Scope asm.

Fixpoint eval_code (ce : CU.typenv) (s : state) (acc : pred) (c : code) {struct c} : res pred :=
  match c with
  | nil => OK acc
  | Pld d a ofs :: c =>
    Error (msg "eval_code")
  | _ => Error (msg "eval_code")
  end.
  | Pmv d s :: c =>
    do _ <- unify (LM.get (IR s) colors) (LM.get (IR d) colors);
    let v := LM.get (IR s) vals in
    let vals := LM.set (IR d) v vals in
    let acc := Form.color_eq (IR d) (IR s) /\ acc in
    eval_code vals colors acc c
(** State for a register *)





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

#[projections(primitive)]
Record triple {A : Type} : Type := Triple {
  red : A;
  green : A;
  blue : A;
}.
#[global] Arguments triple : clear implicits.
#[global] Arguments Triple {_} _ _ _ : assert.


#[projections(primitive)]
Record tag {A} : Type := Tag {
  tag_color : color;
  tag_val : A;
}.
#[global] Arguments tag : clear implicits.
#[global] Arguments Tag {_} _ _ : assert.
Add Printing Constructor tag.

(*
We treat a value's color as part of its type, separately
from its symbolic expression.
*)

(** ** Locations *)

Definition valmap := LM.t vexpr.
Definition colormap := LM.t color.

Notation "m # l" := (LM.get l m).

Parameter unify : color -> color -> res unit.

Fixpoint eval_code (vals : valmap) (colors : colormap) (acc : pred) (c : code) {struct c} : res pred :=
  match c with
  | nil => OK acc
  | Pld d a ofs :: c =>
    Error (msg "eval_code")
  | _ => Error (msg "eval_code")
  end.
  | Pmv d s :: c =>
    do _ <- unify (LM.get (IR s) colors) (LM.get (IR d) colors);
    let v := LM.get (IR s) vals in
    let vals := LM.set (IR d) v vals in
    let acc := Form.color_eq (IR d) (IR s) /\ acc in
    eval_code vals colors acc c

fix eval_instr (i : instruction) (s : state) (rec : ) : A :=
  match i with

  | Pmv d s => k (OK (val_eq (IR d) (IR s) /\ color_eq (IR d) (IR s)))

  | _ => k (Error (msg "eval_instr"))
  end.
