(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(* *********************************************************************)

(** Shared fault-model classification policy for operations and builtins. *)

Require Import Coqlib.
Require Import AST Builtins Op.

(** * Operation classification *)

(* Design note: maybe we can just assume faulted floats aren't NaN,
   and then the conversions from single/float to int/long will always
   succeed and we can consider them safe?

   It seems that considering NaN conversions to int/long to be
   immediate UB is a CompCert choice that isn't necessarily dictated
   by the C standard. *)
Inductive is_protected : operation -> Prop :=
  (* Because division by zero causes immediate UB (see [Val.divs] in
     common/Values.v) *)
  | is_protected_Odiv : is_protected Odiv
  | is_protected_Odivu : is_protected Odivu
  | is_protected_Omod : is_protected Omod
  | is_protected_Omodu : is_protected Omodu
  | is_protected_Odivl : is_protected Odivl
  | is_protected_Odivlu : is_protected Odivlu
  | is_protected_Omodl : is_protected Omodl
  | is_protected_Omodlu : is_protected Omodlu

  (* Trying to convert NaN (and maybe something else) causes immediate
     UB (see Val.intoffloat in common/Values.v) *)
  | is_protected_Ointofsingle : is_protected Ointofsingle
  | is_protected_Ointoffloat : is_protected Ointoffloat
  | is_protected_Olongofsingle : is_protected Olongofsingle
  | is_protected_Olongoffloat : is_protected Olongoffloat

  (* Shifting more than the archi word size is immediate UB (see Val.shl
     in common/Values.v) *)
  | is_protected_Oshl : is_protected Oshl
  | is_protected_Oshr : is_protected Oshr
  | is_protected_Oshru : is_protected Oshru
  | is_protected_Oshll : is_protected Oshll
  | is_protected_Oshrl : is_protected Oshrl
  | is_protected_Oshrlu : is_protected Oshrlu

(* Subtracting pointers in different blocks causes immediate UB (see
   [Val.subl] in common/Values.v) *)
  | is_protected_Osubl : Archi.ptr64 = true -> is_protected Osubl

  (* A faulty selection can cause the faulty execution to take Vundef
     into a register that the normal execution has a defined value for,
     and subsequently encounter UB that the normal execution avoids. See
     [Val.select] in common/Values.v. *)
  | is_protected_Osel : forall cond ty, is_protected (Osel cond ty)

  (* Comparing pointers in different blocks or comparing a pointer with
     a nonzero integer causes immediate UB. *)
  | is_protected_Ocmp_Ccompu : forall c, Archi.ptr64 = false ->
                                 is_protected (Ocmp (Ccompu c))
  | is_protected_Ocmp_Ccompuimm : forall c n, Archi.ptr64 = false ->
                                      is_protected (Ocmp (Ccompuimm c n))
  | is_protected_Ocmp_Ccomplu : forall c, Archi.ptr64 = true ->
                                  is_protected (Ocmp (Ccomplu c))
  | is_protected_Ocmp_Ccompluimm : forall c n, Archi.ptr64 = true ->
                                       is_protected (Ocmp (Ccompluimm c n))
  .

Definition is_protectedb (op : operation) : bool :=
  match op with
  | Odiv | Odivu | Omod | Omodu
  | Odivl | Odivlu | Omodl | Omodlu
  | Ointofsingle | Ointoffloat => true
  | Olongofsingle | Olongoffloat => true
  | Oshl | Oshr | Oshru | Oshll | Oshrl | Oshrlu => true
  | Osubl => Archi.ptr64
  | Osel _ _ => true
  | Ocmp (Ccompu _) | Ocmp (Ccompuimm _ _) => negb Archi.ptr64
  | Ocmp (Ccomplu _) | Ocmp (Ccompluimm _ _) => Archi.ptr64
  | _ => false
  end.


Lemma is_protectedb_spec (op : operation) :
  reflect (is_protected op) (is_protectedb op).
Proof.
  destruct op; try solve [right; intro HC; inv HC];
    try left; try constructor; auto.
  destruct cond; simpl; try solve [right; intro HC; inv HC].
  - destruct Archi.ptr64 eqn:Harchi; simpl.
    + right; intro HC; inv HC; congruence.
    + left; constructor; assumption.
  - destruct Archi.ptr64 eqn:Harchi; simpl.
    + right; intro HC; inv HC; congruence.
    + left; constructor; assumption.
  - destruct Archi.ptr64 eqn:Harchi; simpl.
    + left; constructor; assumption.
    + right; intro HC; inv HC; congruence.
  - destruct Archi.ptr64 eqn:Harchi; simpl.
    + left; constructor; assumption.
    + right; intro HC; inv HC; congruence.
Qed.

Lemma is_protected_subl_archi_ptr64_false :
  ~ is_protected Op.Osubl ->
  Archi.ptr64 = false.
Proof.
  intro H.
  destruct Archi.ptr64 eqn:Harchi; auto.
  exfalso; apply H; constructor; assumption.
Qed.



Definition platform_builtin_can_replicate (pb : platform_builtin) : bool :=
  match pb with
  | _ => false
  end.
