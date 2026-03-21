Require Import Coqlib.
Require Import AST Builtins Op.

(** * Operation classification *)

Inductive is_protected : operation -> Prop :=
| is_protected_Odiv : is_protected Odiv
| is_protected_Odivu : is_protected Odivu
| is_protected_Ointofsingle : is_protected Ointofsingle
| is_protected_Ointuofsingle : is_protected Ointuofsingle
| is_protected_Ointoffloat : is_protected Ointoffloat
| is_protected_Ointuoffloat : is_protected Ointuoffloat
| is_protected_Oshl : is_protected Oshl
| is_protected_Oshr : is_protected Oshr
| is_protected_Oshru : is_protected Oshru
| is_protected_Osel : forall cond ty, is_protected (Osel cond ty)
| is_protected_Ocmp_Ccompu : forall c, Archi.ptr64 = false ->
    is_protected (Ocmp (Ccompu c))
| is_protected_Ocmp_Ccompushift : forall c s, Archi.ptr64 = false ->
    is_protected (Ocmp (Ccompushift c s))
| is_protected_Ocmp_Ccompuimm : forall c n, Archi.ptr64 = false ->
    is_protected (Ocmp (Ccompuimm c n)).

Definition is_protectedb (op : operation) : bool :=
  match op with
  | Odiv | Odivu
  | Ointofsingle | Ointuofsingle | Ointoffloat | Ointuoffloat
  | Oshl | Oshr | Oshru
  | Osel _ _ => true
  | Ocmp (Ccompu _) | Ocmp (Ccompushift _ _) | Ocmp (Ccompuimm _ _) =>
      negb Archi.ptr64
  | _ => false
  end.

Lemma is_protectedb_spec (op : operation) :
  reflect (is_protected op) (is_protectedb op).
Proof.
  destruct op; simpl;
    try solve [right; intro HC; inversion HC];
    try solve [left; constructor].
  - destruct cond; simpl; try solve [right; intro HC; inversion HC].
    + destruct Archi.ptr64 eqn:Harchi; simpl.
      * right; intro HC; inversion HC; congruence.
      * left; constructor; exact Harchi.
    + destruct Archi.ptr64 eqn:Harchi; simpl.
      * right; intro HC; inversion HC; congruence.
      * left; constructor; exact Harchi.
    + destruct Archi.ptr64 eqn:Harchi; simpl.
      * right; intro HC; inversion HC; congruence.
      * left; constructor; exact Harchi.
Qed.

Definition builtin_can_replicate_platform (pb : platform_builtin) : bool :=
  match pb with end.
