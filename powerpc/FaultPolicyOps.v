Require Import Coqlib.
Require Import AST Builtins Op.

(** * Operation classification *)

Inductive is_protected : operation -> Prop :=
| is_protected_Odiv : is_protected Odiv
| is_protected_Odivu : is_protected Odivu
| is_protected_Odivl : is_protected Odivl
| is_protected_Odivlu : is_protected Odivlu
| is_protected_Ointoffloat : is_protected Ointoffloat
| is_protected_Olongoffloat : is_protected Olongoffloat
| is_protected_Oshl : is_protected Oshl
| is_protected_Oshr : is_protected Oshr
| is_protected_Oshru : is_protected Oshru
| is_protected_Oshll : is_protected Oshll
| is_protected_Oshrl : is_protected Oshrl
| is_protected_Oshrlu : is_protected Oshrlu
| is_protected_Osubl : Archi.ptr64 = true -> is_protected Osubl
| is_protected_Osel : forall cond ty, is_protected (Osel cond ty)
| is_protected_Ocmp_Ccompu : forall c, Archi.ptr64 = false ->
    is_protected (Ocmp (Ccompu c))
| is_protected_Ocmp_Ccompuimm : forall c n, Archi.ptr64 = false ->
    is_protected (Ocmp (Ccompuimm c n))
| is_protected_Ocmp_Ccomplu : forall c, Archi.ptr64 = true ->
    is_protected (Ocmp (Ccomplu c))
| is_protected_Ocmp_Ccompluimm : forall c n, Archi.ptr64 = true ->
    is_protected (Ocmp (Ccompluimm c n)).

Definition is_protectedb (op : operation) : bool :=
  match op with
  | Odiv | Odivu | Odivl | Odivlu
  | Ointoffloat | Olongoffloat
  | Oshl | Oshr | Oshru | Oshll | Oshrl | Oshrlu
  | Osel _ _ => true
  | Osubl => Archi.ptr64
  | Ocmp (Ccompu _) | Ocmp (Ccompuimm _ _) => negb Archi.ptr64
  | Ocmp (Ccomplu _) | Ocmp (Ccompluimm _ _) => Archi.ptr64
  | _ => false
  end.

Lemma is_protectedb_spec (op : operation) :
  reflect (is_protected op) (is_protectedb op).
Proof.
  destruct op; simpl;
    try solve [right; intro HC; inversion HC];
    try solve [left; constructor].
  - destruct Archi.ptr64 eqn:Harchi; simpl.
    + left; constructor; exact Harchi.
    + right; intro HC; inversion HC; congruence.
  - destruct cond; simpl; try solve [right; intro HC; inversion HC].
    + destruct Archi.ptr64 eqn:Harchi; simpl.
      * right; intro HC; inversion HC; congruence.
      * left; constructor; exact Harchi.
    + destruct Archi.ptr64 eqn:Harchi; simpl.
      * right; intro HC; inversion HC; congruence.
      * left; constructor; exact Harchi.
    + destruct Archi.ptr64 eqn:Harchi; simpl.
      * left; constructor; exact Harchi.
      * right; intro HC; inversion HC; congruence.
    + destruct Archi.ptr64 eqn:Harchi; simpl.
      * left; constructor; exact Harchi.
      * right; intro HC; inversion HC; congruence.
Qed.

Lemma is_protected_subl_archi_ptr64_false :
  ~ is_protected Op.Osubl ->
  Archi.ptr64 = false.
Proof.
  intro H.
  destruct Archi.ptr64 eqn:Harchi; auto.
  exfalso; apply H; constructor; assumption.
Qed.

Definition builtin_can_replicate_platform (pb : platform_builtin) : bool :=
  match pb with
  | BI_isel | BI_uisel | BI_isel64 | BI_uisel64 | BI_bsel => false
  | BI_mulhw | BI_mulhwu | BI_mulhd | BI_mulhdu => true
  end.
