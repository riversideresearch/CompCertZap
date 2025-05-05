Require Import Coqlib.
Require Import Asm.

(** TODO: Misplaced *)
Definition obind {A B} (m : option A) (f : A -> option B) : option B :=
  match m with
  | Some x => f x
  | None => None
  end.
#[global] Arguments obind _ _ !_ _ : simpl nomatch, assert.

Declare Scope option_scope.
Delimit Scope option_scope with option.
Notation "'leto' X <- A ; B" := (obind A (fun X => B))
  (at level 200, X binder, A at level 100, B at level 200) : option_scope.

Definition encode_ireg (r : ireg) : positive :=
  match r with
  | X1 => 1
  | X2 => 2
  | X3 => 3
  | X4 => 4
  | X5 => 5
  | X6 => 6
  | X7 => 7
  | X8 => 8
  | X9 => 9
  | X10 => 10
  | X11 => 11
  | X12 => 12
  | X13 => 13
  | X14 => 14
  | X15 => 15
  | X16 => 16
  | X17 => 17
  | X18 => 18
  | X19 => 19
  | X20 => 20
  | X21 => 21
  | X22 => 22
  | X23 => 23
  | X24 => 24
  | X25 => 25
  | X26 => 26
  | X27 => 27
  | X28 => 28
  | X29 => 29
  | X30 => 30
  | X31 => 31
  end.
Definition decode_ireg (p : positive) : option ireg :=
  match p with
  | 1 => Some X1
  | 2 => Some X2
  | 3 => Some X3
  | 4 => Some X4
  | 5 => Some X5
  | 6 => Some X6
  | 7 => Some X7
  | 8 => Some X8
  | 9 => Some X9
  | 10 => Some X10
  | 11 => Some X11
  | 12 => Some X12
  | 13 => Some X13
  | 14 => Some X14
  | 15 => Some X15
  | 16 => Some X16
  | 17 => Some X17
  | 18 => Some X18
  | 19 => Some X19
  | 20 => Some X20
  | 21 => Some X21
  | 22 => Some X22
  | 23 => Some X23
  | 24 => Some X24
  | 25 => Some X25
  | 26 => Some X26
  | 27 => Some X27
  | 28 => Some X28
  | 29 => Some X29
  | 30 => Some X30
  | 31 => Some X31
  | _ => None
  end%positive.

Lemma decode_encode_ireg r : decode_ireg (encode_ireg r) = Some r.
Proof. now destruct r. Qed.
Lemma encode_ireg_inj r1 r2 : encode_ireg r1 = encode_ireg r2 -> r1 = r2.
Proof. destruct r1, r2; simpl; auto; discriminate. Qed.

Definition encode_freg (r : freg) : positive :=
  match r with
  | F0 => 1
  | F1 => 2
  | F2 => 3
  | F3 => 4
  | F4 => 5
  | F5 => 6
  | F6 => 7
  | F7 => 8
  | F8 => 9
  | F9 => 10
  | F10 => 11
  | F11 => 12
  | F12 => 13
  | F13 => 14
  | F14 => 15
  | F15 => 16
  | F16 => 17
  | F17 => 18
  | F18 => 19
  | F19 => 20
  | F20 => 21
  | F21 => 22
  | F22 => 23
  | F23 => 24
  | F24 => 25
  | F25 => 26
  | F26 => 27
  | F27 => 28
  | F28 => 29
  | F29 => 30
  | F30 => 31
  | F31 => 32
  end.
Definition decode_freg (p : positive) : option freg :=
  match p with
  | 1 => Some F0
  | 2 => Some F1
  | 3 => Some F2
  | 4 => Some F3
  | 5 => Some F4
  | 6 => Some F5
  | 7 => Some F6
  | 8 => Some F7
  | 9 => Some F8
  | 10 => Some F9
  | 11 => Some F10
  | 12 => Some F11
  | 13 => Some F12
  | 14 => Some F13
  | 15 => Some F14
  | 16 => Some F15
  | 17 => Some F16
  | 18 => Some F17
  | 19 => Some F18
  | 20 => Some F19
  | 21 => Some F20
  | 22 => Some F21
  | 23 => Some F22
  | 24 => Some F23
  | 25 => Some F24
  | 26 => Some F25
  | 27 => Some F26
  | 28 => Some F27
  | 29 => Some F28
  | 30 => Some F29
  | 31 => Some F30
  | 32 => Some F31
  | _ => None
  end%positive.

Lemma decode_encode_freg r : decode_freg (encode_freg r) = Some r.
Proof. now destruct r. Qed.
Lemma encode_freg_inj r1 r2 : encode_freg r1 = encode_freg r2 -> r1 = r2.
Proof. destruct r1, r2; simpl; auto; discriminate. Qed.

Definition encode_preg (r : preg) : positive :=
  match r with
  | IR r => xI (encode_ireg r)
  | FR r => xO (encode_freg r)
  | PC => xH
  end.
Definition decode_preg (p : positive) : option preg :=
  match p with
  | xI p => leto r <- decode_ireg p; Some (IR r)
  | xO p => leto r <- decode_freg p; Some (FR r)
  | xH => Some PC
  end%option.

Lemma decode_encode_preg r : decode_preg (encode_preg r) = Some r.
Proof.
  destruct r; simpl; auto.
  - now rewrite decode_encode_ireg.
  - now rewrite decode_encode_freg.
Qed.

Lemma encode_preg_inj r1 r2 : encode_preg r1 = encode_preg r2 -> r1 = r2.
Proof.
  intros Hr.
  destruct r1, r2; simpl in *; inversion Hr as [Hr']; auto; clear Hr.
  - apply encode_ireg_inj in Hr'. now rewrite Hr'.
  - apply encode_freg_inj in Hr'. now rewrite Hr'.
Qed.
