#[projections(primitive)]
Record lens {A A' B B' : Type} : Type := Lens {
  lens_view : A -> B;
  lens_over : (B -> B') -> A -> A';
}.
#[global] Arguments lens : clear implicits.
#[global] Arguments Lens {_ _ _ _} _ _ : assert.

Definition lens_compose {A A' B B' C C'}
    (l1 : lens A A' B B') (l2 : lens B B' C C') : lens A A' C C' := {|
  lens_view a := l2.(lens_view) (l1.(lens_view) a);
  lens_over f := l1.(lens_over) (l2.(lens_over) f);
|}.
Definition lens_set {A A' B B'} (l : lens A A' B B') (x : B') : A -> A' :=
  l.(lens_over) (fun _ => x).
Definition lens_const {A B B'} (b : B) : lens A A B B' := {|
  lens_view _ := b;
  lens_over _ a := a;
|}.

Notation "A -l> B" := (lens A A B B)
  (at level 99, B at level 200, right associativity) : type_scope.

Declare Scope lens_scope.
Delimit Scope lens_scope with lens.
Bind Scope lens_scope with lens.

Reserved Notation "a # b" (at level 1).
Notation "a # b" := (b a) (only parsing) : lens_scope.

Reserved Notation "a .[ b ]" (at level 2, left associativity, format "a .[ b ]").
Notation "a .[ b ]" := (lens_view b a) : lens_scope.

Reserved Notation ".[ a <$> b ]" (at level 2, left associativity, format ".[ a  <$>  b ]").
Notation ".[ a <$> b ]" := (lens_over a b) : lens_scope.

Reserved Notation ".[ a <- b ]" (at level 2, left associativity, format ".[ a  <-  b ]").
Notation ".[ a <- b ]" := (lens_set a b) : lens_scope.

Reserved Notation "a \; b" (at level 60, right associativity, format "a  \; '/'  b").
Notation "a \; b" := (lens_compose a b) : lens_scope.
