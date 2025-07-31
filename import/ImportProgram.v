(*
Example: Manually written Cminor program
*)

Require Import ImportPrelude.

Module sig.
  Definition incr : signature := mksignature (Xlong :: nil) Xlong cc_default.
End sig.

Module id.
  Definition incr := intern "incr".
  Definition a := intern "a".
  Definition ret := intern "ret".
End id.

Module gd.
  Definition incr : globdef := Gfun $ Internal {|
    fn_sig := sig.incr;
    fn_params := id.a :: nil;
    fn_vars := nil;
    fn_stackspace := 0;
    fn_body := Sreturn $ Some $
      Ebinop Oaddl
        (Evar id.a)
        (Eunop Olongofint $ Econst $ Ointconst $ Int.repr 1);
  |}.
  Definition main : globdef := Gfun $ Internal {|
    fn_sig := sig.main;
    fn_params := nil;
    fn_vars := id.ret :: nil;
    fn_stackspace := 0;
    fn_body := Sseq
      (Scall (Some id.ret) sig.incr
        (Econst (Oaddrsymbol id.incr Ptrofs.zero))
        (Econst (Olongconst $ Int64.repr 41) :: nil))
      (Sreturn $ Some $ Eunop Ointoflong (Evar id.ret));
  |}.
End gd.

Definition prog : program := {|
  prog_defs := (id.incr, gd.incr) :: (id.main, gd.main) :: prelude.defs;
  prog_public := id.main :: nil;
  prog_main := id.main;
|}.
