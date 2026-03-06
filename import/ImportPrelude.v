Require Export Coqlib.
Require Export AST.
Require Export Integers.
Require Export Floats.
Require Export Cminor.

(**
Add an identifier to CompCert's state (a partial bijection between
strings and positives).
*)
Parameter intern: string -> ident.

Notation "f $ x" := (f x) (at level 65, right associativity, only parsing).
#[global] Arguments Gfun {_ _} _ : assert.
#[global] Arguments External {_} _ : assert.
Definition globdef : Type := AST.globdef fundef unit.

(**
Separately compiled "programs" need not define identifier <<main>> but
they should mention it in <<prog_main>>.
*)
Module sig.
  Notation main := signature_main (only parsing).
End sig.
Module id.
  Definition main := intern "main".
End id.

(**
SplitLong helpers.

Compare ../cfrontend/C2C.ml:/helper_functions
and ../backend/SplitLongproof.v
*)
Module prelude.
  Definition sig_l_f := [Xlong ---> Xfloat]%asttyp.
  Definition sig_l_s := [Xlong ---> Xsingle]%asttyp.
  Definition sig_f_l := [Xfloat ---> Xlong]%asttyp.
  Definition sig_ll_l := [Xlong; Xlong ---> Xlong]%asttyp.
  Definition sig_li_l := [Xlong; Xint ---> Xlong]%asttyp.
  Definition sig_i_v := [Xint ---> Xvoid]%asttyp.

  Definition external_function (p : string * signature) : ident * globdef :=
    let '(name, sg) := p in
    (intern name, Gfun (External (EF_external name sg))).

  Definition runtime_function (p : string * signature) : ident * globdef :=
    let '(name, sg) := p in
    (intern name, Gfun (External (EF_runtime name sg))).

  Local Open Scope string_scope.
  Definition defs : list (ident * globdef) :=
    app 
    (map external_function $
      ("exit", sig_i_v) ::
      nil
    )
    (map runtime_function $
      ("__compcert_i64_dtos", sig_f_l) ::
      ("__compcert_i64_dtou", sig_f_l) ::
      ("__compcert_i64_stod", sig_l_f) ::
      ("__compcert_i64_utod", sig_l_f) ::
      ("__compcert_i64_stof", sig_l_s) ::
      ("__compcert_i64_utof", sig_l_s) ::
      ("__compcert_i64_sdiv", sig_ll_l) ::
      ("__compcert_i64_udiv", sig_ll_l) ::
      ("__compcert_i64_smod", sig_ll_l) ::
      ("__compcert_i64_umod", sig_ll_l) ::
      ("__compcert_i64_shl", sig_li_l) ::
      ("__compcert_i64_shr", sig_li_l) ::
      ("__compcert_i64_sar", sig_li_l) ::
      ("__compcert_i64_umulh", sig_ll_l) ::
      ("__compcert_i64_smulh", sig_ll_l) ::
      nil).
End prelude.
