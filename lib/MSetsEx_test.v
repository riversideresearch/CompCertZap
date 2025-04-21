Require Import Coq.PArith.BinPos.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetRBT.
Require Import MSetsEx.

Module Type EXAMPLE.

  Module PositiveInhabited <: InfiniteType.INHABITED Pos.
    Definition inhabitant := xH.
  End PositiveInhabited.

  Module PositiveBitsSucc <: InfiniteType.SUCC Pos PositiveOrderedTypeBits.
    Import PositiveOrderedTypeBits.

    Definition succ : positive -> positive := xI.

    Lemma lt_succ_diag_r p : lt p (succ p).
    Proof. now induction p. Qed.
  End PositiveBitsSucc.

  Module PSet <: WSetsOn Pos := MSetRBT.Make PositiveOrderedTypeBits.

  Module PInf <: InfiniteType.S Pos PSet := InfiniteType.Make PositiveOrderedTypeBits PositiveInhabited PositiveBitsSucc PSet.

  Module Toy <: IWSetsOn Pos := FinCofinOn Pos PSet PInf.

End EXAMPLE.
