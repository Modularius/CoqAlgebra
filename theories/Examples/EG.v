Require Import Coq.Init.Notations.
Require Import Coq.Init.Datatypes.
Require Import Bool.
Require Import Coq.Logic.FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Export ssrnat seq fintype.

Require Export Quiver void.
Set Implicit Arguments.
Unset Strict Implicit.

Module QuiverEg.
  Section ADef.
    Variable n : nat.

    Definition An := Quiver.Fill _ (Quiver.Pack
    (Quiver.Univ (ordinal_finType (S n)) (@Ordinal (S n) 0 is_true_true))
    (ordinal_finType n)
    (fun a => @Ordinal (S n) a (leq_trans (ltn_ord a) (leqnSn n)))
    (fun a => @Ordinal (S n) (S a) (ltn_ord a))
    ).
  End ADef.
  Section ATildeDef.
    Variable n : nat.
    Definition ATilde_n := @Quiver.addArrows (An n) 1 (fun _ => (@Ordinal (S n) 0 (ltn0Sn n))) (fun _ => (@Ordinal (S n) n (ltnSn n))).
  End ATildeDef.

  Definition SSQ_centre := Quiver.Fill _ (Quiver.Pack
  (Quiver.Univ unit_finType tt) void_finType (fun _ => tt) (fun _ => tt)).

  Definition SSQ (d : seq nat) := Quiver.union SSQ_centre (map An d).

  Section DEDef.
    Variable n : nat.

    Definition Dn (_: n > 3) := SSQ (1::1::(n - 3)::nil).
    Definition En (_: n > 4) := SSQ (1::2::(n - 3)::nil).
    Definition EnTilde (_: n > 4) := SSQ (2::2::(n - 3)::nil).
(*    Definition DnTilde (_: n > 3) := . *)
  End DEDef.

  Module Exports.
  End Exports.
End QuiverEg.
Export QuiverEg.Exports.

Require Import QuiverRep Algebras Morphism Dimension.
From mathcomp Require Export matrix.
Module RepEg.
Section ADef.
    Variable R : ringIBNType.
    Variable Q : Quiver.full_type.
    Variable alpha : \V_Q -> nat.
    Variable matr : forall a : \A_Q, 'M[R]_(alpha \t_Q(a), alpha \h_Q(a)).
    Definition rep := QuivRep.Pack R _ Q
      (fun i => (ringCartProd.ofRing R (alpha i))).

  Section One.
    Variable (n : nat) (e : 'I_n) (s : 'I_e).
    Definition indcmpAnVS := fun i : \V_(Quiver.Q_Q (QuiverEg.An n)) =>
      if s < i < e then
        (lmods.ringMod R)
      else
        (lmodZero.type R).
    Program Definition indcmpAn := rep (QuivRep.Pack R _ (Quiver.Q_Q (QuiverEg.An n))
      (indcmpAnVS)
      (fun a : \A_(Quiver.Q_Q (QuiverEg.An n)) =>
        if s < a < e then
          linID.map (lmods.ringMod R)
        else
          linZero.map (indcmpAnVS \t_Q(a)) (indcmpAnVS \h_Q(a))
      ).
  End ADef.*)
End RepEg.