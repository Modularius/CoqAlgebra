From Coq.Init Require Import Notations Datatypes.
Require Import Bool.
Require Import Coq.Logic.FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq fintype.


Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool ssrnat.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Require Export Quiver.
Set Implicit Arguments.
Unset Strict Implicit.

Module QuiverEg.
  Section ADef.
    Variable n : nat.
Check vPack.
    Definition An : finQuiverType := Quiver.Build
    (Quiver.aPack (vPack
      (ordinal_finType (S n)) (@Ordinal (S n) 0 is_true_true))
      (ordinal_finType n)
      (fun a => @Ordinal (S n) a (leq_trans (ltn_ord a) (leqnSn n)))
      (fun a => @Ordinal (S n) (S a) (ltn_ord a))
    ).
  End ADef.
  Section ATildeDef.
    Variable n : nat.
    Definition ATilde_n := @Quiver.addArrows (An n) 1 (fun _ => (@Ordinal (S n) 0 (ltn0Sn n))) (fun _ => (@Ordinal (S n) n (ltnSn n))).
  End ATildeDef.

  Definition SSQ_centre := Quiver.Build (Quiver.aPack
    (vPack unit_finType tt)
    void_finType
    (fun _ => tt)
    (fun _ => tt)
  ).

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
    Variable Q : finQuiverType.
    Variable alpha : \V_Q -> nat.
    Variable matr : forall a : \A_Q, 'M[R]_(alpha \t_Q(a), alpha \h_Q(a)).
    Definition rep := @QuivRep.Pack R Q
      (fun i : \V_Q => R \lmod^ (alpha i)).

    Section One.
      Variable (n : nat) (e : 'I_n) (s : 'I_e).
      Definition indcmpAnVS := fun i : \V_(Quiver.Q_Q (QuiverEg.An n)) =>
        if s < i < e then
          (lmods.ringMod R)
        else
          (lmodZero.type R).
          (*
      Program Definition indcmpAn := rep (@QuivRep.Pack R ((QuiverEg.An n))
        (indcmpAnVS)
        (fun a : \A_(Quiver.Q_Q (QuiverEg.An n)) =>
          if s < a < e then
            linID.map (lmods.ringMod R)
          else
            linZero.map (indcmpAnVS \t_Q(a)) (indcmpAnVS \h_Q(a))
        )).
    End ADef.*)
    End One.
  End ADef.
End RepEg.