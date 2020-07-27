From Coq.Init Require Import Notations Datatypes.
Require Import Coq.Logic.FunctionalExtensionality.

From mathcomp Require Import ssreflect ssrfun eqtype fintype seq.
Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
From mathcomp Require Import ssrbool.
Set Warnings "parsing".


Module Quiver.
  Section Def.
    Record finNonEmptyVectorSet := finNeVectorSetPack {
      U_0 : finType;
      getOneVertex : U_0;
    }.
    Local Notation vType := finNonEmptyVectorSet.
    Local Notation vPack := finNeVectorSetPack.

    Record aType {U : vType} := aPack {
      Q_0 := U_0 U;
      Q_1 : finType;
      h : Q_1 -> Q_0;
      t : Q_1 -> Q_0;
    }.
    Record type := Pack {
      Q_U : vType;
      Q_Q : @aType Q_U;
    }.
    Definition Build {U : vType} (Q : @aType U) := Pack U Q.
    Local Coercion Q_U : type >-> vType.
    Local Coercion Q_Q : type >-> aType.
    Local Coercion Build : aType >-> type.

    Definition head {U} {Q : @aType U} (a : Q_1 Q) := h Q a.
    Definition tail {U} {Q : @aType U} (a : Q_1 Q) := t Q a.
  

    Definition Op {U} (Q : @aType U) :=
      aPack U (Q_1 Q)
        (fun a => t Q a)
        (fun a => h Q a).

    Lemma Op_Op (Q : type) : Op (Op Q) = Q.
    Proof. unfold Op . destruct Q. by destruct Q_Q. Qed.

    Definition EdgeGraph (Q : type) : rel (Q_1 Q) :=
      fun a1 a2 : Q_1 Q => head a1 == tail a2.

    Definition Doubled (Q : type) : type
    := aPack (Q_U Q) (sum_finType (Q_1 Q) (Q_1 (Op Q)))
      (fun a => match a with
      |inl a' => h Q a' |inr a' => h (Op Q) a'
      end)
      (fun a => match a with
      |inl a' => t Q a' |inr a' => t (Op Q) a'
      end).

    Definition ReversedAt {Q : type} (i : Q_0 Q) : type
    := aPack (Q_U Q) (Q_1 Q)
      (fun a => (if (head a == i) || (tail a == i) then tail else head) a)
      (fun a => (if (head a == i) || (tail a == i) then head else tail) a).

    Definition sink {Q : type} (i : Q_0 Q) : bool
    := [forall a, tail a != i].

    Definition source {Q : type} (i : Q_0 Q) : bool
    := [forall a, head a != i].


    Set Implicit Arguments.
    Unset Strict Implicit.
    Section Union.
      Section Union2.
        Variable (Q1 Q2 : type).
        Definition unionUniv2 := vPack (sum_finType (U_0 Q1) (U_0 Q2)) (inl (getOneVertex Q1)).
        Definition unionQuiv2 := aPack unionUniv2 (sum_finType (Q_1 Q1) (Q_1 Q2))
        (fun a => match a with inl a' => inl (head a')|inr a' => inr (head a') end)
        (fun a => match a with inl a' => inl (tail a')|inr a' => inr (tail a') end).
        Definition union2 := Pack unionUniv2 unionQuiv2.
      End Union2.
      Definition union (a : type) (L : seq type) : type := foldl union2 a L.
    End Union.
    Section AddArrows.
      Variable (Q : type) (n : nat) (h t : (ordinal_finType n) -> Q_0 Q).
      Program Definition addArrows := aPack Q (sum_finType (Q_1 Q) (ordinal_finType n))
        (fun a => match a with inl a' => (head a')|inr i => h i end)
        (fun a => match a with inl a' => (tail a')|inr i => t i end).
    End AddArrows.
  End Def.

  Module Exports.
    Notation finQuiverType := @type.
    Notation vType := finNonEmptyVectorSet.
    Notation vPack := finNeVectorSetPack.
    Coercion Q_U : type >-> vType.
    Coercion Q_Q : type >-> aType.
    Coercion Build : aType >-> type.
    Notation Q_0 := Q_0.
    Notation Q_1 := Q_1.
    Notation Qtail := t.
    Notation Qhead := h.
    Notation "\V_ Q " := (Q_0 Q) (at level 0).
    Notation "\A_ Q " := (Q_1 Q) (at level 0).
    Notation "\t_Q( a )" := (tail a) (at level 0).
    Notation "\h_Q( a )" := (head a) (at level 0).
    Notation "\Op_ Q " := (Op Q) (at level 0).
    Notation "\V_ Q " := (Q_0 Q) (at level 0).
    Notation "\Dbl_ Q " := (Doubled Q) (at level 0).
    Notation "\sigma_ Q ( i )" := (@ReversedAt \V_Q Q i) (at level 0).
  End Exports.
End Quiver.
Export Quiver.Exports.