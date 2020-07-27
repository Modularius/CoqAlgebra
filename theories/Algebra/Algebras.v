Require Import Coq.Program.Tactics.
From mathcomp Require Import ssreflect ssrfun eqtype choice.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope ring_scope.

Require Import Submodule.

Module lmodZero.
  Section Def.
  Definition zeroAdd := fun _ _ : unit => tt.
  Definition zeroNeg := fun _ : unit => tt.
  Definition zeroAbGroupA : associative zeroAdd. Proof. by []. Qed.
  Definition zeroAbGroupC : commutative zeroAdd. Proof. by []. Qed.
  Definition zeroAbGroup0z : left_id tt zeroAdd. Proof. by case. Qed.
  Definition zeroAbGroupIz : left_inverse tt zeroNeg zeroAdd. Proof. by case. Qed.

  Definition zeroAbGroup : zmodType :=
    ZmodType unit (GRing.Zmodule.Mixin zeroAbGroupA zeroAbGroupC zeroAbGroup0z zeroAbGroupIz).
  Canonical zeroAbGroup.

  Variable R : ringType.

  Definition zeroScale := (fun (_ : R) (_ : unit) => tt).
  Lemma zeroScale_id : left_id 1%R zeroScale. Proof. by case. Qed.
  Lemma zeroScale_rD : right_distributive zeroScale +%R. Proof. by rewrite /(GRing.add)=>/=. Qed.

  Program Definition type : lmodType R :=
    LmodType R unit (LmodMixin _ zeroScale_id zeroScale_rD _).
  Next Obligation. by rewrite /(GRing.add)=>/=. Qed.
  End Def.
End lmodZero.

Notation lmodZeroType := lmodZero.type.

Module lmods.
  Section Def.
    Variable (R : ringType).
    Program Definition ringMod : lmodType R
     := LmodType R R (LmodMixin (@GRing.mulrA R) (@GRing.mul1r R) (@GRing.mulrDr R) _).
    Next Obligation. by move=>x y; rewrite GRing.mulrDl. Qed.

    Variable (A : lalgType R) (V : lmodType A).
    Definition AtoRscale := fun (r : R) (v : V) => (r *: (GRing.one A)) *: v.
    Lemma AtoRscale_id : left_id 1 AtoRscale.
    Proof. by rewrite/AtoRscale=>x; rewrite !GRing.scale1r. Qed.
    Lemma AtoRscale_rD : right_distributive AtoRscale +%R.
    Proof. by rewrite/AtoRscale=> x y z; rewrite GRing.scalerDr. Qed.

    Program Definition AtoRmod : lmodType R
    := LmodType R V (LmodMixin _ AtoRscale_id AtoRscale_rD _).
    Next Obligation.
    by rewrite/AtoRscale GRing.scalerA -GRing.scalerAl GRing.mul1r GRing.scalerA.
    Qed. Next Obligation.
    by rewrite/AtoRscale=>r s; rewrite !GRing.scalerDl.
    Qed.
  End Def.
End lmods.
Close Scope ring_scope.
