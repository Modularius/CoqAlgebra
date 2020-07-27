From mathcomp Require Import ssreflect ssrfun.
From mathcomp Require Import eqtype choice fintype generic_quotient.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".


Require Import Submodule.
Set Implicit Arguments.
Unset Strict Implicit.

Open Scope ring_scope.
Open Scope quotient_scope.
Module quotLmod.

  Section Def.
    Variables (R : ringType) (M : lmodType R) (S : subLmodType M).

    Definition equiv (x y : M) := (x - y) \in (subLmod.predP S).

    Lemma equivE x y : (equiv x y) = (x - y \in (subLmod.predP S)).
    Proof. by []. Qed.

    Fact key : pred_key (subLmod.qualSubElem (subLmod.predP S)). Proof. by []. Qed.
    Canonical ST_keyed := KeyedQualifier key.

    Definition kP := @PackKeyedPred M (subLmod.predP S) key (subLmod.predP S) (fun x => erefl (x \in subLmod.predP S)).

    Canonical ST_opprPred := OpprPred (subLmod.closedP S).
    Canonical ST_addrPred := AddrPred (subLmod.closedP S).
    Canonical ST_zmodPred  := ZmodPred (subLmod.closedP S).
    Canonical ST_submodPred := SubmodPred (subLmod.closedP S).

    Lemma equiv_is_equiv : equiv_class_of equiv.
    Proof.
    split=> [x|x y|y x z]; rewrite !equivE. {
    rewrite GRing.subrr; apply (GRing.rpred0 kP). } {
    rewrite -GRing.opprB. apply (GRing.rpredN kP). } {
    move=> *; rewrite -[x](GRing.addrNK y) -GRing.addrA.
    by apply (@GRing.rpredD _ _ _ kP (x - y) (y - z)). }
    Qed.

    Canonical equiv_equiv := EquivRelPack equiv_is_equiv.
    Canonical equiv_encModRel := defaultEncModRel equiv.

    Definition qtype := {eq_quot equiv}.
    Definition qtype_of of phant R := qtype.

    (* registers type to be a quotType *)
    Canonical quot_quotType := [quotType of qtype].
    (* registers type to be a eqType, etc... *)
    Canonical quot_eqType := [eqType of qtype].
    Canonical quot_choiceType := [choiceType of qtype].
    (* registers type to be a eqQuotType *)
    Canonical quot_eqQuotType := [eqQuotType equiv of qtype].

    (* These lemmas [TODO] *)
    Lemma cosetrBE x y : (x - y) \in kP = (x == y %[mod qtype]).
    Proof. by rewrite piE equivE. Qed.

    Lemma cosetrDE x y : (x + y) \in kP = (x == - y %[mod qtype]).
    Proof. by rewrite -cosetrBE GRing.opprK. Qed.

    Lemma cosetSr r x : x \in kP -> r *: x \in kP.
    Proof. by move=>H; rewrite GRing.rpredZ. Qed.


    (* These define the group operations and constants of the quotient type,
      they must be operations on the underlying type *)
    Definition zero : qtype := lift_cst qtype 0.
    Definition add := lift_op2 qtype +%R.
    Definition opp := lift_op1 qtype -%R.

    (* This registers zero as [TODO] *)
    Canonical pi_zero_morph := PiConst zero.

    Lemma pi_opp : {morph \pi : x / - x >-> opp x}.
    Proof.
    move=> x; unlock opp; apply/eqP; rewrite piE equivE.
    by rewrite -GRing.opprD (GRing.rpredN kP) cosetrDE GRing.opprK reprK.
    Qed.

    (* This registers opp as a morphism compatible with the canonical surjection \pi *)
    Canonical pi_opp_morph := PiMorph1 pi_opp.

    Lemma pi_add : {morph \pi : x y / x + y >-> add x y}.
    Proof.
    move=> x y /=; unlock add; apply/eqP; rewrite piE equivE.
    rewrite GRing.opprD GRing.addrAC GRing.addrA -GRing.addrA GRing.addrC -GRing.addrA.
    rewrite cosetrDE pi_opp reprK -pi_opp GRing.opprD -cosetrBE
      -GRing.opprD GRing.addrA GRing.addrN GRing.add0r GRing.opprK.
    by rewrite cosetrBE reprK eq_refl.
    Qed.
    Canonical pi_add_morph := PiMorph2 pi_add.

    (* We prove the usual axioms of an abelian group *)
    Lemma addqA: associative add.
    Proof. by move=> x y z; rewrite -[x]reprK -[y]reprK -[z]reprK !piE GRing.addrA. Qed.
    Lemma addqC: commutative add.
    Proof. by move=> x y; rewrite -[x]reprK -[y]reprK !piE GRing.addrC. Qed.
    Lemma add0q: left_id zero add.
    Proof. by move=> x; rewrite -[x]reprK !piE GRing.add0r. Qed.
    Lemma addNq: left_inverse zero opp add.
    Proof. by move=> x; rewrite -[x]reprK !piE GRing.addNr. Qed.

    (* We register the type as a Zmodule *)
    Definition quot_zmodMixin := ZmodMixin addqA addqC add0q addNq.
    Canonical quot_zmodType := Eval hnf in ZmodType qtype quot_zmodMixin.



    (* This defines the scaling operation, we parameterize over the base ring
      and define "scale by r" as a univalent operation *)
    Definition scale (r : R) := lift_op1 qtype (GRing.scale r).

    Lemma pi_scale (r : R) : {morph \pi : x / r *: x >-> scale r x}.
    Proof. move=> x; unlock scale; apply/eqP; rewrite piE equivE -GRing.scalerBr.
    by apply cosetSr; rewrite cosetrBE reprK.
    Qed.
    Canonical pi_scale_morph (r : R) := PiMorph1 (pi_scale r).

    Lemma scale_axiom : forall (a b : R) (v : qtype), scale a (scale b v) = scale (a * b) v.
    Proof. move=> r s x; rewrite -[x]reprK.
    by apply/eqP; rewrite piE /= GRing.scalerA.
    Qed.

    Lemma scale_left_id : left_id 1 scale.
    Proof. move=> x; rewrite -[x]reprK.
    by apply/eqP; rewrite piE /=  GRing.scale1r.
    Qed.

    Lemma scale_right_distributive : right_distributive scale +%R.
    Proof. move=> r x y; rewrite -[x]reprK -[y]reprK.
    by apply/eqP; rewrite piE /=  GRing.scalerDr.
    Qed.
    Lemma scale_morph : forall v : quot_zmodType, {morph scale^~ v : a b / a + b >-> a + b}.
    Proof. move=> x a b; rewrite -[x]reprK.
    by apply/eqP; rewrite piE /=  GRing.scalerDl.
    Qed.

    Definition quot_lmodMixin := LmodMixin scale_axiom scale_left_id scale_right_distributive scale_morph.
    Canonical quot_lmodType := Eval hnf in LmodType R qtype quot_lmodMixin.
  End Def.

  Section ClassDef.
    Variables (R : ringType) (M : lmodType R).
    Record type := Pack {
      factorModule : subLmodType M;
    }.
    Definition Build (Q : type) : lmodType R
      := quot_lmodType (factorModule Q).
  End ClassDef.

  Module Exports.
    Coercion Build : type >-> lmodType.
    Notation quotLmodType := type.
    Notation quotLmod := Pack.
  End Exports.
End quotLmod.
Export quotLmod.Exports.

Module quotPiLmod.
  Section Def.
    Variables (R : ringType) (M : lmodType R) (S : subLmodType M) (Q : quotLmod S).

    Definition proj : M -> quotLmod.quot_lmodType S := \pi.
    Lemma proj_lin : linear proj.
    Proof. move=>r x y; by rewrite /proj quotLmod.pi_add quotLmod.pi_scale. Qed.
    Definition projLin : {linear M -> quotLmod.quot_lmodType S} := Linear proj_lin.
  End Def.

  Module Exports.
  Canonical projLin.
  Notation quotLmodProj := projLin.
  End Exports.
End quotPiLmod.
Export quotPiLmod.Exports.