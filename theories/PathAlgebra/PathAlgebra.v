Require Import Coq.Logic.FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun eqtype bigop choice path seq.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
    From mathcomp Require Import ssrbool.
Set Warnings "parsing".
Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Require Import Path ntPathPairs PathAlgebraMul FormalLC Quiver.
Set Implicit Arguments.
Unset Strict Implicit.

Open Scope ring_scope.
Module PathAlg.

  Section Def.
  Variables (R : ringType) (Q : finQuiverType).
  Local Notation lmod := (PAMul.lmod R Q).
  Local Notation Add := (@GRing.add lmod).
  Local Notation Neg := (@GRing.opp lmod).
  Local Notation Zero := (@GRing.zero lmod).
  Local Notation Scale := (@GRing.scale lmod).
  Local Notation Mul := (PAMul.Mul R Q).
  Local Notation One := (PAMul.One R Q).
  Local Notation addXr := (PAMul.addXr).
  Local Notation addrX := (PAMul.addrX).

  Section Ring.
    Lemma left_d : left_distributive Mul Add.
    Proof. move=>x y z.
      rewrite /Mul/Add/Neg/Zero; apply functional_extensionality=>p/=.
      rewrite /formalLC.Add.
      induction p; by rewrite  (eq_bigr _ (fun _ _ => (GRing.mulrDl _ _ _))) big_split=>/=.
    Qed.


    Lemma right_d : right_distributive Mul Add.
    Proof. move=>x y z.
      rewrite /Mul/Add/Neg/Zero; apply functional_extensionality=>p/=.
      rewrite /formalLC.Add.
      induction p; by rewrite  (eq_bigr _ (fun _ _ => (GRing.mulrDr _ _ _))) big_split=>/=.
    Qed.

    Lemma one_neq_zero : One != Zero.
    Proof. rewrite /One/Zero.
      apply (rwP negP).
      rewrite /not=>H.
      apply (rwP eqP) in H.
      assert (A:=equal_f H (\e_(Quiver.getOneVertex Q))); clear H.
      simpl in A.
      assert(B := GRing.oner_neq0 R).
      rewrite /negb in B.
      rewrite A in B.
      case ((GRing.zero R) == (GRing.zero R)) as []eqn:E.
      rewrite E in B=>//=.
      rewrite eq_refl in E=>//=.
    Qed.
    Definition PathAlg_ringMixin
      := RingMixin
        (PAMul.MulA R Q) (PAMul.left_id1 R Q) (PAMul.right_id1 R Q)
        left_d right_d one_neq_zero.

    Definition ring
      := RingType lmod PathAlg_ringMixin.
  End Ring.

  Section Lalg.
    Lemma lalgAxiom
     : @GRing.Lalgebra.axiom R lmod Mul.
    Proof. move=> a u1 u2.
      rewrite /(GRing.scale _)=>/=; rewrite /PAMul.Mul/formalLC.Scale.
      apply functional_extensionality=>p.
      case p=>[s|t];
      by rewrite big_distrr (eq_bigr _ (fun _ _ => (GRing.mulrA _ _ _))).
    Qed.
    Definition lalg := LalgType R ring lalgAxiom.
  End Lalg.

  Section Alg.
    Axiom algAxiom : @GRing.Algebra.axiom R lalg.

    Definition alg := AlgType R lalg algAxiom.
  End Alg.
  End Def.

  Close Scope ring_scope.

  Module Exports.
    Canonical lalg.
    Canonical alg.

    Notation pathAlgType := alg.
  End Exports.

End PathAlg.
Export PathAlg.Exports.