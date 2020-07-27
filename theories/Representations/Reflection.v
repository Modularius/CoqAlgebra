Require Import Coq.Init.Notations.
Require Import Coq.Logic.FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype choice ssralg bigop.
Require Import Coq.Program.Tactics.

Require Export Algebras DirectSum QuiverRep Morphism.
Require Export PathAlgebra PathAlgebraBasis.
Require Export FiniteBasis InfiniteBasis Quiver Submodule.
Set Implicit Arguments.
Unset Strict Implicit.

Open Scope ring_scope.
Module QuivRepRefl.

Section Def.
  Variable R : comRingType.
  Variable U : Quiver.nonEmptyUniverse.
  Variable Q : quiverType U.
  Variable i : \V_Q.
  Variable V : quiverRepType R Q.

  Definition newQ := Quiver.ReversedAt i.
  Section DefSink.
    Variable sinkP : Quiver.sink i.

    Definition predInArrow : pred \A_Q := fun a => \h_Q(a) == i.
    Definition qualInArrow := [qualify x | x \in predInArrow].

    Record inA := inArrowPack {
      inarr :> \A_Q;
      inarrP : inarr \in qualInArrow;
    }.
    Hint Resolve inarrP.
    Canonical inarr_subType := [subType for inarr].

    Definition inarr_eqMixin := [eqMixin of inA by <:].
    Canonical inarr_eqType := EqType inA inarr_eqMixin.
    Definition inarr_choiceMixin := [choiceMixin of inA by <:].
    Canonical inarr_choiceType := ChoiceType inA inarr_choiceMixin.
    Definition inarr_countMixin := [countMixin of inA by <:].
    Canonical inarr_countType := CountType inA inarr_countMixin.
    Canonical inarr_subCountType := [subCountType of inA].
    Definition inarr_finMixin := [finMixin of inA by <:].
    Canonical inarr_finType := FinType inA inarr_finMixin.

    Definition alterCoDomain {a : inarr_finType}
      (f : {linear \Vec_(V)(\t_Q(a)) -> \Vec_(V)(\h_Q(a))})
     : {linear \Vec_(V)(\t_Q(a)) -> \Vec_(V)(i)}.
    Proof.
    assert (A:= (inarrP a)).
    rewrite qualifE unfold_in in A.
    by apply (rwP eqP) in A; rewrite -A. Qed.

    Definition inFunc : forall a : inarr_finType,
      {linear \Vec_(V)(\t_Q(a)) -> \Vec_(V)(i)}
      := fun a : inA
       => alterCoDomain \Map_(V)(a).

    Definition VPlusSinkFunc := fun a : inarr_finType => \Vec_(V)(\t_Q(a)).

    Definition VPlusSink
     := lmodDS.idx.DS VPlusSinkFunc.

    Definition Pi := lmodDS.linExt.ExtendLinearlyFromLin inFunc.
    Definition kerPi := \ker(Pi).

    Definition newMap (a : inarr_finType)
      : {linear kerPi -> \Vec_(V)(\t_Q(a))} := linConcat.map
      (subLmodIncl kerPi)
      (lmodDS.idx.projLin VPlusSinkFunc a).

    Program Definition ReflectAtSink : quiverRepType R (newQ)
     := QuivRep.Pack R U newQ
      (fun i' : \V_(newQ) => if i' == i
        then kerPi : lmodType R
        else \Vec_(V)(i') : lmodType R
      )
      (fun a : \A_Q => _).
    Next Obligation.
    case((\h_Q(a) == i) || (\t_Q(a) == i)) as []eqn:E. {
    case(\t_Q(a) == i) as []eqn:Et; rewrite Et. {
    by assert (K := negP (forallP sinkP a)). }
    case(\h_Q(a) == i) as []eqn:Eh; rewrite Eh. {
    assert(a \is qualInArrow).
    by rewrite unfold_in (qualifE 0) Eh.
    apply (newMap (inArrowPack H)). }
    by simpl in E. }
    apply negbT in E.
    apply (rwP norP) in E.
    destruct E as [E1 E2].
    rewrite (negbTE E1) (negbTE E2).
    apply (\Map_(V)(a)).
    Qed.
  End DefSink.
(*
  Section DefSource.
    Variable srcP : Quiver.source i.

    Definition predOutArrow : pred \A_Q := fun a => \t_Q(a) == i.
    Definition qualOutArrow := [qualify x | x \in predOutArrow].

    Record outA := outArrowPack {
      outarr :> \A_Q;
      outarrP : outarr \in qualOutArrow;
    }.
    Hint Resolve outarrP.
    Canonical outarr_subType := [subType for outarr].

    Definition outarr_eqMixin := [eqMixin of outA by <:].
    Canonical outarr_eqType := EqType outA outarr_eqMixin.
    Definition outarr_choiceMixin := [choiceMixin of outA by <:].
    Canonical outarr_choiceType := ChoiceType outA outarr_choiceMixin.
    Definition outarr_countMixin := [countMixin of outA by <:].
    Canonical outarr_countType := CountType outA outarr_countMixin.
    Canonical outarr_subCountType := [subCountType of outA].
    Definition outarr_finMixin := [finMixin of outA by <:].
    Canonical outarr_finType := FinType outA outarr_finMixin.

    Definition alterDomain {a : outarr_finType}
      (f : {linear \Vec_(V)(\t_Q(a)) -> \Vec_(V)(\h_Q(a))})
     : {linear \Vec_(V)(i) -> \Vec_(V)(\h_Q(a))}.
    Proof.
    assert (A:= (outarrP a)).
    rewrite qualifE unfold_in in A.
    by apply (rwP eqP) in A; rewrite -A. Qed.

    Definition outFunc : forall a : outarr_finType,
      {linear \Vec_(V)(i) -> \Vec_(V)(\h_Q(a))}
      := fun a : outA
       => alterDomain \Map_(V)(a).

    Definition VPlusSrcFunc := fun a : outarr_finType => \Vec_(V)(\h_Q(a)).

    Definition VPlusSrc
     := lmod_DS.idx.DS VPlusSrcFunc.

    Definition Pi_src := ExtendLinearlyToLin outFunc.
    Definition kerPi_src := lmods.kernel R \Vec_(V)(i) VPlusSrc Pi_src.

    Definition newMap_src (a : outarr_finType)
      : {linear \Vec_(V)(\h_Q(a)) -> kerPi_src} := lmod_Maps.cat
      (subLmodInclType kerPi_src)
      (lmod_DS.idx.projLin VPlusSrcFunc a).

    Program Definition ReflectAtSink : quiverRepType R (newQ)
     := QuivRep.Pack R U newQ
      (fun i' : \V_(newQ) => if i' == i
        then kerPi : lmodType R
        else \Vec_(V)(i') : lmodType R
      )
      (fun a : \A_Q => _).
    Next Obligation.
    case((\h_Q(a) == i) || (\t_Q(a) == i)) as []eqn:E. {
    case(\t_Q(a) == i) as []eqn:Et; rewrite Et. {
    by assert (K := negP (forallP sinkP a)). }
    case(\h_Q(a) == i) as []eqn:Eh; rewrite Eh. {
    assert(a \is qualInArrow).
    by rewrite unfold_in (qualifE 0) Eh.
    apply (newMap (inArrowPack H)). }
    by simpl in E. }
    apply negbT in E.
    apply (rwP norP) in E.
    destruct E as [E1 E2].
    rewrite (negbTE E1).
    rewrite (negbTE E2).
    apply (\Map_(V)(a)).
    Qed.
  End DefSource. *)
End Def.


End QuivRepRefl.
Close Scope ring_scope. 