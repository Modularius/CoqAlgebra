Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Init.Datatypes.
From mathcomp Require Import ssreflect ssrfun eqtype seq fintype bigop.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool ssrnat.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Set Implicit Arguments.
Unset Strict Implicit.

Require Export FreeModules DirectSum Algebras Basis Morphism Submodule Quotient.
Module ringCartProd.
  Section Def.
    Variable (R : ringType).

    Section UnitBasis.
      Definition unit_fn := fun _ : unit => (GRing.one R) : (lmods.ringMod R).
      Lemma unit_injective : injective unit_fn.
        Proof. by move=>x y; destruct x, y. Qed.
      Lemma unit_nondegen : non_degenerate unit_fn.
        Proof. rewrite /unit_fn=>x; apply GRing.oner_neq0. Qed.

      Definition unit_bset := lmodFinSet.Build unit_injective unit_nondegen.

      Lemma unit_li : li unit_bset.
      Proof. move=>/=c H b.
        rewrite -big_enum in H; simpl in H.
        rewrite big_enum_cond in H; simpl in H.
      Admitted. (*
        rewrite /unit_fn in H.
        rewrite (big_pred1 tt) in H.
        rewrite /unit_fn in H.
        case b.
        apply (@lmods.ringModEq R) in H.
        Set Printing All.
        rewrite/lmods.ringMod in H.
        rewrite -H.
        rewrite enumT in H.
        assert (J := @unit_enumP).
        rewrite /Finite.axiom in J.
        rewrite enumP in H.

        rewrite /lmodFinSet.BuildSelfSubSet in b.
      Admitted.*)

      Lemma unit_spanning : spanning unit_bset.
      Proof. move=>/=x. rewrite /lmodFinBasis.spanProj.
        refine (exist _ (fun _ => linID.map _) _).
        rewrite /lmodFinBasis.spanProp -big_enum enumT=>//=.
      Admitted.

      Definition unitBasis : lmodFinBasisType (lmods.ringMod R) := lmodFinBasis.Build unit_li unit_spanning.
      Definition freeRingMod := @fdFreeLmodPack R (lmods.ringMod R) unitBasis.
    End UnitBasis.
    Variable (n : nat).
    Definition fn := fun j : 'I_n => lmods.ringMod R : lmodType R.

    Definition type := \fbigoplus_(j : 'I_n) freeRingMod.
  End Def.

  Module Exports.
    Notation lmodRingPower := type.
    Notation "R \lmod^ n" := (type R n) (at level 30).
  End Exports.
End ringCartProd.
Export ringCartProd.Exports.

Open Scope ring_scope.
Module ringIBN.
  Section Def.
    Definition axiom (R : ringType) :=
      forall n m : nat,
        (exists b : {linear (R \lmod^ n) -> (R \lmod^ m)},
          bijective b) -> n == m.

    Record mixin (R : ringType) := Mixin { _ : axiom R; }.
    Record type := Pack { sort : _;  class_of : mixin sort; }.
    Lemma cRingIBN : forall (R : comRingType), axiom R. Proof.
    move=>R n m E.
    destruct E as [f E].
    induction n.
    unfold ringCartProd.type in f.
    Admitted.

    Definition cRingToRingIBN (R : comRingType) : type
     := Pack (Mixin (@cRingIBN R)).
  End Def.

  Module Exports.
    Notation ringIBNType := type.
    Coercion sort : type >-> ringType.
    Coercion class_of : type >-> mixin.
    Notation cRingToRingIBN := cRingToRingIBN.
    Coercion cRingToRingIBN : comRingType >-> type.
  End Exports.
End ringIBN.
Export ringIBN.Exports.

Module fdFreeLmodDimension.
  Section Def.
  Definition dim {R : ringIBNType} (M : fdFreeLmodType R) : nat
    := lmodFinBasis.basis_number (fdBasis M).
  End Def.

  Section Theory.
    Variable (R : ringIBNType).
    Open Scope nat_scope.
    Lemma steinitz_exchange {M : lmodType R}
      (B1 B2 : lmodFinBasisType M) :
      (basis_number B1 <= basis_number B2).
    Proof.
    rewrite /basis_number !cardE.
    rewrite /(enum (to_FinType (lmodFinBasis.sort B1))).
    rewrite /(enum (to_FinType (lmodFinBasis.sort B2))).
    destruct(Finite.enum (to_FinType (lmodFinBasis.sort B1))) as []eqn:E=>//=.
    destruct(Finite.enum (to_FinType (lmodFinBasis.sort B2))) as []eqn:E2=>//=.
    Admitted. (*
    assert (A := fin_span B2 (B1 s)); move: A;
    rewrite /lmodFinGenSet.spanProp
      /lmodFinSet.BuildSelfSubSet/lmodFinSubSetIncl
      -big_enum enumT E2 big_nil -(rwP eqP)=>A.
    assert (D:= @typeIsNonDegenerate _ _ B1 s);
    by move: D; rewrite A eq_refl-(rwP eqP) =>D.
    Admitted.*)
    Theorem invariant_dimension {M : lmodType R}
      (B1 B2 : lmodFinBasisType M) : basis_number B1 == basis_number B2.
    Proof.
    rewrite eqn_leq.
    by rewrite -(rwP andP);
      split; [ apply (steinitz_exchange B1 B2) | apply (steinitz_exchange B2 B1) ].
    Qed.
(*
    Axiom rank_nullity : forall {M N : fdFreeLmodType R} (f : {linear M -> N}),
      (dim (fdSubLmod \image(f))) + (dim (fdSubLmod \ker(f))) == (dim M).
*)
    Lemma dim_of_DSPair : forall (M1 M2 : fdFreeLmodType R),
      dim (pair_fdFreeLmod M1 M2) = (dim M1 + dim M2).
    Proof. move=> M1 M2.
      by rewrite /pair_fdFreeLmod/dim/basis_number card_sum.
    Qed.

    Lemma dim_of_DS : forall {F : finType} (I : F -> fdFreeLmodType R),
      dim (\fbigoplus I) = \sum_f (dim (I f)).
    Proof. move => F I.
      rewrite /finType_fdFreeLmod/fdFreeLmodFin.type -big_enum enumT =>/=;
      induction(Finite.enum F); by [
      rewrite /dim/basis_number big_nil card_void|
      rewrite dim_of_DSPair big_cons IHl].
    Qed.

(*
    Axiom dim_of_Quot : forall {M : fdFreeLmodType R} (S : subLmodType M),
      dim (fdSubLmod S) + dim (fdQuotLmod S) == dim M.
*)
    Close Scope nat_scope.
  End Theory.

  Module Exports.
    Notation "'\' 'dim' '(' M ')'" := (dim M) (at level 0, format "'\' 'dim' '(' M ')'").
  End Exports.
End fdFreeLmodDimension.
Export fdFreeLmodDimension.Exports.
Close Scope ring_scope.