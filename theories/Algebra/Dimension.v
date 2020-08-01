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
      Proof. apply fin_li; move=>/=c H b.
        rewrite -big_enum in H; simpl in H.
        rewrite enumT in H.
      Admitted.

      Lemma unit_spanning : spanning (lmodBasisSet.Build (fun _ : unit_bset => linID.map (lmods.ringMod R))).
      Proof. move=>/=x.
        refine (exist _ (lmodFinSet.BuildSelfSubSet unit_bset) _).
        rewrite -big_enum enumT=>//=.
      Admitted.

      Definition unitBasis : lmodFinBasisType (lmods.ringMod R) := lmodFinBasis.Build unit_li unit_spanning.
      Definition freeRingMod := @fdFreeLmodPack R (lmods.ringMod R) unitBasis.
    End UnitBasis.
    Variable (n : nat).
    Definition fn := fun j : 'I_n => lmods.ringMod R : lmodType R.

    Definition type := \fbigoplus_(j : 'I_n) freeRingMod.

(*
    Definition basis_fn := fun i => lmodDS.idx.injLin fn i (GRing.one R).

    Lemma basis_inj : injective basis_fn. Proof.
    rewrite /basis_fn=>x y H.
    destruct x as [x Hx], y as [y Hy].
    case(x == y) as []eqn:E.
    apply (rwP eqP) in E. destruct E.
    by rewrite (proof_irrelevance _ Hx Hy).
    by apply (lmodDS.idx.inj_index_injective) in H.
    Qed.

    Lemma basis_nondeg : non_degenerate basis_fn. Proof.
    move=>x.
    assert(A := GRing.linear0 (@lmodDS.idx.injLin R (ordinal_finType n) fn x)).
    rewrite -A.
    apply (rwP negP); rewrite /not=>H.
    apply (rwP eqP) in H.
    apply (@lmodDS.idx.inj_injective R _ fn x) in H.
    apply (rwP eqP) in H.
    by rewrite (GRing.oner_eq0) in H.
    Qed.

    Lemma basis_li : li (lmodFinSet.Build basis_inj basis_nondeg).
    Proof. move=>/= c H b.
    case(c b == 0) as []eqn:E=>//.
    destruct b.
    Admitted.

    Lemma basis_spanning : spanning (lmodFinSet.Build basis_inj basis_nondeg).
    Proof. move=>m. Admitted.


    Program Definition basis : finBasisType type
     := lmodFinBasis.Build basis_li basis_spanning.

    Program Definition ofRing := fdFreeLmod.Pack (fdFreeLmod.Mixin basis). *)
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

    Axiom cRingToRingIBNMixin : forall (R : comRingType), mixin R.
    Definition cRingToRingIBN (R : comRingType) : type
     := Pack (cRingToRingIBNMixin R).
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
    := lmodFinBasis.basis_number (basis M).
  End Def.

  Section Theory.
    Variable (R : ringIBNType).
    Open Scope nat_scope.
    Axiom steinitz_exchange : forall {M : lmodType R}
      (B1 B2 : lmodFinBasisType M),
      (basis_number B1 <= basis_number B2).
    (*Proof. move=> H1 H2.
    rewrite !cardE.
    rewrite /(enum B1).
    rewrite /(enum B2).
    destruct(Finite.enum B1) as []eqn:E=>//.
    destruct(Finite.enum B2) as []eqn:E2=>//.
    destruct H1 as [H1 H1'].
    rewrite /fin_spanning in H2.
    Search "enum".
    Set Printing All.
    *)
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