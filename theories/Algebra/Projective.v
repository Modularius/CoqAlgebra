Require Import Coq.Program.Tactics.
Require Import Coq.Logic.FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun seq bigop eqtype choice fintype.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Require Import Algebras DirectSum Basis Submodule Quotient FreeModules.
Set Implicit Arguments.
Unset Strict Implicit.

Module projLmod.
  Section Def.
    Variable (R : ringType).
    Record mixin_of (M : lmodType R)
    := Mixin { partner : lmodType R; basis : lmodFinBasisType (pair_lmodType M partner); }.
    Record type := Pack { sort : _;  class_of : mixin_of sort; }.

    Definition Build (M : lmodType R) (partner : lmodType R)
     (basis : lmodFinBasisType (pair_lmodType M partner))
      := @Pack M (@Mixin M partner basis).
  End Def.

  Section FromFree.
    Variable (R : ringType) (F : fdFreeLmodType R).
    Definition from_free : type R
    := @Build R F (null_fdFreeLmod R) (pairBasis (fdFreeLmod.basis F) (fdFreeLmod.basis (null_fdFreeLmod R))).
  End FromFree.

  Module Exports.
    Notation projLmodType := type.
    Notation proj_partner := partner.
    Notation proj_basis := basis.
    Notation proj_from_free := from_free.
    Coercion sort : type >-> lmodType.
    Coercion class_of : type >-> mixin_of.
  End Exports.
End projLmod.
Export projLmod.Exports.

Notation null_projLmod := (fun R => proj_from_free (null_fdFreeLmod R)).

Module lmodProjPair.
  Section Def.
    Variable (R : ringType) (m1 m2 : projLmodType R).

    Notation typ m1 m2 := (sum_finType (lmodFinSet.sort (proj_basis m1)) (lmodFinSet.sort (proj_basis m2))).
    Definition pairBasis_set : lmodFinSetType
    (lmodDSPairType (lmodDSPairType m1 m2)
       (lmodDSPairType (proj_partner m1) (proj_partner m2))).
    Proof. Admitted. (*
      refine (@lmodFinSet.Build _ 
        (lmodDSPairType
          (lmodDSPairType m1 m2)
          (lmodDSPairType (proj_partner m1) (proj_partner m2))
        ) _
      (fun bAB => match bAB with
      |inl bA => match bA with
        |inl A1 => ((A1,0%R),(0%R,0%R))
        |inr A2 => ((_,_),(_,_))
        end
      |inr bB => match bB with
        |inl B1 => ((_,_),(_,_))
        |inr B2 => ((_,_),(_,_))
        end
      end)
       _ _).*)

    Definition pairBasis : lmodFinBasisType
    (lmodDSPairType (lmodDSPairType m1 m2)
       (lmodDSPairType (proj_partner m1) (proj_partner m2))).

       refine (lmodFinBasis.Build _ _).
       destruct m1, m2=>/=.
       rewrite/lmodDSPairType=>/=.
    Admitted.

    Definition type : projLmodType R :=
      projLmod.Build pairBasis.
  End Def.

  Section Results.
    Variable (R : ringType) (m1 m2 : projLmodType R).
    Lemma proj_part : proj_partner (type m1 m2) = pair_lmodType (proj_partner m1) (proj_partner m2).
    Proof. by rewrite/type=>/=. Qed.
  End Results.
End lmodProjPair.

Notation pair_lmodProj := lmodProjPair.type.

Module lmodProjSeq.
  Section Def.
  Variable (R : ringType).
    Fixpoint type (L : seq (projLmodType R)) : projLmodType R :=
      match L with
      |nil => null_projLmod R
      |a::l => pair_lmodProj a (type l)
      end.
  End Def.
End lmodProjSeq.

Notation seq_lmodProj := lmodProjSeq.type.

Module lmodProjFin.
  Section Def.
    Variable (R : ringType) (F : finType) (I : F -> (projLmodType R)).
    Definition type := seq_lmodProj (map I (enum F)).

    Lemma is_direct_sum
      : projLmod.sort type = \bigoplus (fun f : F => projLmod.sort (I f)).
    Proof.
      rewrite /type/dsLmod.DS.
      rewrite /seq_lmodProj.
      by induction (enum F)=>//=; rewrite IHl.
    Qed.
  End Def.
End lmodProjFin.

Close Scope ring_scope.