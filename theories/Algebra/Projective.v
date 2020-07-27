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
      := Pack (Mixin basis).
  End Def.

  Module Exports.
    Notation projLmodType := type.
    Notation proj_partner := partner.
    Notation proj_basis := basis.
    Coercion sort : type >-> lmodType.
    Coercion class_of : type >-> mixin_of.
  End Exports.
End projLmod.
Export projLmod.Exports.


Module lmodProjDS.
  Section Def.
    Variable (R : ringType).

    Section FromFree.
      Variable (F : fdFreeLmodType R).
      Definition from_free : projLmodType R
       := projLmod.Build (fdDSBasis_lmod.pairBasis (basis F) (basis (fdDSBasis_lmod.null_fdFreeLmod R))).
    End FromFree.
    Section Pair.
      Variable (m1 m2 : projLmodType R).
      Definition lmodProjPair : projLmodType R :=
        projLmod.Build (fdDSBasis_lmod.pairBasis (proj_basis m1) (proj_basis m2)).
    End Pair.
    Section List.
      Fixpoint seq_lmodProj (L : seq (projLmodType R)) : projLmodType R :=
        match L with
        |nil => from_free (fdDSBasis_lmod.null_fdFreeLmod R)
        |a::l => lmodProjPair a (seq_lmodProj l)
        end.
    End List.

    Section TypeIndex.
      Definition finType_lmodProj (F : finType) (I : F -> (projLmodType R)) :=
        seq_lmodProj (map I (enum F)).
      Lemma is_direct_sum (F : finType) (I : F -> (projLmodType R)) :
        projLmod.sort (finType_lmodProj I) = \bigoplus (fun f : F => projLmod.sort (I f)).
      Proof.
        rewrite /finType_lmodProj/dsLmod.DS.
        induction (enum F)=>//=. rewrite -IHl.
      Admitted.
    End TypeIndex.
  End Def.
End lmodProjDS.

Close Scope ring_scope.