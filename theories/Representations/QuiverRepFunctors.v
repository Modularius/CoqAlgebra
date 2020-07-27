Require Import Coq.Logic.FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun eqtype choice fintype seq bigop.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool.
Set Warnings "parsing".
Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Require Import Algebras QuiverRep PathAlgebra Submodule.
Require Import PathAlgebraBasis Basis FreeModules DirectSum.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope ring_scope.
Module QuivRepFunc.

  Section Def.
    Variable R : comRingType.
    Variable Q : finQuiverType.

    Section RepToMod.
      Variable V : quiverRepType R Q.

      Definition VIndex := fun i => \Vec_(V)(i).
      Definition AIndex (f : \A_Q -> \V_Q) := fun a => \Vec_(V)(f(a)).

      Definition dsum_vertices :=   \bigoplus_(i : \V_Q) fun i => \Vec_(V)(i).

      (* We want to define a path-algebra action on
      the R-module dum_vertices, turning it into a
      (path-algebra)-module
      *)
      Definition path_action_fn (v : dsum_vertices)
      (p : pathAlgBasis R Q) : dsum_vertices
      := dsLmod.inj ((QuivRep.Path V p) (dsLmod.proj (Path.tail p) v)).
      Lemma path_action_lin (v : dsum_vertices) : linear (path_action_fn v).
  (*     := [(Path.head p) --> inj](
            \PathMap_(V)(p)
              [proj --> (Path.tail p)](v)
          ).*)

      Definition newScale (r : pathAlgType R Q) (v : dsum_vertices)
      := @extendLinearlyRisky R (pathAlgType R Q) dsum_vertices
      (fun p =>
        (r p) * (freeLmodMorphism.linear_to_matrix (path_action v))
      ).

      Lemma newScale_comp (a b : pathAlgType R Q) (v : dsum_vertices) : newScale a (newScale b v) = newScale (a * b) v.
      Proof.
        rewrite /newScale=>/=.
        rewrite /infBasis.MakeExtension.
        rewrite {1 2}/path_action=>/=.
        destruct(typeIsInfSpanning (PAlgBasis.basis R Q) a) as [La Ha]eqn:A.
        destruct(typeIsInfSpanning (PAlgBasis.basis R Q) b) as [Lb Hb]eqn:B.
        destruct(typeIsInfSpanning (PAlgBasis.basis R Q) ((a : pathAlgType R Q) * b)) as [Lab Hab]eqn:AB.
        rewrite A B AB=>/=. clear A B AB.
        rewrite /PAlgBasis.pathApply.
      Admitted.

      Lemma newScale_left_id : left_id 1 newScale.
      Proof.      rewrite /newScale=>v/=.
      rewrite /infBasis.MakeExtension.
      destruct(typeIsInfSpanning (PAlgBasis.basis R Q) 1) as [L H]eqn:One.
      rewrite One.
      rewrite /path_action.
      rewrite /PAlgBasis.pathApply=>/=.
      rewrite PAlgBasis.OneIsFiniteSum.

      (* GRing.raddf_sum *)
      Admitted.


      Program Definition repToMod_lmodMixin
        := LmodMixin newScale_comp newScale_left_id _ _.
      Next Obligation.
      move=>r x y.
      rewrite /newScale.
      Admitted.
      Next Obligation.
      by move=>x y; rewrite -GRing.raddfD.
      Qed.

      (*refine (eq_bigr _
      (infGenSet.RiskyLinear_basis (PAlgBasis.basis R Q) (path_action V v))).
      rewrite /(GRing.one _)=>/=.
      rewrite /PAMul.One.
      Check (@LmodBasis.coefProj_endo_eq R (pathAlgType R Q) (PAlgBasis.basis R Q) ((path_action_func V)^~(newScale b v))).
      rewrite -GRing.scalerA.
      rewrite (LmodBasis.coefProj_eq (PAlgBasis.basis R Q)).
      rewrite (LmodBasis.basisMap_to_lmodMap_unfold
      (PAlgBasis.basis R Q)
      ((path_action_func V)^~v)
      ).
      destruct(scale_sig V v) as [g G]=>/=.
      destruct(scale_sig V v) as [g2 G2]=>/=.
      rewrite /scale_sig.
      apply eq_bigr=>i _.
      apply lmod_CountSums.sum_eq.
      apply functional_extensionality=>p.
      rewrite -lmod_CountSums.sum_bigop.
      Admitted.*)

      Definition repToMod : lmodType (PathAlg.lalg R Q)
      := LmodType (PathAlg.lalg R Q) dsum_vertices repToMod_lmodMixin.
    End RepToMod.

    Section ModToRep.
      Variable (M : lmodType (pathAlgType R Q)).

      Definition vPred (i : \V_Q) : pred M := fun m => m == \B[R](\e_i)*:m.

      Lemma vPred_subModule (i : \V_Q)
        : @submod_closed R (lmods.AtoRmod M) (subLmod.qualSubElem (vPred i)).
      Proof.
        split=>[|a x y]; rewrite qualifE unfold_in.
        by rewrite GRing.scaler0.
        rewrite !unfold_in -!(rwP eqP)=>Hx Hy.
        rewrite Hx Hy !GRing.scalerDr !GRing.scalerA PAlgBasis.idem.
      Admitted.

      Definition VSpace (i : \V_Q) := subLmodPack (vPred_subModule i).
  (*
      Program Definition VSpace_zmod_mixin (i : \V_Q)
        := (@ZmodMixin {m : M | m == \B[R](\e_i)*:m } _ _ _ _ _ _ _).
      Next Obligation.
      refine(exist _ 0%R _).
      by rewrite GRing.scaler0 eq_refl.
      Qed. Next Obligation.
      refine(exist _ (-X) _).
      apply(rwP eqP) in H.
      rewrite GRing.scalerN.
      by rewrite {1}H.
      Qed. Next Obligation.
      refine(exist _ (X + X0) _).
      apply(rwP eqP) in H.
      apply(rwP eqP) in H0.
      by rewrite {1}H {1}H0 GRing.scalerDr.
      Qed. Next Obligation.
      move=>x y z.
      Admitted. Next Obligation.
      Admitted. Next Obligation.
      Admitted. Next Obligation.
      Admitted.


      Definition VSpace_zmod (i : \V_Q)
      := ZmodType _ (VSpace_zmod_mixin i).

      Program Definition VSpace_lmod_mixin (i : \V_Q)
        := (@LmodMixin R (VSpace_zmod i) _ _ _ _ _).
      Next Obligation.
      Admitted. Next Obligation.
      Admitted. Next Obligation.
      Admitted. Next Obligation.
      Admitted. Next Obligation.
      Admitted. 

      Definition VSpace_lmod (i : \V_Q)
      := LmodType R (VSpace_zmod i) (VSpace_lmod_mixin i).
  *)
      Program Definition modToRep : quiverRepType R Q
        := QuivRep.Pack R Q
          (fun i => (VSpace i : lmodType R))
          (fun a => _).
      Next Obligation.
      Admitted.
    End ModToRep.
  End Def.

End QuivRepFunc.
Close Scope ring_scope.