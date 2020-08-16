From Coq.Logic Require Import FunctionalExtensionality ProofIrrelevance.
From mathcomp Require Import ssreflect ssrfun eqtype bigop choice path seq fintype.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
    From mathcomp Require Import ssrbool.
Set Warnings "parsing".
Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Require Export Path ntPathPairs PathAlgebraMul PathAlgebra.
Require Export Algebras Basis Submodule FreeModules Quiver FormalLC.
Open Scope ring_scope.
Set Implicit Arguments.
Unset Strict Implicit.

Module PAlgBasis.
Include ntPath.NTPath.Exports.

  Section Def.
    Variable (R : comRingType) (Q : finQuiverType).
    (*Lemma elem_li : lmodLISet.axiom (formalLC.genSet R (Path.Path_eqType Q)).
    Proof. rewrite /elem => f coef =>H finb; move:H.
      rewrite -(rwP eqP)=>H.
      apply (f_equal (formalLC.pathApplyLin R (f finb))) in H; move:H.
      rewrite (GRing.raddf_sum (formalLC.pathApplyLin _ (f finb))) /formalLC.Zero=>/=.
      rewrite /formalLC.pathApply=>H.
      assert(forall i, true->
        (coef i * (if f finb == f i then 1 else 0)) =
        ((if f finb == f i then coef i else 0))
      ).
      move=>i _.
      by case(f finb == f i);[rewrite GRing.mulr1|rewrite GRing.mulr0].
      rewrite (eq_bigr _ H0) in H; clear H0.
      rewrite -big_mkcond in H; simpl in H.
      destruct f as [F f I].
      rewrite (eq_bigl _ _ (inj_eq I finb)) (eq_bigl _ _ (eq_sym _)) big_pred1_eq in H.
      by rewrite H eq_refl.
    Qed.*)

    Definition pathAlgBasis := formalLC.basis R (Path.eqType Q).

    Section Element.
      Definition elem : pathType Q -> pathAlgType R Q
      := pathAlgBasis.

  Lemma idemR : forall (p : pathType Q),
    (elem p) * (elem \e_(Path.tail p)) = (elem p).
  Proof. move=>p; rewrite /(GRing.mul _)=>/=.
  rewrite /PAMul.Mul/elem=>/=.
  rewrite /formalLC.elem=>/=.
  apply functional_extensionality=>p'.
  case (p' == p) as []eqn:E.
    apply (rwP eqP) in E; rewrite E.
    case p as [i|r]eqn:P.
    by rewrite /Path.BuildPairs big_cons big_nil eq_refl GRing.mul1r GRing.addr0=>/=.

    destruct r as [[a r] H].
    clear P E.
  Admitted.
    destruct H.
    induction r as []=>/=.
    rewrite /ntPath.NTPath.type2tail/ntPath.NTPath.type2deTail=>/=.
      rewrite !big_cons big_nil GRing.mul0r GRing.addr0 GRing.add0r=>/=.
      by rewrite !eq_refl GRing.mul1r.

      rewrite big_cat=>/=.

      rewrite /Path.BuildPairs=>/=.
      rewrite /ntPath.NTPath.type2tail=>/=.
      rewrite /ntPath.NTPath.type2tail in IHr; simpl in IHr.
      rewrite /ntPath.NTPath.type2tail/ntPath.NTPath.type2deTail in IHr; simpl in IHr.
      rewrite !big_cons GRing.mul0r GRing.add0r=>/=.
      rewrite IHr.
      rewrite eq_refl in E2.
      rewrite E2 GRing.mul0r.
  case p'=>s. {
  case (\e_ (s) == p) as []eqn:E. {
  Admitted.
  (*apply (rwP eqP) in E.  rewrite E eq_refl -E. GRing.mulr1=>/=.
  by rewrite E GRing.mul0r. } {
  rewrite /PAMul.MulEndPairs.
  Admitted.*)

  Lemma idemL : forall (p : pathType Q),
    (elem \e_(Path.head p)) * (elem p) = (elem p).
  Proof. move=> p. Admitted.

  Lemma idem : forall (i : \V_Q),
    (elem \e_i) * (elem \e_i) = (elem \e_i).
  Proof. move=>i; apply(idemR \e_i). Qed.*)
End Element.

(*    Definition pathAlgBasisSet := formalLC.genSet R (Path.Path_eqType Q).
    Definition pathAlgBasis := lmodBasisSet.Pack (lmodBasisSet.Class
      (lmodBasisSet.Mixin
        (fun p : pathAlgBasisSet => @formalLC.pathApplyLin R (Path.Path_eqType Q) p)
      )).*)
    Definition freePathAlgType := freeLmod.Build pathAlgBasis.
  End Def.


  Lemma OneIsFiniteSum (R : comRingType) {Q : finQuiverType} :
    1%R = \big[+%R/0%R]_(i : \V_Q)(elem R \e_i).
  Proof.
    rewrite/(GRing.one _)=>/=.
    apply functional_extensionality=>p.
    assert(formalLC.pathApplyLin p (PAMul.One R Q) = formalLC.pathApplyLin p(\big[+%R/0]_i elem R \e_ (i))). {
    rewrite GRing.raddf_sum=>/=.
    rewrite /formalLC.pathApply/PAMul.One/elem.
    case p as [a|a]. {
    rewrite -big_mkcond=>/=.
    rewrite (eq_bigl _ _ (inj_eq _ a)).
    by rewrite (eq_bigl _ _ (eq_sym _)) big_pred1_eq.
    by move=>x y H; inversion H. } {
    rewrite big_mkcond=>/=.
    by rewrite big1_eq. } }
    by rewrite /formalLC.pathApply in H.
  Qed.

  Module Exports.
  Notation "\B[ R ]( p )" := (elem R p) (at level 0).
  Notation pathAlgBasis := pathAlgBasis.
  Notation freePathAlgType := freePathAlgType.
  End Exports.
End PAlgBasis.
Export PAlgBasis.Exports.

Module PAlgSub.
  Module Rmul.
    Section Def.
      Variable (R : comRingType) (Q : finQuiverType) (i : \V_Q).
      Definition inSet
       := fun x : (lmods.ringMod (pathAlgType R Q)) => x == (x*\B[R](\e_i)).

      Lemma subModule
       : GRing.submod_closed (subLmod.qualSubElem inSet).
      Proof. split=>[|a x y];rewrite qualifE !unfold_in.
      by rewrite GRing.mul0r eq_refl.
      rewrite -!(rwP eqP)=>Hx Hy;
      by rewrite Hx Hy GRing.mulrDl -!GRing.mulrA !PAlgBasis.idem.
      Qed.
      Canonical lmodType := subLmod.Pack subModule.
    End Def.
    Section Basis.
      Variable (R : comRingType) (Q : finQuiverType) (i : \V_Q).
      Definition elem (p : {p : pathType Q | (Path.tail p == i)}) : pathAlgType R Q
       := fun p' => if p' == (sval p) then 1 else 0.

      Lemma elem_inj : injective elem. Proof.
        move=> x y. destruct x as [x Hx], y as [y Hy]=>H.
        refine (eq_sig_hprop _ _ _ _).
        move=> x' p' q'; apply proof_irrelevance=>/=.
        rewrite /elem in H. simpl in H.
        assert (A := equal_f H x); rewrite eq_refl in A.
        case(x == y) as []eqn:E; [by apply (rwP eqP) in E|apply (rwP eqP) in A].
        assert (P := GRing.oner_eq0 R).
        by rewrite A in P.
      Qed.

      Lemma elem_nondeg : non_degenerate elem. Proof.
        rewrite /elem=> x.
        apply (rwP negP); rewrite /not -(rwP eqP)=>H.
        destruct x as [x Hx].
        assert (A := equal_f H x); rewrite eq_refl in A.
        rewrite /(GRing.zero _) in A; simpl in A.
        rewrite /formalLC.Zero in A.
        apply (rwP eqP) in A.
        by rewrite (GRing.oner_eq0 R) in A. Qed.
(*
      Lemma elem_li : lmodBasis.LISet.axiom (lmodSet.Build elem_inj elem_nondeg).
      Proof. rewrite /elem=> f coef =>H finb; move:H.
        rewrite -(rwP eqP)=>H. Admitted.

    Lemma span : @inf_spanning _ _ (lmodSet.Build elem_inj elem_nondeg) (fun x => (@PAlgBasis.pathApplyLin R Q (sval x))).
    Proof. move=>el. Admitted.
*)
(*
    Lemma coef_one : lmodBasis.axiom_coef_one (infGenSet.Mixin span).
    Proof. move=>b; rewrite/infGenCoef=>/=; by rewrite/PAlgBasis.pathApply/elem !eq_refl. Qed.

    Lemma coef_zero : infBasis.axiom_coef_zero (infGenSet.Mixin span).
    Proof. move=>b1 b2; rewrite/infGenCoef=>/=; rewrite/PAlgBasis.pathApply/elem/not=>H.
      case (sval b1 == sval b2) as []eqn:E; [apply (rwP eqP) in E | rewrite eq_refl].
Admitted.
*)
(*      by contradict(H (@eq_sig_hprop _ _ 5 b1 b2 E)).
    Qed.

    Lemma pathApplyLin_one : forall b, PAlgBasis.pathApplyLin R (sval b) (elem b) == 1.
      Proof. simpl; rewrite /PAlgBasis.pathApply/elem=>b/=; by rewrite !eq_refl. Qed.
    Lemma pathApplyLin_zero : forall b1 b2, b1 <> b2 -> PAlgBasis.pathApplyLin R (sval b1) (elem b2) == 0.
    Proof. rewrite /PAlgBasis.pathApply/elem=>b1 b2/=; rewrite /not=> H.
      case(b1 == b2) as []eqn:E=>//.
      by apply (rwP eqP) in E.
       rewrite /PAlgBasis.pathApply.
Admitted.
*) (*
      Definition basis : lmodBasisType _
       := lmodBasis.Build elem_li span.*)
    End Basis.
  End Rmul.

  Close Scope ring_scope.

  Module Exports.
    Canonical Rmul.lmodType.
    (*Notation AlgModToRingMod := AlgModToRingMod.*)
    Notation Rmul := Rmul.lmodType.
    Notation "'[alg ' R Q '\e_' i ']'" := (Rmul.lmodType R Q i) (at level 0).
  End Exports.


End PAlgSub.
Export PAlgSub.Exports.