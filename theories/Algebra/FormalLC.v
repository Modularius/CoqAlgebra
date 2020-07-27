Require Import Coq.Program.Tactics.
Require Import Coq.Logic.FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun seq.
From mathcomp Require Import bigop eqtype choice.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Algebras DirectSum Basis FreeModules Submodule.
Open Scope ring_scope.

Module formalLC.
  Section Def.
    Variable (R : ringType) (T : Type).
    Definition type := T -> R.

    Axiom type_eqMixin : Equality.mixin_of type.
    Definition type_eqType := Equality.Pack type_eqMixin.
    Axiom type_choiceMixin : Choice.mixin_of type.
    Definition type_choiceClass := Choice.Class type_eqMixin type_choiceMixin.
    Canonical type_choiceType := Choice.Pack type_choiceClass.

    Section Zmod.
      Definition Add : type -> type -> type
         := fun x1 x2 => fun p => (x1 p) + (x2 p).

      Definition Neg : type -> type
         := fun x => fun p => -(x p).

      Definition Zero : type := fun _ => 0.

      Lemma addA : associative Add.
      Proof. rewrite/Add=>x y z;
      apply functional_extensionality=>p.
      by rewrite GRing.addrA. Qed.

      Lemma addC : commutative Add.
      Proof. rewrite/Add=>x y;
      apply functional_extensionality=>p.
      by rewrite GRing.addrC. Qed.

      Lemma left_id0 : left_id Zero Add.
      Proof. rewrite/Add/Zero=>x;
      apply functional_extensionality=>p.
      by rewrite GRing.add0r. Qed.

      Lemma right_id0 : right_id Zero Add.
      Proof. rewrite/Add/Zero=>x;
      apply functional_extensionality=>p.
      by rewrite GRing.addr0. Qed.

      Lemma left_inv0 : left_inverse Zero Neg Add.
      Proof. rewrite /Add/Neg/Zero=>x;
      apply functional_extensionality=>p.
      by rewrite GRing.addNr. Qed.

      Lemma right_inv0 : right_inverse Zero Neg Add.
      Proof. rewrite /Add/Neg/Zero=>x;
      apply functional_extensionality=>p.
      by rewrite GRing.addrN. Qed.

      Definition type_zmodMixin := ZmodMixin addA addC left_id0 left_inv0.
      Canonical type_zmodType := ZmodType type type_zmodMixin.
    End Zmod.

    Section Lmod.
      Definition Scale (r : R) (f : type)
       := fun p => r * (f p).

      Lemma scaleAxiom : forall (a b : R) (v : type_zmodType),
        Scale a (Scale b v) = Scale (a * b) v.
      Proof. rewrite/Scale=> a b v;
      apply functional_extensionality=>p.
      by rewrite GRing.mulrA.
      Qed.
      Lemma left_id_scale : left_id 1 Scale.
      Proof. rewrite/Scale=> a;
      apply functional_extensionality=>p.
      by rewrite GRing.mul1r.
      Qed.
      Lemma right_d_scale : right_distributive Scale Add.
      Proof. rewrite/Scale/Add=> r x y;
      apply functional_extensionality=>p.
      by rewrite GRing.mulrDr. Qed.

      Lemma lmodMorph : forall v : type_zmodType,
        morphism_2 (Scale^~ v) (fun x y : R => x + y) (fun x y : type => x + y).
      Proof. rewrite/morphism_2/Scale/GRing.add=>f x y/=.
      rewrite/Add; apply functional_extensionality=>p/=.
      by rewrite GRing.mulrDl. Qed.

      Definition type_lmodMixin := LmodMixin scaleAxiom left_id_scale right_d_scale lmodMorph.
      Canonical type_lmodType := LmodType R type_zmodType type_lmodMixin.
    End Lmod.
  End Def.

  Section FreeLmod.
    Variable (R : ringType) (T : eqType).
    Notation lmod_type := (type_lmodType R T).
    Definition elem (p : T) : lmod_type
     := fun p' => if p' == p then 1 else 0.
    Lemma elem_inj : injective elem. Proof.
      rewrite /elem=> x y.
      case (x == y) as []eqn:E=>H; [by apply (rwP eqP) in E |].
      assert (X := equal_f H x); simpl in X.
      rewrite E eq_refl in X; apply (rwP eqP) in X.
      assert (P := GRing.oner_eq0 R).
      by rewrite X in P.
    Qed.
    Lemma elem_nondeg : non_degenerate elem. Proof.
      rewrite /elem=> x.
      apply (rwP negP); rewrite /not -(rwP eqP)=>H.
      assert (A := equal_f H x); rewrite eq_refl in A.
      rewrite /(GRing.zero _) in A; simpl in A.
      rewrite /formalLC.Zero in A.
      apply (rwP eqP) in A.
      by rewrite (GRing.oner_eq0 R) in A.
    Qed.

    Definition genSet := lmodSet.Build elem_inj elem_nondeg.

    Section PathApply.
      Definition pathApply (p : T) : lmod_type -> R := fun f => f p.

      Lemma pathApply_lin (p : T) : linear_for (@GRing.mul R) (pathApply p).
      Proof. by rewrite /(GRing.add _)=>/=. Qed.

      Definition pathApplyLin (p : T) : {linear lmod_type -> R |*%R}
        := Linear (pathApply_lin p).

      Lemma pathApplyLin_one : forall b, pathApplyLin b (elem b) == 1.
        Proof. simpl; rewrite /pathApply/elem=>b/=; by rewrite !eq_refl. Qed.
      Lemma pathApplyLin_zero : forall b1 b2, b1 <> b2 -> pathApplyLin b1 (elem b2) == 0.
      Proof. rewrite /pathApply/elem=>b1 b2/=; rewrite /not=> H.
        case(b1 == b2) as []eqn:E=>//.
        by apply (rwP eqP) in E.
        by rewrite /pathApply E eq_refl.
      Qed.
    End PathApply.

    Lemma elem_li : lmodLISet.axiom genSet.
    Proof. rewrite /elem => F proj =>H finb; move:H.
      rewrite -(rwP eqP)=>H.
      apply (f_equal (pathApplyLin (lmodFinSubSetIncl finb))) in H; move:H.
      rewrite (GRing.raddf_sum (pathApplyLin (lmodFinSubSetIncl finb))) /formalLC.Zero=>/=.
      rewrite /pathApply/elem=>H.
      assert(forall i, true->
        (proj i * (if lmodFinSubSetIncl finb == lmodFinSubSetIncl i then 1 else 0)) =
        ((if lmodFinSubSetIncl i == lmodFinSubSetIncl finb then proj i else 0))
      ).
      move=>i _.
      by case(lmodFinSubSetIncl finb == lmodFinSubSetIncl i) as []eqn:E ;
      [rewrite GRing.mulr1|rewrite GRing.mulr0]; rewrite eq_sym in E;
      rewrite E.
      rewrite (eq_bigr _ H0) in H; clear H0.
      rewrite -big_mkcond in H.
      simpl in H.
      destruct F as [F f I].
      simpl in f, H.
    Admitted.

    Definition li_set : lmodLISet.type _
      := lmodLISet.Build elem_li.

    (*Definition freeModType := freeLmod.Build basis.*)

  End FreeLmod.
(*  Section FreeSubmod.
    Variable (R : ringType) (T : eqType).
    Variable inSet : predType T.
    Notation lmod_type := {e : type_lmodType R T | inSet e}.
    
    
    Lemma subModule
    : GRing.submod_closed (subLmod.qualSubElem inSet).
    Proof. split=>[|a x y];rewrite qualifE !unfold_in.
    by rewrite GRing.mul0r eq_refl.
    rewrite -!(rwP eqP)=>Hx Hy;
    by rewrite Hx Hy GRing.mulrDl -!GRing.mulrA !PAlgBasis.idem.
    Qed.
  End FreeSubmod.
  *)
  Module Exports.
    Notation formalLCType := type.
    (*Notation formalLCFreeLmodType := freeModType.*)
  End Exports.
End formalLC.
Export formalLC.Exports.
(*
Module formalLC_funSupp.
  Module finSuppFun.
    Section Def.
      Variable (A : eqType) (R : ringType) (B : lmodType R).
      Record mixin (f : A -> B) := Mixin {
          finT : lmodFinBasis.FinSet.type;
          _ : forall a : A, reflect (a \in finT)(f a == 0);
      }.
      Record type := Pack { sort : _ ; mixin_of : mixin sort}.
    End Def.
    Module Exports.
      Notation finSuppFunType := type.
    End Exports.
  End finSuppFun.
  Section Def.
    Variable (A : eqType) (R : ringType) (B : lmodType R).
  
*)
Close Scope ring_scope.
