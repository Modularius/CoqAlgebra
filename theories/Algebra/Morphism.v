Require Import Coq.Program.Tactics.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun.
From mathcomp Require Import eqtype choice.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope ring_scope.

Require Import Submodule Quotient.
Module linKernel.
  Section Def.
    Variable (R : ringType) (U V : lmodType R) (f : {linear U -> V}).
    Definition inKer : predPredType U := fun x => f x == 0.

    Definition ker_elem := [qualify x | x \in inKer].

    Lemma ker_subModule : GRing.submod_closed (ker_elem).
    Proof. split=>[|a x y].
      by rewrite qualifE unfold_in GRing.linear0.
      rewrite qualifE !unfold_in !GRing.linearP -!(rwP eqP)=>Hx Hy.
      by rewrite Hx Hy GRing.addr0 GRing.scaler0.
    Qed.

    Definition kernel := subLmodPack ker_subModule.
  End Def.
  Module Exports.
    Notation kernel := kernel.
    Notation "\ker( f )" := (kernel f) (at level 0).
  End Exports.
End linKernel.
Export linKernel.Exports.


Module linImage.
  Section Def.
    Variable (R : ringType) (U V : lmodType R) (f : {linear U -> V}).
    Definition U' := option U.
    Definition V' := option V.
    Definition f' : U' -> V' := fun u' => match u' with Some u => Some (f u)|None => None end.

    Definition preim (v : V) := {u : U | f u == v}.

    Definition inIm : predPredType V :=
    fun v : V => 
      choose (fun u : U' => f' u == Some v) None != None.

    Definition im_elem := [qualify x | x \in inIm].

    Lemma im_subModule : GRing.submod_closed (im_elem).
    Proof. split.
      rewrite qualifE unfold_in.
rewrite /choose/insub.
(*case idP.
case(choose (fun u : U' => f' u == Some 0) None) as []eqn:E.
by rewrite E.
assert(choose (fun u : U' => f' u == Some 0) None = Some 0).
rewrite /choose.
case(insub (@None U)).
move=>x.
simpl.
rewrite xchooseP.*)
Admitted. (*
      by rewrite qualifE unfold_in GRing.linear0.
      move=>a x y Hx Hy.
      rewrite qualifE unfold_in GRing.linearP.
      rewrite unfold_in in Hx; apply (rwP eqP) in Hx.
      rewrite unfold_in in Hy; apply (rwP eqP) in Hy.
      by rewrite Hx Hy GRing.addr0 GRing.scaler0.
    Qed. *)

    Definition image := subLmodPack im_subModule.
  End Def.
  Module Exports.
    Notation image := image.
    Notation "\image( f )" := (image f) (at level 0).
  End Exports.
End linImage.
Export linImage.Exports.


Module linCokernel.
  Section Def.
    Variable (R : ringType) (U V : lmodType R) (f : {linear U -> V}).
    Definition coker := quotLmod.Pack (image f).
  End Def.
  Module Exports.
    Notation cokernel := coker.
    Notation "\coker( f )" := (coker f) (at level 0).
  End Exports.
End linCokernel.
Export linCokernel.Exports.

Module linCoimage.
  Section Def.
    Variable (R : ringType) (U V : lmodType R) (f : {linear U -> V}).
    Definition coim := quotLmod.Pack (kernel f).
  End Def.
  Module Exports.
    Notation coimage := coim.
    Notation "\coimage( f )" := (coim f) (at level 0).
  End Exports.
End linCoimage.
Export linCoimage.Exports.


Module linID.
  Section Def.
    Variable (R : ringType) (M : lmodType R).
    Definition map : {linear M -> M} := locked (GRing.idfun_linear M).
    Lemma chain x : x = (map x).
    Proof. by rewrite /map -(lock). Qed.
  End Def.
End linID.
Notation "\id_ M " := (linID.map M) (at level 36, right associativity).
Notation linIDChain := (linID.chain).

Module linConcat.
  Section Def.
    Variable (R : ringType) (A B C : lmodType R)
    (f : {linear A -> B}) (g : {linear B -> C}).
    
    Definition map : {linear A -> C} := locked (GRing.comp_linear g f).
    Lemma chain x : g (f x) = (map x).
    Proof. by rewrite /map -(lock (GRing.comp_linear _ _)). Qed.
  End Def.
End linConcat.
Notation " g \oLin f " := (linConcat.map f g) (at level 36, right associativity).
Notation linCompChain := (linConcat.chain).


Module linZero.
  Section Def.
    Variable (R : ringType) (M1 M2 : lmodType R).

    Lemma lmod_zero_lin : linear (fun _ : M1 => @GRing.zero M2).
    Proof. by rewrite /(linear _)=>a x y; rewrite GRing.scaler0 GRing.addr0. Qed.

    Definition map : {linear M1 -> M2} := locked (Linear lmod_zero_lin).
    Lemma chain x : 0 = (map x).
    Proof. by rewrite /map -(lock). Qed.
  End Def.
End linZero.
Notation "\0_( M1 , M2 )" := (linZero.map M1 M2) (at level 36, right associativity).
Notation linZeroChain := (linZero.chain).

(*
Module linInj.
  Section Def.
    Variable (R : ringType) (M N : lmodType R).

    Record mixin_of (f : {linear M -> N}) := Mixin { axiom_of : injective f; }.
    Record type := Pack {
      sort : _;
      class_of : @mixin_of sort;
    }.
  End Def.
    Module Exports.
      Coercion sort : type >-> GRing.Linear.map.
      Coercion class_of : type >-> mixin_of.
      Coercion axiom_of : mixin_of >-> injective.
    End Exports.
End linInj.

Module linSurj.
  Section Def.
    Variable (R : ringType) (M N : lmodType R).

    Record mixin_of (f : {linear M -> N}) := Mixin { inv: {linear N -> M} ; _ : cancel inv f; }.
    Record type := Pack {
      sort : _;
      class_of : mixin_of sort;
    }.
    Lemma linSurjK (f' : type) : cancel (inv (class_of f')) (sort f'). Proof. by destruct f', class_of0=>/=. Qed.
  End Def.
  Module Exports.
    Coercion sort : type >-> GRing.Linear.map.
    Coercion class_of : type >-> mixin_of.
    Notation linSurjK := linSurjK.
  End Exports.
End linSurj.

Module linIsom.
  Section Def.
    Variable (R : ringType) (M N : lmodType R).

    Record mixin_of (f : {linear M -> N}) := Mixin { inj_mixin : linInj.mixin_of f; surj_mixin : linSurj.mixin_of f; }.
    Record type := Pack {
      sort : _;
      class_of : mixin_of sort;
    }.
    Definition toInj (f' : type) := linInj.Pack (inj_mixin (class_of f')).
    Definition toSurj (f' : type) := linSurj.Pack (surj_mixin (class_of f')).
  End Def.
  Module Exports.
    Coercion sort : type >-> GRing.Linear.map.
    Coercion class_of : type >-> mixin_of.
    Coercion toInj : type >-> linInj.type.
    Coercion toSurj : type >-> linSurj.type.
  End Exports.
End linIsom.
*)

Section Results.
Variable (R : ringType) (M1 M2 : lmodType R).
Lemma linear_eq (p q : {linear M1 -> M2}) : p = q <-> (p : M1 -> M2) = (q : M1 -> M2).
Proof.
  split=>H.
  by inversion H.
  destruct p, q. simpl in H; destruct H.
  by rewrite (proof_irrelevance _ c c0).
Qed.
End Results.

Module linIsom.
  Section Def.
    Variable (R : ringType) (M1 M2 : lmodType R).
    Record mixin  (f : M1 -> M2)
                  (g : M2 -> M1)
   := Mixin {
      isom_lin : linear f;
      isom_inv_lin : linear g;
      isomfK : cancel f g;
      isomKf : cancel g f;
      }.
    Record type := Pack { isom_map : _ ; isom_mapI : _;
                          class_of : mixin isom_map isom_mapI;
                          isom_linmap : {linear M1 -> M2} := (Linear (isom_lin class_of));
                          isom_linmapI : {linear M2 -> M1} := (Linear (isom_inv_lin class_of));
    }.
    Definition Build (f : M1 -> M2)
                     (g : M2 -> M1)
                     (flin : linear f)
                     (glin : linear g)
                     (fg : cancel f g)
                     (gf : cancel g f)
                      := Pack (Mixin flin glin fg gf).

    Program Definition BuildPack (f : M1 -> M2) (g : M2 -> M1)
                      (fglin : linear f /\ linear g)
                      (fg_gf : cancel f g /\ cancel g f)
                      := Pack (@Mixin f g _ _ _ _).

    Lemma isomlK (p : type) : cancel (isom_linmap p) (isom_linmapI p).
    Proof. rewrite /isom_linmap/isom_linmapI=>/=.
    apply (isomfK (class_of p)). Qed.
    
    Lemma isomKl (p : type) : cancel (isom_linmapI p) (isom_linmap p).
    Proof. rewrite /isom_linmap/isom_linmapI=>/=.
    apply (isomKf (class_of p)). Qed.
  End Def.

  Import GRing.
  Section Concat.
    Variable (R : ringType) (M1 M2 M3 : lmodType R).
    Variable (I1 : type M1 M2) (I2 : type M2 M3).
    Local Coercion class_of : type >-> mixin.
    Program Definition Concat : type M1 M3
     := @Build _ _ _
          (isom_linmap I2 \o isom_linmap I1)
          (isom_linmapI I1 \o isom_linmapI I2)
          _ _ _ _.
    Next Obligation.
    apply (linearPZ (comp_linear (isom_linmap I2) (isom_linmap I1))).
    Qed. Next Obligation.
    apply (linearPZ (comp_linear (isom_linmapI I1) (isom_linmapI I2))).
    Qed. Next Obligation.
    rewrite /isom_linmap/isom_linmapI=>/=.
    by rewrite/comp=>x; rewrite (isomfK I2) (isomfK I1).
    Qed. Next Obligation.
    rewrite /isom_linmap/isom_linmapI=>/=.
    by rewrite/comp=>x; rewrite (isomKf I1) (isomKf I2).
    Qed.
  End Concat.

  Section Results.
  Variable (R : ringType) (M1 M2 : lmodType R).
  Lemma concatKl (p : type M1 M2) : (isom_linmap p) \oLin (isom_linmapI p) = \id__.
  Proof. rewrite !linear_eq.
    apply functional_extensionality=>x.
    by rewrite -linCompChain (isomKl p) -linIDChain.
  Qed.
  Lemma concatlK (p : type M1 M2) : (isom_linmapI p) \oLin (isom_linmap p) = \id__.
  Proof. rewrite !linear_eq.
    apply functional_extensionality=>x.
    by rewrite -linCompChain (isomlK p) -linIDChain.
  Qed.
  End Results.
End linIsom.
Notation linIsomType := (linIsom.type).
Notation linIsomBuild := (linIsom.Build).
Notation linIsomBuildPack := (linIsom.BuildPack).
Notation linIsomConcat := (linIsom.Concat).
Notation isom_linmap := (linIsom.isom_linmap).
Notation isom_linmapI := (linIsom.isom_linmapI).
Notation isomfK := (linIsom.isomfK).
Notation isomKf := (linIsom.isomKf).
Notation isomlK := (linIsom.isomlK).
Notation isomKl := (linIsom.isomKl).
Coercion linIsom.class_of : linIsomType >-> linIsom.mixin.
Coercion linIsom.isom_linmap : linIsomType >-> GRing.Linear.map.
Notation "inv( f )" := (isom_linmapI f) (at level 36, right associativity).


Close Scope ring_scope.
