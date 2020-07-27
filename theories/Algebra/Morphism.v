Require Import Coq.Program.Tactics.
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
    Proof. split.
      by rewrite qualifE unfold_in GRing.linear0.
      move=>a x y Hx Hy.
      rewrite qualifE unfold_in GRing.linearP.
      rewrite unfold_in in Hx; apply (rwP eqP) in Hx.
      rewrite unfold_in in Hy; apply (rwP eqP) in Hy.
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
    Definition map {R : ringType} (M : lmodType R) := GRing.idfun_linear M.
  End Def.
End linID.

Module linConcat.
  Section Def.
    Definition map {R : ringType} {A B C : lmodType R}
      (f : {linear A -> B})
      (g : {linear B -> C})
     : {linear A -> C}
     := GRing.comp_linear g f.
  End Def.
End linConcat.


Module linZero.
  Section Def.
    Lemma lmod_zero_add {R : ringType} (M1 M2 : lmodType R) : additive (fun _ : M1 => @GRing.zero M2).
    Proof. by rewrite /(additive _)/morphism_2 GRing.addrN. Qed.
    Lemma lmod_zero_lin {R : ringType} (M1 M2 : lmodType R) : linear (fun _ : M1 => @GRing.zero M2).
    Proof. by rewrite /(linear _)=>a x y; rewrite GRing.scaler0 GRing.addr0. Qed.
    Lemma lmod_zero_sca {R : ringType} (M1 M2 : lmodType R) : scalable (fun _ : M1 => @GRing.zero M2).
    Proof. by rewrite /(scalable _)/morphism_1=> r x; rewrite GRing.scaler0. Qed.

    Definition map {R : ringType} (M1 M2 : lmodType R)
     := Linear (GRing.Linear.Class (@lmod_zero_add R M1 M2) (@lmod_zero_sca R M1 M2)).
  End Def.
End linZero.


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

Close Scope ring_scope.
