Require Import Coq.Init.Notations.
Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Logic.
Require Import Coq.Lists.List.
Require Import Coq.Program.Tactics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Bool.Bool.
From mathcomp Require Import ssreflect.
From mathcomp Require Import ssrfun.
From mathcomp Require Import ssrnat.
From mathcomp Require Import ssrbool.
From mathcomp Require Import eqtype.
From mathcomp Require Import ssralg.
From mathcomp Require Import bigop.
From mathcomp Require Import choice.
From mathcomp Require Import fintype.

Require Import Algebras Morphism.

Open Scope ring_scope.
Module Hom.

Definition add {R : ringType} (U V : lmodType R) (f g : {linear U -> V}) : {linear U -> V}
 := (GRing.add_fun_linear f g).

Definition neg {R : ringType} (U V : lmodType R) (f : {linear U -> V}) : {linear U -> V}
 := (GRing.sub_fun_linear (linZero.map U V) f).


Program Definition zmodMixin {R : ringType} (U V : lmodType R)
 := @ZmodMixin _ (linZero.map U V) (neg U V) (add U V) _ _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

(*
Definition zmod {R : ringType} (U V : lmodType R)
 := ZmodType _ (zmodMixin U V).
*)

Axiom class : forall {R : ringType} (U V : lmodType R)
 , GRing.Lmodule.class_of R {linear U -> V}.

Canonical type {R : ringType} (U V : lmodType R) := @GRing.Lmodule.Pack R (Phant R) _ (class U V) {linear U -> V}.



Definition leftHomMorph {R : ringType} {U V : lmodType R}
  (f : type U V) (W : lmodType R) : type W U -> type W V
    := fun g : {linear W -> U} => GRing.comp_linear f g.

Axiom leftHomMorph_lin : forall {R : ringType} {U V : lmodType R}
  (f : {linear U -> V}) (W : lmodType R)
    , linear (leftHomMorph f W).


Definition rightHomMorph {R : ringType} (T : lmodType R) {U V : lmodType R}
  (f : type U V) : type V T -> type U T
    := fun g : {linear V -> T} => GRing.comp_linear g f.

Axiom rightHomMorph_lin : forall {R : ringType} (T : lmodType R) {U V : lmodType R}
  (f : {linear U -> V})
    , linear (rightHomMorph T f).

Module Exports.

Canonical leftHomMorphLin {R : ringType} {U V : lmodType R}
  (f : type U V) (W : lmodType R) := Linear (leftHomMorph_lin f W).

Canonical rightHomMorphLin {R : ringType} (T : lmodType R) {U V : lmodType R}
  (f : type U V) := Linear (rightHomMorph_lin T f).

Notation homType := type.
Notation homMorphL := leftHomMorphLin.
Notation homMorphR := rightHomMorphLin.
Notation "\Hom( A , B )" := (homType A B) (at level 99).
Notation "\fHom1( f , B )" := (homMorphL f B) (at level 99).
Notation "\fHom2( A , f )" := (homMorphR A f) (at level 99).
End Exports.

End Hom.
Export Hom.Exports.