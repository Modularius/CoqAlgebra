Require Import Coq.Init.Notations.
Require Import Coq.Init.Datatypes.
Require Import Coq.Program.Tactics.
From Coq.Logic Require Import  FunctionalExtensionality ProofIrrelevance.
Require Import Coq.Bool.Bool.
From mathcomp Require Import ssreflect ssrfun eqtype.
From mathcomp Require Import bigop choice fintype.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool ssrnat.
Set Warnings "parsing".
Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Require Import Algebras Morphism.
Import GRing.

Open Scope ring_scope.
Module Hom.
  Section Def.
    Variable (R : ringType) (U V : lmodType R).
    Definition add (f g : {linear U -> V}) : {linear U -> V}
    := (add_fun_linear f g).

    Definition neg (f : {linear U -> V}) : {linear U -> V}
    := (sub_fun_linear (linZero.map U V) f).

    Lemma addA : associative add.
    Proof. move=>x y z.
    destruct x, y, z.
    rewrite/add=>/=.
    apply linearPZ.
    unfold AddLinear=>/=.

    Program Definition zmodMixin_hom
    := @ZmodMixin {linear U -> V} (linZero.map U V) (neg) (add) _ _ _ _.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.

    Definition zmodType_hom := ZmodType {linear U -> V} zmodMixin_hom.

    Program Definition lmodMixin_hom
    := @LmodMixin R (@ZmodType {linear U -> V} zmodMixin_hom).
Check zmodMixin_hom.
    (*
    Definition zmod {R : ringType} (U V : lmodType R)
    := ZmodType _ (zmodMixin U V).
    *)

    Axiom class : GRing.Lmodule.class_of R {linear U -> V}.
Print ZmodType.
    Definition type := @ZmodType {linear U -> V} zmodMixin_hom.
    Canonical type := @GRing.Lmodule.Pack R (Phant R) _ (class U V) {linear U -> V}.



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