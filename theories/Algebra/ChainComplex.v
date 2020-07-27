Require Import Coq.Init.Notations.
From mathcomp Require Import ssreflect eqtype ssrfun generic_quotient.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool.
Set Warnings "parsing".
Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Require Export Submodule Quotient Morphism Algebras.

Open Scope ring_scope.
Module ChainCpx.
  Definition isComplex {R : ringType} {M1 M2 M3 : lmodType R}
    (f : M1 -> M2) (g : M2 -> M3) := forall x : M1, (g \o f) x == 0.

  Inductive type {R : ringType} (M1 M2 : lmodType R) (f : M1 -> M2) :=
  |CpxStart : type M1 M2 f
  |CpxNext : forall (M3 : lmodType R) (g : M2 -> M3), (isComplex f g) ->
    (type M2 M3 g) -> type M1 M2 f.
End ChainCpx.

Module ExactSequence.
  Definition isExact {R : ringType} {M1 M2 M3 : lmodType R}
    (f : {linear M1 -> M2}) (g : {linear M2 -> M3}) := ChainCpx.isComplex f g /\ (forall y, (g y == 0 -> (exists x, f x == y))).

  Inductive exactType {R : ringType} (M1 M2 : lmodType R) (f : {linear M1 -> M2}) :=
  |ExactStart : exactType M1 M2 f
  |ExactNext : forall (M3 : lmodType R) (g : {linear M2 -> M3}), (isExact f g) ->
    (exactType M2 M3 g) -> exactType M1 M2 f.

  Definition leftZeroExact {R : ringType} (M1 M2 : lmodType R) (f : {linear M1 -> M2}) I
    := ExactNext (lmodZero.type R) M1 (linZero.map _ _) M2 f I.

  Definition rightZeroExact {R : ringType} (M2 M3 : lmodType R) (g : {linear M2 -> M3}) S
    := ExactNext M2 M3 g (lmodZero.type R) (linZero.map _ _) S (ExactStart _ _ _).

  Module Short.
    Definition shortExactSequence {R : ringType} (M1 M2 M3 : lmodType R)
      (f : {linear M1 -> M2}) (g : {linear M2 -> M3})
        (I : isExact (linZero.map _ _) f) (E : isExact f g) (S : isExact g (linZero.map _ _))
      := leftZeroExact M1 M2 f I
          (ExactNext M1 M2 f M3 g E
            (rightZeroExact M2 M3 g S)  ).

    Record ses_type {R : ringType} := SES {
      M1 : lmodType R; M2 : lmodType R; M3 : lmodType R;
      ses_f : {linear M1 -> M2};
      ses_g : {linear M2 -> M3};
      ses_I :> isExact (linZero.map (lmodZero.type R) M1) ses_f;
      ses_E :> isExact ses_f ses_g;
      ses_S :> isExact ses_g (linZero.map M3 (lmodZero.type R));
      ses := shortExactSequence M1 M2 M3 ses_f ses_g ses_I ses_E ses_S;
    }.

    Module Exports.
      Notation ses := ses_type.
      Notation SES := SES.
      Notation "[ 'ses' '0' '-->' A '-->' B '-->' C '-->' '0' ]" :=
          (shortExactSequence A B C)
        (at level 0, format "[ 'ses' '0' '-->' A '-->' B '-->' C '-->' '0' ]",
        A at level 99, B at level 99, C at level 99).

      Notation "[ 'ses' '0' '-->' A '-->' B '-->' C '-->' '0' '|' f ',' g ]" :=
          (shortExactSequence A B C f g)
        (at level 0, format "[ 'ses' '0' '-->' A '-->' B '-->' C '-->' '0' '|' f ',' g ]",
        A at level 99, B at level 99, C at level 99).
    End Exports.
  End Short.

  Program Definition ExtendSequenceHere {R : ringType} (M1 M2 : lmodType R) (f : {linear M1 -> M2})
    : exactType M1 M2 f
   := ExactNext M1 M2 f (lmodZero.type R) (linZero.map _ _) _ (ExactStart _ _ _).
  Next Obligation. Admitted.

  Fixpoint ExtendSequence {R : ringType} {M1 M2 : lmodType R} {f : {linear M1 -> M2}}
   (es : exactType M1 M2 f) {struct es} := match es with
    |ExactNext M3 g E ES => ExactNext M1 M2 f M3 g E (ExtendSequence ES)
    |ExactStart => ExtendSequenceHere M1 M2 f
    end.
End ExactSequence.
Export ExactSequence.Short.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Module subLmodSES.
  Section Def.
    Variable (R : ringType) (M : lmodType R) (S : subLmodType M).
    Program Definition type := [ses 0 --> S --> M --> (quotLmod S) --> 0 | (subLmodIncl S), (quotLmodProj S)] _ _ _.
    Next Obligation.
    split=>[|y H]=>//=.
    refine(ex_intro _ tt _).
    simpl in H.
    rewrite /(eq_op _)=>/=.
    by rewrite eq_sym.
    Qed.
    Next Obligation.
    split=>[x|y H]=>//=.
    rewrite /quotPiLmod.proj=>/=.
    Admitted.
    Next Obligation.
    split=>[x|y H]=>//=.
    refine(ex_intro _ (repr y) _).
    by rewrite /quotPiLmod.proj reprK.
    Qed.
  End Def.
End subLmodSES.

Module linSES.
  Section Def.
    Variable (R : ringType) (M N : lmodType R) (f : {linear M -> N}).
    Program Definition type := [ses 0 --> \ker(f) --> M --> \image(f) --> 0].
  End Def.
End linSES.

Close Scope ring_scope.