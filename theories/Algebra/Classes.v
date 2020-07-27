Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
    From mathcomp Require Import ssrbool.
Set Warnings "parsing".

From mathcomp Require Import ssreflect ssrfun seq.
From mathcomp Require Import eqtype choice fintype bigop generic_quotient tuple finfun.

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".


Open Scope ring_scope.
Set Implicit Arguments.
Unset Strict Implicit.

Module lmodIso.
    Section Def.
        Variable (R : ringType) (M N : lmodType R).
        Record mixin (f : {linear M -> N}) := Mixin { bij : bijective f; }.
        Record type := Pack { sort : _ ;  class_of : mixin sort; }.
        
        Definition Build {f : M -> N} (m : linear f) (b : bijective f)
            := @Pack (Linear m) (Mixin (b : bijective (Linear m))).
    End Def.
    Axiom CosetIrrelevance : forall (R : ringType) (m1 m2 : lmodType R), type m1 m2 -> m1 = m2.
    
End lmodIso.

Notation lmodIsoType := lmodIso.type.
Notation lmodIsoBuild := lmodIso.Build.
Notation CosetIrrelevance := lmodIso.CosetIrrelevance.

Close Scope ring_scope.