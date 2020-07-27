Require Import Coq.Program.Tactics.
From mathcomp Require Import ssreflect ssrfun.
From mathcomp Require Import eqtype choice ssralg seq bigop.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
    From mathcomp Require Import ssrbool.
Set Warnings "parsing".

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope ring_scope.


Module idempotent.
    Section Def.
        Variable (R : ringType).
        Definition axiom (e : R) := e*e == e.
        Record type := Pack { sort : _ ; _ : axiom sort; }.
        Local Coercion sort : type >-> GRing.Ring.sort.

        Definition orthogonal (e1 e2 : type) := ((sort e1) == (sort e2)) || ((sort e1)*e2 == 0) && (e2*e1 == 0).
    End Def.
    Module Exports.
        Notation idempType := type.
        Coercion sort : type >-> GRing.Ring.sort.
    End Exports.
End idempotent.
Export idempotent.Exports.
Module basicAlgebra.
    Section Def.
        Variable (R : ringType).

        Definition allUnique {A : algType R} (L : seq (idempType A))
            := uniq (map (@idempotent.sort A) L).

        Definition allOrthogonal {A : algType R} (L : seq (idempType A))
            := all2 (@idempotent.orthogonal A) L L.

        Definition allPrimitive {A : algType R} (L : seq (idempType A))
            := forall e1 e2 : idempType A,
                all (fun e : idempType A => ((idempotent.sort e) != (idempotent.sort e1) + (idempotent.sort e2))%R) L.

        Definition sumToOne {A : algType R} (L : seq (idempType A))
            := \sum_(e <- L)(idempotent.sort e) == 1.

        Definition axiom {A : algType R} (L : seq (idempType A))
            := all2 (fun e1 e2 => true) L L.
        
        Record class (A : algType R) := Class {
            cpoi : seq (idempType A);
            _ : allUnique cpoi;
            _ : allOrthogonal cpoi;
            _ : allPrimitive cpoi;
            _ : sumToOne cpoi;
            _ : axiom cpoi;
        }.
        Record type := Pack { sort : _; class_of : class sort; }.
    End Def.
    Local Notation basicAlgType := type.
    Local Coercion sort : type >-> GRing.Algebra.type.

    Section Theory.
    Variable (R : ringType) (A : basicAlgType R).

    Definition makeQuiver : quiverType.

    End Theory.
    Module Exports.
        Notation basicLAlgType := type.
        Coercion sort : type >-> GRing.Algebra.type.
    End Exports.
End basicAlgebra.