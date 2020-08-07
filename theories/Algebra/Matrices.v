Require Import Coq.Program.Tactics.
From mathcomp Require Import ssreflect ssrfun eqtype choice
  fintype finfun matrix bigop seq.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool.

Set Warnings "parsing".
Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
Set Warnings "ambiguous-paths".

Set Implicit Arguments.
Unset Strict Implicit.
    From mathcomp Require Import ssralg.

Open Scope ring_scope.

Module ringFormalSum.
  Section Def.
    Variable (R : ringType) (I : eqType) (L : Monoid.law I).

    Definition formalSum := I -> R.

    Definition formalSumAdd (s t : formalSum) := fun i => s i + t i.

    Definition formalSumScale (r : R) (s : formalSum) := fun i => r * s i.

    Definition IndexSet_Break (i : I) : {S : seq (I*I) | all (fun l => (L l.1 l.2) == i) S}.
    Definition formalSumMul (s t : formalSum)
     := fun i => \sum_(p : prod_finType I I | p.1 + p.2 == i)(s p.1)*(t p.2).
  End Def.
End ringFormalSum.

Require Import Basis FreeModules.


Module lmodMatrix.
  Section Def.
    Variable (R : ringType) (M1 M2 : freeLmodType R).

    Definition type := ((basis M1) * (basis M2))%type -> R.
  End Def.

  Section Add.
    Variable (R : ringType) (M1 M2 : freeLmodType R).
    Definition AddMatrix (M : type M1 M2) (N : type M1 M2)
     : lmodMatrix M1 M2 := fun (a : basis M1) (b : basis M2)
       => M(a,b) + N(a,b).
  End Add.

  Section Mul.
    Variable (R : ringType) (M1 M3 : freeLmodType R)
      (M2 : fdFreeLmodType R).
    Definition MulMatrix (M : type M1 M2) (N : type M2 M3)
     : lmodMatrix M1 M3 := fun (a : basis M1) (c : basis M3)
       => \sum_b M(a,b) * N(b,c).
  End Mul.

  Section Coercion.
    Variable (R : ringType) (M1 M2 : fdFreeLmodType R).

    Definition to_ssrmatrix (A : type M1 M2)
      : 'M[R]_(dim M1, dim M2)
     := \matrix[tt]_(i,j)
      (A (@enum_val (lmodFinSet.sort (lmodFinBasis.sort (basis M1))) _ i,@enum_val (lmodFinSet.sort (lmodFinBasis.sort (basis M2))) _ j)).

    Definition from_ssrmatrix (A : 'M[R]_(dim M1, dim M2))
      : type
     := [ffun ij => A (@enum_rank (lmodFinSet.sort (lmodFinBasis.sort (basis M1))) ij.1) (@enum_rank (lmodFinSet.sort (lmodFinBasis.sort (basis M2))) ij.2)].
  End Coercion.

  Module Exports.
    Notation lmodMatrixType := type.
  End Exports.
End lmodMatrix.
Export lmodMatrix.Exports.

Module linExtend.
  Section FiniteDimensional.
    Variable (R : ringType) (M1 M2 : fdFreeLmodType R).

    Section Def.
      Variable (A : lmodMatrixType B1 B2).

      Definition fn := fun m =>
        \sum_(b1 : B1)
          \sum_(b2 : B2)
              ((lmodBasisProj B1 b1 m) * A(b1,b2)) *: B2 b2.

      Lemma lin : linear fn.
      Proof. rewrite/fn=>r x y.
        rewrite GRing.scaler_sumr -big_split=>/=.
        assert(H1 : forall b1, true ->
          \sum_(b2 : B2)
            lmodBasisProj B1 b1 (r *: x + y) * A(b1,b2) *: B2 b2
          = (r *: \sum_(b2 : B2)
            ((lmodBasisProj B1 b1 x) * A(b1,b2)) *: B2 b2) +
                \sum_(b2 : B2)
            ((lmodBasisProj B1 b1 y) * A(b1,b2)) *: B2 b2
            ).
        move=> b1 _.
        rewrite GRing.scaler_sumr -big_split=>/=.
        assert(H2 : forall b2, true ->
          lmodBasisProj B1 b1 (r *: x + y) * A(b1,b2) *: B2 b2
          = (r *: (lmodBasisProj B1 b1 x * A(b1,b2) *: B2 b2)) +
              lmodBasisProj B1 b1 y * A(b1,b2) *: B2 b2).
        by move=> b2 _; rewrite GRing.linearP GRing.mulrDl GRing.scalerDl !GRing.scalerA GRing.mulrA.
        by rewrite (eq_bigr _ H2).
        by rewrite (eq_bigr _ H1).
      Qed.
      Definition fdFun := Linear lin.
    End Def.

    Section Results.
      Variable (A : lmodMatrixType M1 M2).

      Lemma one_zero : forall (b1 b2 : basis M1), lmodBasisProj _ b1 (B1 b2) = if b1 == b2 then 1%R else 0%R.
      Proof. move=>b1 b2.
      case (b1 == b2) as []eqn:E.
      apply (rwP eqP) in E.
      destruct E.
      Admitted.
      

      Lemma projToK :
        forall (b1 : B1) (b2 : B2),
          lmodBasisProj B2 b2 (fdFun A (B1 b1)) = A(b1,b2).
      Proof. rewrite /fdFun=>b1 b2/=.
      rewrite /fn. Admitted.
    End Results.
  End FiniteDimensional.

  Section Risky.
    Section Def.
      Variable (R : ringType) (M1 M2 : freeLmodType R).

      Axiom extendMatrixLinearlyR : (lmodMatrixType B1 B2) -> {linear M1 -> M2}.

      Axiom extendLinearlyRK : forall (A : (lmodMatrixType B1 B2)) (b1 : B1) (b2 : B2),
      lmodBasisProj B2 b2 (extendMatrixLinearlyR A (B1 b1)) = A(b1,b2).

      Lemma extendLinearlyREq (A B : lmodMatrixType B1 B2)
       : extendMatrixLinearlyR A = extendMatrixLinearlyR B <-> forall (b1 : B1) (b2 : B2), A(b1,b2) == B(b1,b2).
      Proof. split=>[H b1 b2|H].
      by rewrite -!extendLinearlyRK H.
      assert(Q : @eq (M1 -> M2) (extendMatrixLinearlyR A) (extendMatrixLinearlyR B)).
      apply functional_extensionality=>m.
      Admitted.
(*
      Axiom extendLinearlyRK :
        forall (f : B1 -> B2 -> R) (b : B1), (extendLinearlyR f (B1 b)) = B2 (f b).
*)
      Axiom extendLinearlyR1 : (B1 -> M2) -> {linear M1 -> M2}.

      Axiom extendLinearlyR1K :
        forall (f : B1 -> M2) (b : B1), (extendLinearlyR1 f (B1 b)) = (f b).

      Axiom extendLinearlyR1Eq :
      forall (f g : B1 -> M2), (extendLinearlyR1 f = extendLinearlyR1 g) <-> forall (b : B1), f b = g b.
      
      Axiom extendLinearlyR1Eq2 :
        forall (f g : B1 -> M2) (x y : M1),
        (extendLinearlyR1 f x = extendLinearlyR1 g y)
        <-> forall (b : B1),
        (lmodBasisProj B1 b x) *: (f b) = (lmodBasisProj B1 b y) *: (g b).
    End Def.
  End Risky.
  Module Exports.
    Notation extendLinearly := fdFun.
    Notation extendLinearlyK := projToK.
    Notation extendLinearlyRisky1 := extendLinearlyR1.
    Notation extendLinearlyRisky1K := extendLinearlyR1K.
    Notation extendMatrixLinearlyRisky := extendMatrixLinearlyR.
    (*Notation extendLinearlyRiskyK := extendLinearlyRK.*)
  End Exports.
End linExtend.
Export linExtend.Exports.


Close Scope ring_scope.
