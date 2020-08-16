Require Import Coq.Program.Tactics.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun eqtype choice
  fintype finfun matrix bigop seq.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool.

Set Warnings "parsing".
Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope ring_scope.
(*
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
*)

Require Import Basis FreeModules Dimension.
Open Scope ring_scope.

Module lmodMatrix.
  Section Def.
    Variable (R : ringType) (M1 M2 : freeLmodType R).

    Definition type := ((basis M1) * (basis M2))%type -> R.
  End Def.

  Section Add.
    Variable (R : ringType) (M1 M2 : freeLmodType R).
    Definition AddMatrix (M : type M1 M2) (N : type M1 M2)
     : type M1 M2 := fun p => M(p.1,p.2) + N(p.1,p.2).
  End Add.

  Section Mul.
    Variable (R : ringType) (M1 M3 : freeLmodType R)
      (M2 : fdFreeLmodType R).
    Definition MulMatrix (M : type M1 (fdFreeLmod.to_arb M2)) (N : type (fdFreeLmod.to_arb M2) M3)
     : type M1 M3 := fun p =>  \sum_b M(p.1,b) * N(b,p.2).
  End Mul.

  Section Coercion.
    Variable (R : ringIBNType) (M1 M2 : fdFreeLmodType R).

    Definition to_ssrmatrix (A : type (fdFreeLmod.to_arb M1) (fdFreeLmod.to_arb M2))
    : 'M[R]_(fdFreeLmodDimension.dim M1, fdFreeLmodDimension.dim M2)
     := \matrix[tt]_(i,j)
      (A (@enum_val (lmodFinSet.sort (lmodFinBasis.sort (fdBasis M1))) _ i,@enum_val (lmodFinSet.sort (lmodFinBasis.sort (fdBasis M2))) _ j)).
(*
    Definition from_ssrmatrix (A : 'M[R]_(fdFreeLmodDimension.dim M1, fdFreeLmodDimension.dim M2))
      : type _ _
     := fun ij => A (@enum_rank (lmodFinSet.sort (lmodFinBasis.sort (fdBasis M1))) ij.1) (@enum_rank (lmodFinSet.sort (lmodFinBasis.sort (fdBasis M2))) ij.2).
     *)
  End Coercion.

  Module Exports.
    Notation lmodMatrixType := type.
  End Exports.
End lmodMatrix.
Export lmodMatrix.Exports.

Module linExtend.
  Section InfiniteDimensional.
    Variable (R : ringType) (M1 M2 : freeLmodType R).
    Section ToMatrix.
      Variable (f : {linear M1 -> M2}).

      Definition to_matrix := fun p =>
        lmodBasisProj (basis M2) p.2 (f ((basis M1) p.1)).

    End ToMatrix.

    Section ToLinear.
      Axiom to_funcR : forall A : lmodMatrixType M1 M2,
        {linear M1 -> M2}.

      Axiom func_to_matrixR : forall (f : {linear M1 -> M2}),
        to_funcR (to_matrix f) = f.

      Axiom matrix_to_funcR : forall A : lmodMatrixType M1 M2,
        to_matrix (to_funcR A) = A.

      Lemma to_funcRK : forall A : lmodMatrixType M1 M2,
        forall (b1 : basis M1) (b2 : basis M2),
          lmodBasisProj (basis M2) b2 ((to_funcR A) (basis M1 b1))
           = A(b1,b2).
      Proof. move => A b1 b2. Admitted.
    End ToLinear.
  End InfiniteDimensional.

  Section FiniteDimensional.
    Variable (R : ringType) (M1 M2 : fdFreeLmodType R).

    Section Def.
      Variable (A : lmodMatrixType (fdFreeLmod.to_arb M1) (fdFreeLmod.to_arb M2)).

      Definition fn := fun m =>
        \sum_(b1 : fdBasis M1)
          \sum_(b2 : fdBasis M2)
              ((lmodFinBasisProj b1 m) * A(b1,b2)) *: (fdBasis M2) b2.

      Lemma lin : linear fn.
      Proof. rewrite/fn=>r x y.
        rewrite GRing.scaler_sumr -big_split=>/=.
        assert(H1 : forall b1, true ->
          \sum_(b2 : (fdBasis M2))
            lmodFinBasisProj b1 (r *: x + y) * A(b1,b2) *: (fdBasis M2) b2
          = (r *: \sum_(b2 : (fdBasis M2))
            ((lmodFinBasisProj b1 x) * A(b1,b2)) *: (fdBasis M2) b2) +
                \sum_(b2 : (fdBasis M2))
            ((lmodFinBasisProj b1 y) * A(b1,b2)) *: (fdBasis M2) b2
            ).
        move=> b1 _.
        rewrite GRing.scaler_sumr -big_split=>/=.
        assert(H2 : forall b2, true ->
          lmodFinBasisProj b1 (r *: x + y) * A(b1,b2) *: (fdBasis M2) b2
          = (r *: (lmodFinBasisProj b1 x * A(b1,b2) *: (fdBasis M2) b2)) +
            lmodFinBasisProj b1 y * A(b1,b2) *: (fdBasis M2) b2).
        by move=> b2 _; rewrite GRing.linearP GRing.mulrDl GRing.scalerDl !GRing.scalerA GRing.mulrA.
        by rewrite (eq_bigr _ H2).
        by rewrite (eq_bigr _ H1).
      Qed.
      Definition to_func := Linear lin.
    End Def.

    Section Results.
      Variable (A : lmodMatrixType (fdFreeLmod.to_arb M1) (fdFreeLmod.to_arb M2)).
 
      Lemma projToK :
        forall (b1 : (fdBasis M1)) (b2 : (fdBasis M2)),
          lmodFinBasisProj b2 (to_func A ((fdBasis M1) b1)) = A(b1,b2).
      Proof. rewrite /to_func/lmodFinBasisProj=>b1 b2/=.
      assert(lmodFinBasis.coef_fn (T:=fdBasis M2) b2
      (fn A ((fdBasis M1) b1)) = A (b1, b2)).
      rewrite /lmodFinBasis.coef_fn/fn.
      destruct(lmodFinBasis.span_ax (fdBasis M2) _) as [c H]=>/=.
      assert(
        c b2 (\sum_b0 \sum_b3
         (lmodFinBasis.coef_fn b0 (fdBasis M1 b1) *
          A (b0, b3)) *: fdBasis M2 b3) = A(b1, b2)
      ).
       Admitted.
    End Results.
  End FiniteDimensional.
  Module Exports.
    Notation extendLinearly := to_func.
    Notation extendLinearlyRisky := to_funcR.
    Notation extendLinearlyRiskyK := to_funcRK.

    Notation matrix_of := to_matrix.

    (*Notation extendLinearlyK := projToK.
    Notation extendLinearlyRisky1 := extendLinearlyR1.
    Notation extendLinearlyRisky1K := extendLinearlyR1K.
    Notation extendMatrixLinearlyRisky := extendMatrixLinearlyR.
    Notation extendLinearlyRiskyK := extendLinearlyRK.*)
  End Exports.
End linExtend.
Export linExtend.Exports.
(*
Module freeLmodMorphism.
  Section Def.

    Variable (R : ringType).
    Section fd.
      Variable (M1 M2 : fdFreeLmodType R) (f : {linear M1 -> M2}).
      Definition fd_linear_to_matrix : lmodFinMatrixType (basis M1) (basis M2)
        := [ffun b1b2 => lmodBasisProj (basis M2) b1b2.2 (f ((basis M1) b1b2.1))].
    End fd.
    Variable (M1 M2 : freeLmodType R) (f : {linear M1 -> M2}).
    Definition linear_to_matrix : lmodMatrixType (freeLmod.basis M1) (freeLmod.basis M2)
      := fun b1b2 => lmodBasisProj (freeLmod.basis M2) b1b2.2 (f ((freeLmod.basis M1) b1b2.1)).
  End Def.
End freeLmodMorphism.
Notation fdFreeLmod_linear_to_matrix := freeLmodMorphism.fd_linear_to_matrix.
Notation freeLmod_linear_to_matrix := freeLmodMorphism.linear_to_matrix.
Lemma linear_eq_matrix (R : ringType) (M1 M2 : freeLmodType R) (f : {linear M1 -> M2})
 : f = extendLinearlyRisky (freeLmod_linear_to_matrix f).
 Proof.
   assert (@eq (M1 -> M2) f (extendLinearlyRisky (freeLmod_linear_to_matrix f))).
 apply functional_extensionality=>m.
 Admitted.
*)

Close Scope ring_scope.
