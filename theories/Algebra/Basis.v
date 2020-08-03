
Require Import Coq.Program.Tactics.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun eqtype fintype seq bigop.

Require Import Algebras.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Open Scope ring_scope.
Set Implicit Arguments.
Unset Strict Implicit.

Module lmodSet.
  Section Def.
    Variable (R : ringType) (M : lmodType R).
    Definition non_degenerate {T : Type} (elem : T -> M) := forall b : T, elem b != 0%R.

    Record mixin (T : eqType) := Mixin {
      elem : T -> M;
      _ : injective elem;
      _ : non_degenerate elem;
    }.

    Record type := Pack { sort : _; class_of : mixin sort; }.

    Definition Build {T : eqType} (elem : T -> M) (I : injective elem) (ND : non_degenerate elem)
     := Pack (Mixin I ND).

    Lemma typeIsInjective (T : type) : injective (elem (class_of T)).
    Proof. by destruct (class_of T)=>/=. Qed.

    Lemma typeIsNonDegenerate (T : type) : non_degenerate (elem (class_of T)).
    Proof. by destruct (class_of T)=>/=. Qed.

    Definition to_Type (T : type) : Type := (sort T).
  End Def.

  Module Exports.
    Notation lmodSetType := type.
    Notation non_degenerate := non_degenerate.
    Notation typeIsInjective := typeIsInjective.
    Notation typeIsNonDegenerate := typeIsNonDegenerate.
    Coercion to_Type : type >-> Sortclass.
    Coercion elem : mixin >-> Funclass.
    Coercion class_of : type >-> mixin.
  End Exports.
End lmodSet.
Export lmodSet.Exports.

Module lmodFinSubSet.
  Section Def.
    Variable (R : ringType) (M : lmodType R) (B : lmodSetType M).
    Record type  := Pack { sort : finType; incl : sort -> B; _ : injective incl; }.
  End Def.

  Section Coercion.
    Variable (R : ringType) (M : lmodType R) (S : lmodSetType M) (F : type S).
    
    Lemma inj : injective (S \o incl (t:=F)).
    Proof. rewrite /comp=> x y; destruct F as [F' f I].
    by rewrite !(rwP eqP) (inj_eq (@typeIsInjective _ _ S)) (inj_eq I).
    Qed.

    Lemma non_deg : non_degenerate (S \o incl (t:=F)).
    Proof. rewrite/comp => b.
      by apply (@typeIsNonDegenerate _ _ S (incl (t:=F) b)).
    Qed.

    Program Definition to_set  : lmodSetType M
      := @lmodSet.Build _ _ _ (S \o (@incl _ _ S F)) inj non_deg.
  End Coercion.

  Module Exports.
    Notation lmodFinSubSetType := type.
    Notation to_FinType := sort.
    Notation lmodFinSubSetIncl := incl.
    Coercion to_set : type >-> lmodSetType.
  End Exports.
End lmodFinSubSet.
Export lmodFinSubSet.Exports.

Module lmodLISet.
  Section Def.
    Variable (R : ringType) (M : lmodType R).

    Definition li_of (B : lmodSetType M) (F : lmodFinSubSetType B) :=
        forall (c : F -> R), (\sum_(f : F) (c f) *: (B (lmodFinSubSetIncl f))) == 0
          -> forall b, c b == 0.

    Lemma li_of_cascade (B : lmodSetType M) (F : lmodFinSubSetType B)
      : forall (G : lmodFinSubSetType F), li_of F -> li_of G.
    Proof. rewrite/li_of=>G H1 c H2.
    destruct G. simpl in H2.
     Admitted.

    Definition axiom (B : lmodSetType M) :=
        forall (f : lmodFinSubSetType B), li_of f.

    Record mixin (B : lmodSet.type M) := Mixin { _ : axiom B; }.

    Record class (B : lmodSet.type M)
    := Class { base := lmodSet.class_of B; mixin_of : mixin B; }.

    Record type := Pack { sort : _; class_of : class sort; }.

    Definition Build {T : eqType} (elem : T -> M)
      (I : injective elem) (ND : non_degenerate elem)
      (Ax : axiom (lmodSet.Build I ND))
    := Pack (Class (Mixin  Ax)).

    Definition to_set (T : type)
    := lmodSet.Pack (base (class_of T)).

    (*Lemma finLI_axiom (L : lmodFinBasis.LISet.type M) : axiom L.
    Proof. move=>f c H b.
    assert (a := @typeIsLi _ _ L).
    destruct f as [F f I].
    unfold finSubsetFrom in c; simpl in c.
    unfold finSubsetFrom in H; simpl in H.
    unfold finSubsetFrom in b; simpl in b.
    Admitted.

    Definition finLI_to_type (L : lmodFinBasis.LISet.type M)
      := @Build _ _ (@typeIsInjective _ _ L) (@typeIsNonDegenerate _ _ L) (@finLI_axiom L).
      *)
  End Def.

  Module Exports.
    (* Coercion LI_to_set : type >-> lmodSet.type. *)
    Coercion sort : type >-> lmodSet.type.
    Coercion class_of : type >-> class.
    Notation li := axiom.
    Notation lmodLISet := type.
  End Exports.
End lmodLISet.
Export lmodLISet.Exports.

Module lmodSpanningSet.
  Section Def.
    Variable (R : ringType) (M : lmodType R).

    Definition spanP (B : lmodSetType M) (proj : B -> {scalar M})
     := forall m1 m2 : M, reflect (forall b : B, proj b m1 = proj b m2) (m1 == m2).

    Record mixin (B : lmodSetType M) := Mixin {
      proj : B -> {scalar M};
      span : spanP proj;
    }.

    Record class (B : lmodSetType M)
    := Class { base := lmodSet.class_of B; mixin_of : mixin B; }.

    Record type := Pack { sort : _; class_of : class sort; }.

    Definition Build {T : finType} (elem : T -> M)
      (I : injective elem) (ND : non_degenerate elem)
      (proj : (lmodSet.Build I ND) -> {scalar M})
      (span : spanP proj)
      := Pack (Class (Mixin span)).
  End Def.

  Module Exports.
    Notation lmodSpanningSetType := type.
    Notation lmodBasisProj := proj.
    Coercion sort : type >-> lmodSetType.
    Coercion mixin_of : class >-> mixin.
    Coercion class_of : type >-> class.
  End Exports.
  Export Exports.

End lmodSpanningSet.
Export lmodSpanningSet.Exports.

Module lmodBasis.
  Section Def.
    Variable (R : ringType) (M : lmodType R).

    Record class (T : lmodSet.type M) := Class {
      li_mixin_of : lmodLISet.mixin T;
      gen_mixin_of : lmodSpanningSet.mixin T;
    }.

    Record type := Pack { sort : _; class_of : class sort; }.

    Definition Build {T : finType} (elem : T -> M)
      (I : injective elem) (ND : non_degenerate elem)
      (proj : (lmodSet.Build I ND) -> {scalar M})
      (Sp : lmodSpanningSet.spanP proj)
      (LI : li (lmodSet.Build I ND))
    := Pack (Class (lmodLISet.Mixin LI) (lmodSpanningSet.Mixin Sp)).

    Definition to_LI (T : type)
    := lmodLISet.Pack (lmodLISet.Class (li_mixin_of (class_of T))).
    Definition to_Spantype (T : type)
    := lmodSpanningSet.Pack (lmodSpanningSet.Class (gen_mixin_of (class_of T))).
  End Def.

  Module Exports.
    Notation lmodBasisType := type.
    Coercion to_LI : type >-> lmodLISet.type.
    Coercion to_Spantype : type >-> lmodSpanningSetType.
    Coercion class_of : type >-> class.
    Coercion sort : type >-> lmodSetType.
  End Exports.
End lmodBasis.
Export lmodBasis.Exports.

(*
Module lmodLocalFinGenSet.
  Section Def.
    Variable (R : ringType) (M : lmodType R).

    Definition spanProp (B : lmodBasisSetType M) (F : lmodFinSubSetType B) (m : M)
     := (\sum_(b : F) (lmodBasisProj B (lmodFinSubSetIncl b)) m *: B (lmodFinSubSetIncl b)) == m.
    Definition spanType (B : lmodBasisSetType M) (m : M)
     := {F : lmodFinSubSetType B | spanProp F m}.
    Definition spanning (B : lmodBasisSetType M) :=
      forall m : M, spanType B m.

    Record mixin (T : lmodBasisSetType M) := Mixin {_ : spanning T; }.

    Record class (T : lmodBasisSetType M) := Class {
      base := lmodBasisSet.class_of T;
      mixin_of : mixin T;
    }.

    Record type := Pack {sort : _; class_of : class sort;}.

    Lemma typeIsSpanning (T : type) : spanning (sort T).
    Proof. by destruct (mixin_of (class_of T)). Qed.

  End Def.

  Module Exports.
    Notation spanning := spanning.
    Notation typeIsSpanning := typeIsSpanning.
    Coercion sort : type >-> lmodBasisSetType.
  End Exports.
  Export Exports.

  Section Results.
    Variable (R : ringType) (M : lmodType R) (B : type M).

    Lemma OneLemma (LI : li B) : forall b : B, lmodBasisProj B b (B b) == 1.
    Proof.
      move=>b.
      assert (F := typeIsSpanning B (B b)).
      assert(L := LI _ (fun b' : sval F => if b == (lmodFinSubSetIncl b') then lmodBasisProj B b (B b) - 1 else 0)).
      simpl in L.
      assert((lmodBasisProj B b (B b) - 1) *: B b == 0 *: B b).
      assert((lmodBasisProj B b (B b) - 1) *: B b == 0).
      assert(\big[+%R/0]_b0
      ((if b == lmodFinSubSetIncl (t:=sval F) b0
        then lmodBasisProj B b (B b) - 1
        else 0) *: B (lmodFinSubSetIncl (t:=sval F) b0))
      = (lmodBasisProj B b (B b) - 1) *: B b).
      assert(\big[+%R/0]_b0
        (if (lmodFinSubSetIncl (t:=sval F) b0) == b
          then ((lmodBasisProj B b (B b) - 1) *: B (lmodFinSubSetIncl (t:=sval F) b0))
          else 0)
      = (lmodBasisProj B b (B b) - 1) *: B b).
      assert(\big[+%R/0]_b0
      (if (lmodFinSubSetIncl (t:=sval F) b0) == b
        then ((lmodBasisProj B b (B b) - 1) *: B (lmodFinSubSetIncl (t:=sval F) b0))
        else 0)
      = (lmodBasisProj B b (B b) - 1) *: B b).
      rewrite -big_mkcond=>/=.
    Admitted.
  End Results.


End lmodLocalFinGenSet.
Export lmodLocalFinGenSet.Exports.
*)
Module lmodFinSet.
  Section Def.
    Variable (R : ringType) (M : lmodType R).
    Record class (T : finType) := Class {
      base : lmodSet.mixin M T;
    }.

    Record type := Pack { sort : _; class_of : class sort; }.

    Definition Build {T : finType} (elem : T -> M) (I : injective elem) (ND : non_degenerate elem)
    := Pack (Class (lmodSet.Build I ND)).

    Definition to_set (T : type)
    := lmodSet.Pack (base (class_of T)).

    Definition BuildSelfSubSet (F : type) : lmodFinSubSetType (to_set F)
    := @lmodFinSubSet.Pack _ _ (to_set F) (sort F) id (fun (x1 x2 : (sort F)) => id).
  End Def.

  Module Exports.
    Notation lmodFinSetType := type.
    Notation to_FinType := sort.
    Coercion to_set : type >-> lmodSetType.
  End Exports.
End lmodFinSet.
Export lmodFinSet.Exports.

Module lmodFinBasis.
  Section Def.
    Variable (R : ringType) (M : lmodType R).

    Record class (T : lmodFinSet.type M) := Class {
      li_mixin_of : lmodLISet.mixin T;
      gen_mixin_of : lmodLocalFinGenSet.mixin (lmodBasisSet.Pack base);
    }.

    Record type := Pack { sort : _; class_of : class sort; }.

    Definition Build {T : finType} (elem : T -> M)
      (I : injective elem) (ND : non_degenerate elem)
      (proj : (lmodFinSet.Build I ND) -> {scalar M})
      (span : lmodBasisSet.spanP proj)
      (LI : li (lmodFinSet.to_set (lmodFinSet.Build I ND))) (Sp : spanning (lmodBasisSet.Build span))
    := Pack (Class (lmodLISet.Mixin LI) (lmodLocalFinGenSet.Mixin Sp)).

    Definition to_BasisSet (T : type)
    := lmodBasisSet.Pack (base (class_of T)).
    Definition to_LI (T : type)
    := lmodLISet.Pack (lmodLISet.Class (li_mixin_of (class_of T))).
    Definition to_Gentype (T : type)
    := lmodLocalFinGenSet.Pack (lmodLocalFinGenSet.Class (gen_mixin_of (class_of T))).

    Definition basis_number (B : type) := #|(to_FinType (sort B))|.
  End Def.

  Module Exports.
    Notation basis_number := basis_number.
    Notation lmodFinBasisType := type.
    Coercion to_BasisSet : type >-> lmodBasisSetType.
    Coercion to_LI : type >-> lmodLISet.type.
    Coercion to_Gentype : type >-> lmodLocalFinGenSet.type.
    Coercion class_of : type >-> class.
    Coercion sort : type >-> lmodFinSetType.
  End Exports.
End lmodFinBasis.
Export lmodFinBasis.Exports.

Lemma fin_li (R : ringType) (M : lmodType R) (B : lmodFinSetType M)
 : lmodLISet.li_of (lmodFinSet.BuildSelfSubSet B) -> li B.
Proof. rewrite/li/lmodLISet.li_of
  =>/=H F c H2 b.
Admitted.

Lemma fin_span (R : ringType) (M : lmodType R) (B : lmodFinBasisType M)
 : forall m : M, @lmodLocalFinGenSet.spanProp _ _ B (lmodFinSet.BuildSelfSubSet B) m.
Proof. rewrite/lmodLocalFinGenSet.spanProp=>m.
rewrite/lmodFinSet.BuildSelfSubSet/lmodFinSubSetIncl.
destruct (typeIsSpanning B m) as [F S].
rewrite/lmodLocalFinGenSet.spanProp in S.
Admitted.

From mathcomp Require Import finfun matrix.

Module lmodMatrix.
  Section Def.
  Variable (R : ringType) (M1 : lmodType R) (M2 : lmodType R)
    (B1 : lmodBasisSetType M1) (B2 : lmodBasisSetType M2).

    Definition type := (B1 * B2)%type -> R.
  End Def.
  Module Exports.
    Notation lmodMatrixType := type.
  End Exports.
End lmodMatrix.
Export lmodMatrix.Exports.

Module lmodFinMatrix.
  Section Def.
  Variable (R : ringType) (M1 : lmodType R) (M2 : lmodType R)
    (B1 : lmodFinBasisType M1) (B2 : lmodFinBasisType M2).

    Definition type := {ffun (B1 * B2)%type -> R}.

    Definition to_ssrmatrix (A : type)
      : 'M[R]_(basis_number B1, basis_number B2)
     := \matrix[tt]_(i,j) (A (@enum_val (lmodFinSet.sort (lmodFinBasis.sort B1)) _ i,@enum_val (lmodFinSet.sort (lmodFinBasis.sort B2)) _ j)).

    Definition from_ssrmatrix (A : 'M[R]_(basis_number B1, basis_number B2))
      : type
     := [ffun ij => A (@enum_rank (lmodFinSet.sort (lmodFinBasis.sort B1)) ij.1) (@enum_rank (lmodFinSet.sort (lmodFinBasis.sort B2)) ij.2)].

    Definition to_arb (A : type) : lmodMatrixType B1 B2 := A.
  End Def.
  Module Exports.
    Notation lmodFinMatrixType := type.
    Coercion to_arb : type >-> lmodMatrixType.
  End Exports.
End lmodFinMatrix.
Export lmodFinMatrix.Exports.

Module linExtend.
  Section FiniteDimensional.
    Variable (R : ringType) (M1 : lmodType R) (M2 : lmodType R)
      (B1 : lmodFinBasisType M1) (B2 : lmodFinBasisType M2).
    Section Def.
      Variable (A : lmodFinMatrixType B1 B2).

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
      Variable (A : lmodFinMatrixType B1 B2).

      Lemma one_zero : forall (b1 b2 : B1), lmodBasisProj B1 b1 (B1 b2) = if b1 == b2 then 1%R else 0%R.
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
      Variable (R : ringType) (M1 : lmodType R) (M2 : lmodType R).
        Variable (B1 : lmodBasisSetType M1) (B2 : lmodBasisSetType M2).

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
