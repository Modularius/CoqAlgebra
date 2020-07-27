(* math-algebra (c) 2020 Dr Daniel Kirk *)

Require Import Coq.Program.Tactics.
Require Import Coq.Logic.FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun seq.
From mathcomp Require Import eqtype choice fintype path bigop.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool ssrnat.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Require Import Algebras DirectSum Classes Basis Morphism.
Set Implicit Arguments.
Unset Strict Implicit.
Open Scope ring_scope.

Module freeLmod.
  Section Def.
    Variable (R : ringType).
    Record mixin (M : lmodType R) := Mixin { basis : lmodBasisSetType M; }.
    Record type := Pack { sort : _ ;  class_of : mixin sort; }.
    Definition Build {M : lmodType R} (B : lmodBasisSetType M) := Pack (Mixin B).
  End Def.

  Section Results.

  End Results.

  Module Exports.
    Notation freeLmodType := type.
    Notation basis := basis.
    Notation fdFreeLmodPack := Build.
    Coercion sort : type >-> lmodType.
    Coercion class_of : type >-> mixin.
  End Exports.
End freeLmod.
Export freeLmod.Exports.
Module fdFreeLmod.
  Section Def.
    Variable (R : ringType).
    Record mixin (M : lmodType R) := Mixin { basis : lmodFinBasis.type M; }.
    Record type := Pack { sort : _ ;  class_of : mixin sort; }.
    Definition Build {M : lmodType R} (B : lmodFinBasis.type M) := Pack (Mixin B).
  End Def.

  Section Results.

  End Results.

  Module Exports.
    Notation fdFreeLmodType := type.
    Notation basis := basis.
    Notation fdFreeLmodPack := Build.
    Coercion sort : type >-> lmodType.
    Coercion class_of : type >-> mixin.
  End Exports.
End fdFreeLmod.
Export fdFreeLmod.Exports.



Reserved Notation "\fbigoplus_ i F"
  (at level 36, F at level 36, i at level 0,
    right associativity,
          format "'[' \fbigoplus_ i '/ ' F ']'").

Reserved Notation "\fbigoplus F"
  (at level 36, F at level 36,
    right associativity,
          format "'[' \fbigoplus F ']'").

Reserved Notation "\fbigoplus_ ( i <- r ) F"
  (at level 36, F at level 36, i, r at level 50,
          format "'[' \fbigoplus_ ( i <- r ) '/ ' F ']'").

Reserved Notation "\fbigoplus_ ( i : t ) F"
  (at level 36, F at level 36, i at level 50,
          format "'[' \fbigoplus_ ( i : t ) '/ ' F ']'").

Reserved Notation "\fbigoplus_ ( i 'in' A ) F"
  (at level 36, F at level 36, i, A at level 50,
          format "'[' \fbigoplus_ ( i 'in' A ) '/ ' F ']'").


Module fdDSBasis_lmod.
  Section Def.
    Variable (R : ringType).
    Section NullBasis.
      Definition nullBasis_fn := fun x : void => match x with end : (lmodZero.type R).

      Lemma null_injective : injective nullBasis_fn.
      Proof. by move=>x; destruct x. Qed.

      Lemma null_nondeg : non_degenerate nullBasis_fn.
      Proof. by move=>x; destruct x. Qed.

      Definition null_set := lmodFinSet.Build null_injective null_nondeg.
      Lemma null_li : li null_set.
      Proof. apply fin_li.
        move=>c H b; case b.
      Qed.

      Lemma fn_zero_lin : GRing.linear_for *%R (fun _ : (lmodZero.type R) => 0 : R).
      Proof. by move => r x y; rewrite GRing.mulr0 GRing.addr0. Qed. 

      Lemma null_sp : spanning (lmodBasisSet.Build (fun _ : null_set => Linear fn_zero_lin)).
      Proof. move =>m; refine(exist _ (lmodFinSet.BuildSelfSubSet null_set) _).
        rewrite (eq_bigr (fun _ => 0)).
        by rewrite big_pred0; destruct m.
        by move=> i _; case i.
      Qed.

      Definition nullBasis := lmodFinBasis.Build null_li null_sp.
    End NullBasis.
    Definition null_fdFreeLmod := fdFreeLmodPack nullBasis.

    Section PairBasis.
      Variable (M1 M2 : lmodType R) (B1 : lmodFinBasisType M1) (B2 : lmodFinBasisType M2).
      Definition pairBasis_fn : B1 + B2 -> M1 * M2 := 
        fun x => match x with
          |inl y => (B1 y, 0%R)
          |inr y => (0%R, B2 y)
        end.

      Lemma pair_injective : injective pairBasis_fn.
      Proof. move=>x y H; case x as [a1|a1]eqn:E1, y as [a2|a2]eqn:E2; inversion H.
        { by rewrite (typeIsInjective H1). }
        { by assert (Y := typeIsNonDegenerate a1); rewrite -H1 in Y; apply (rwP negP) in Y; rewrite (eq_refl) in Y. }
        { by assert (Y := typeIsNonDegenerate a1); rewrite -H2 in Y; apply (rwP negP) in Y; rewrite (eq_refl) in Y. }
        { by rewrite (typeIsInjective H1). }
      Qed.

      Lemma pair_nondeg : non_degenerate pairBasis_fn.
      Proof. move=>x; rewrite /pairBasis_fn; apply(rwP negP).
        by case x as [a|a];
        [assert(A := typeIsNonDegenerate a)| assert(A := typeIsNonDegenerate a)];
        apply(rwP negP) in A; contradict A; apply(rwP eqP) in A; inversion A.
      Qed.

      Lemma pair_zero (M N : lmodType R) (F G : finType) (f : F -> M) (g : G -> N) (m : M) (n : N):
        \sum_i (f i, 0)%R + \sum_i (0, g i) == (m,n) <-> (\sum_i f i == m /\ \sum_i g i == n).
      Proof. split; [move=> H|move=> [H1 H2]].
        assert(\sum_i (inj1Lin (f i)) + \sum_i (inj2Lin (g i)) == (m, n)).
        by apply H. clear H.
        move: H0; rewrite -!GRing.raddf_sum=>/=.
        rewrite /dsPair.inj1/dsPair.inj2/(@GRing.add (pair_lmodType M N)) =>/=.
        rewrite /add_pair=>/=.
        rewrite GRing.add0r GRing.addr0 -(rwP eqP) => H0.
        by inversion H0.
        move: H1 H2; rewrite -!(rwP eqP)=>H1 H2.
        assert(\sum_i (inj1Lin (f i)) == (m, @GRing.zero N)).
        by rewrite -GRing.raddf_sum/dsPair.inj1 H1.
        assert(\sum_i (inj2Lin (g i)) == (@GRing.zero M, n)).
        rewrite -GRing.raddf_sum=>/=.
        by rewrite /dsPair.inj2 H2.
        move: H H0; rewrite -!(rwP eqP)=>H H0.
        assert(\sum_i (inj1Lin (f i)) + \sum_i (inj2Lin (g i)) == (m, n)).
        rewrite H H0 {1}/(@GRing.add (pair_lmodType M N))=>/=.
        rewrite /add_pair=>/=.
        by rewrite GRing.add0r GRing.addr0.
        move:H3=>/=.
        by rewrite /dsPair.inj1/dsPair.inj2 -(rwP eqP).
      Qed.

      Definition pair_set := lmodFinSet.Build pair_injective pair_nondeg.

      Lemma pair_li : li pair_set.
      Proof. apply fin_li.
        move=>c H b.
        move: H; rewrite big_sumType/(GRing.scale _)=>/=.
        rewrite (eq_bigr (fun i => (c (inl i) *: (lmodFinSet.base (lmodFinSet.class_of _)) i, 0))) =>[|i _]/=.
        rewrite (eq_bigr (fun i => ((0, c (inr i) *: (lmodFinSet.base (lmodFinSet.class_of _)) i)))) =>[|j _]/=.
        move=>H.
        apply pair_zero in H as [H1 H2].
        case b as [a|a]eqn:E.
      Admitted.
(*        [apply (@typeIsLI _ _ B1 (fun a => (c (inl a))) H1 a) | apply (@typeIsLi _ _ B2 (fun a => (c (inr a))) H2 a)].
        by rewrite /(GRing.scale _)=>/=; rewrite /scale_pair=>/=; rewrite GRing.scaler0.
        by rewrite /(GRing.scale _)=>/=; rewrite /scale_pair=>/=; rewrite GRing.scaler0.
      Qed. *)

      Definition coefJoin_fn
        (b : pair_set)
        (c1 : B1 -> {scalar M1}) (c2 : B2 -> {scalar M2})
         := fun b m => match b with inl b' => c1 b' m.1|inr b' => c2 b' m.2 end.
      
      Lemma coefJoin_lin
      (b : pair_set)
      (c1 : B1 -> {scalar M1}) (c2 : B2 -> {scalar M2})
       : linear_for *%R (coefJoin_fn b c1 c2 b).
      Proof. rewrite/coefJoin_fn=>r x y.
      case b=>s;
      rewrite /(@GRing.add (pair_lmodType M1 M2))=>/=;
      by rewrite GRing.linearP. Qed.

      Program Definition pair_subset (F1 : lmodFinSubSetType B1)
      (F2 : lmodFinSubSetType B2) : lmodFinSubSetType pair_set
       := @lmodFinSubSet.Pack _ _ pair_set
       (sum_finType (lmodFinSubSet.sort F1) (lmodFinSubSet.sort F2))
        (fun x => match x with
          | inl x' => inl B2 (lmodFinSubSetIncl x')
          | inr x' => inr B1 (lmodFinSubSetIncl x')
        end) _.
        Next Obligation.
        move=> x y.
        case x, y=>//=;
        destruct F1,F2=>/=H;
        inversion H; move: H1;
        rewrite (rwP eqP); [rewrite (inj_eq i)|rewrite (inj_eq i0)]; rewrite -(rwP eqP)=>H1;
        by rewrite H1.
        Qed.

      Lemma pair_sp : spanning (lmodBasisSet.Build (fun b => Linear (coefJoin_lin b (lmodBasisProj B1) (lmodBasisProj B2)))).
      Proof. move=> m.
        destruct (typeIsSpanning B1 m.1) as [F1 H1], (typeIsSpanning B2 m.2) as [F2 H2].
        refine (exist _ (pair_subset F1 F2) _).
        rewrite big_sumType=>/=.
        rewrite (eq_bigr (fun i => (lmodBasisProj B1 (lmodFinSubSetIncl i) m.1 *: B1 (lmodFinSubSetIncl i), 0)))=>[|i _]/=.
        rewrite (eq_bigr (fun i => (0, lmodBasisProj B2 (lmodFinSubSetIncl i) m.2 *: B2 (lmodFinSubSetIncl i))))=>[|i _]/=.
        by rewrite pair_zero.
        by rewrite /(GRing.scale _)=>/=; rewrite /scale_pair GRing.scaler0.
        by rewrite /(GRing.scale _)=>/=; rewrite /scale_pair GRing.scaler0.
      Qed.

      Definition pairBasis : lmodFinBasisType (pair_lmodType M1 M2) := lmodFinBasis.Build pair_li pair_sp.
    End PairBasis.
    Definition pair_fdFreeLmod (m1 m2 : fdFreeLmodType R) := fdFreeLmodPack (pairBasis (basis m1) (basis m2)).

    Section ListBasis.
      Fixpoint seq_fdFreeLmod (L : seq (fdFreeLmodType R)) : fdFreeLmodType R :=
        match L with
        |nil => null_fdFreeLmod
        |a::l => pair_fdFreeLmod a (seq_fdFreeLmod l)
        end.
    End ListBasis.

    Section TypeBasis.
      Definition finType_fdFreeLmod (F : finType) (I : F -> (fdFreeLmodType R)) :=
        seq_fdFreeLmod (map I (enum F)).
      Lemma is_direct_sum (F : finType) (I : F -> (fdFreeLmodType R)) :
        fdFreeLmod.sort (finType_fdFreeLmod I) = \bigoplus (fun f : F => fdFreeLmod.sort (I f)).
      Proof.
        rewrite /finType_fdFreeLmod/dsLmod.DS.
        by induction (enum F)=>//=; rewrite IHl.
      Qed.
    End TypeBasis.
  End Def.
End fdDSBasis_lmod.

Notation "\fbigoplus_ i F" := (fdDSBasis_lmod.finType_fdFreeLmod (fun i => F)).
Notation "\fbigoplus F" := (fdDSBasis_lmod.finType_fdFreeLmod F).
Notation "\fbigoplus_ ( i : t ) F" := (fdDSBasis_lmod.finType_fdFreeLmod (fun i : t => F)).
Notation "\fbigoplus_ ( i 'in' A ) F" := (fdDSBasis_lmod.seq_fdFreeLmod (filter F (fun i => i \in A))).


Module freeLmodMorphism.
  Section Def.
    Variable (R : ringType) (M1 M2 : fdFreeLmodType R) (f : {linear M1 -> M2}).
    Definition linear_to_matrix : (basis M1) -> (basis M2) -> R
      := fun b1 b2 => lmodBasisProj (basis M2) b2 (f ((basis M1) b1)).
  End Def.
End freeLmodMorphism.


Close Scope ring_scope.

(*
  Section Monoid.
    Variable (R : ringType).

    Section Associative.
      Variable (m1 m2 m3 : fdFreeLmodType R).
      Definition pairIsomA :
      (pair_fdFreeLmod m1 (pair_fdFreeLmod m2 m3))
       -> (pair_fdFreeLmod (pair_fdFreeLmod m1 m2) m3)
        := fun p => ((p.1, p.2.1), p.2.2).
      Definition invPairIsomA : 
      (pair_fdFreeLmod (pair_fdFreeLmod m1 m2) m3)
       -> (pair_fdFreeLmod m1 (pair_fdFreeLmod m2 m3))
       := fun p  => (p.1.1, (p.1.2, p.2)).
      Lemma pairIsomA_lin : linear pairIsomA.
      Proof. rewrite/pairIsomA=>r x y/=.
        by repeat (rewrite !/(GRing.scale _)=>/=; rewrite /scale_pair)=>/=.
      Qed.
    End Associative.

    Section LeftID.
      Variable (m : fdFreeLmodType R).
      Definition pairIsomIl : (pair_fdFreeLmod (nullFdFreeLmod R) m) -> m
       := fun p => p.2.
      Definition invPairIsomIl : m -> (pair_fdFreeLmod (nullFdFreeLmod R) m)
       := fun p : m => (0 : nullFdFreeLmod R,p).
      Lemma pairIsomIl_lin : linear pairIsomIl.
      Proof. by rewrite /pairIsomIl. Qed.
    End LeftID.

    Section RightID.
      Variable (m : fdFreeLmodType R).
      Definition pairIsomIr : (pair_fdFreeLmod m (nullFdFreeLmod R)) -> m
        := fun p => p.1.
      Definition invPairIsomIr : m -> (pair_fdFreeLmod m (nullFdFreeLmod R))
        := fun p : m => (p, 0 : nullFdFreeLmod R).
      Lemma pairIsomIr_lin : linear pairIsomIr.
      Proof. by rewrite /pairIsomIr. Qed.
    End RightID.

    Axiom BasisIrrelevance : forall (m1 m2 : fdFreeLmodType R),
    (m1 = m2) <-> ((fdFreeLmod.sort m1) = (fdFreeLmod.sort m2)).

    Lemma pair_lmodTypeA : associative (@pair_fdFreeLmod R).
    Proof. move => m1 m2 m3.
      rewrite BasisIrrelevance.
      refine (CosetIrrelevance (lmodIsoBuild (@pairIsomA_lin m1 m2 m3) _)).
      refine(@Bijective _ _ _ (@invPairIsomA m1 m2 m3) _  _).
      rewrite /cancel/invPairIsomA/pairIsomA=>x/=;
      by destruct x as [x1 [x21 x22]].
      rewrite /cancel/invPairIsomA/pairIsomA=>x/=;
      by destruct x as [[x11 x12] x2].
    Qed.

    Lemma pair_lmodType_Il : left_id (nullFdFreeLmod R) (@pair_fdFreeLmod R).
    Proof. move => m.
      rewrite BasisIrrelevance.
      refine (CosetIrrelevance (lmodIso.Build (@pairIsomIl_lin m) _)).
      refine(@Bijective _ _ _ (@invPairIsomIl m) _  _).
      rewrite /cancel/invPairIsomIl/pairIsomIl=>x/=;
      by destruct x as [x1 x2]=>/=; case x1.
      by rewrite /cancel/invPairIsomIr/pairIsomIr=>x/=.
    Qed.

    Lemma pair_lmodType_Ir : right_id (nullFdFreeLmod R) (@pair_fdFreeLmod R).
    Proof. move => m.
      rewrite BasisIrrelevance.
      refine (CosetIrrelevance (lmodIso.Build (@pairIsomIr_lin m) _)).
      refine(@Bijective _ _ _ (@invPairIsomIr m) _  _).
      rewrite /cancel/invPairIsomIr/pairIsomIr=>x/=;
      by destruct x as [x1 x2]=>/=; case x2.
      by rewrite /cancel/invPairIsomIr/pairIsomIr=>x/=.
    Qed.
  End Monoid.
*)


(*
  Section ListBasis.
    Fixpoint listBasis (L : list (fdFreeLmodType R))
     := match L with
      |nil => fdFreeLmod.Pack (fdFreeLmod.Mixin nullBasis)
      |a'::L' => fdFreeLmod.Pack (fdFreeLmod.Mixin (
        pairBasis (basis a') (basis (listBasis L'))
        ))
      end.
  End ListBasis.

  Section IdxBasis.
    Variable (F : finType) (I : F -> fdFreeLmodType R).

    Definition type := listBasis (map I (Finite.enum F)).

  End IdxBasis.
  End Def.
  Module Exports.
    Notation fdDSType := type.
  End Exports.
End lmodDSBasis.
Export lmodDSBasis.Exports.*)