Require Import Coq.Logic.ProofIrrelevance Coq.Logic.FunctionalExtensionality.
Require Import Coq.Init.Datatypes.
From mathcomp Require Import ssreflect ssrfun eqtype seq fintype finfun bigop matrix.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool ssrnat.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
  From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Set Implicit Arguments.
Unset Strict Implicit.

Require Import FreeModules DirectSum Algebras Basis Morphism Submodule Quotient.

Module ringPower.
  Section Def.
    Variable (R : ringType).

    Section UnitBasis.
      Definition unit_fn := fun _ : unit_eqType => (GRing.one R) : (lmods.ringMod R).
      Lemma unit_injective : injective unit_fn.
        Proof. by move=>x y; destruct x, y. Qed.
      Lemma unit_nondegen : non_degenerate unit_fn.
        Proof. rewrite /unit_fn=>x; apply GRing.oner_neq0. Qed.

      Definition unit_bset := lmodFinSet.Build unit_injective unit_nondegen.

      Lemma unit_li : li unit_bset.
      Proof. move=>/=c H b; move: H.
        rewrite -big_enum big_enum_cond/unit_fn(big_pred1 tt)
        /(GRing.scale _)=>/=;by [rewrite GRing.mulr1; case b|
        rewrite /pred1=>x; case x].
      Qed.

      Lemma unit_spanning : spanning unit_bset.
      Proof. move=>/=x. rewrite /lmodFinBasis.spanProj.
        refine (exist _ (fun _ => linID.map _) _).
        rewrite /lmodFinBasis.spanProp -big_enum big_enum_cond/unit_fn
        (big_pred1 tt) /(scale _); unlock linID.map=>/=;
        by [rewrite GRing.mulr1|rewrite /pred1=>x'; case x'].
      Qed.

      Definition unitBasis : lmodFinBasisType (lmods.ringMod R) := lmodFinBasis.Build unit_li unit_spanning.
      Definition freeRingMod := @fdFreeLmodPack R (lmods.ringMod R) unitBasis.
    End UnitBasis.
    Variable (n : nat).
    Definition fn := fun j : 'I_n => freeRingMod.

    Definition type := \fbigoplus_(j : 'I_n) freeRingMod.
  End Def.

  Module Exports.
    Notation lmodRingPower := type.
    Notation "R \lmod^ n" := (type R n) (at level 30).
  End Exports.
End ringPower.
Export ringPower.Exports.



Section Properties.
  Variable (R : ringType) (n m : nat).

  Local Notation RR := (fun _ => ringPower.freeRingMod R).
  Definition split_vs
    : {linear R\lmod^(n + m) -> R\lmod^n \foplus R\lmod^m}
    := dsFdFreeLmod.split _ unsplit.

  Definition unsplit_vs
    : {linear R\lmod^n \foplus R\lmod^m -> R\lmod^(n + m)}
    := dsFdFreeLmod.unsplit _ unsplit.

  Lemma enumB : enum (ordinal_finType (n + m)) =
    [seq unsplit i | i <- enum (sum_finType (ordinal_finType n) (ordinal_finType m))].
    Proof.
      rewrite !enumT (unlock _)=>/=.
      induction n, m.
      rewrite /sum_enum/ord_enum map_cat (unlock _)/unsplit=>//=.
    Admitted.

    Lemma split_unsplit_vsK : cancel split_vs unsplit_vs.
    Proof. rewrite/split_vs/unsplit_vs=>x.
    apply (dsFdFreeLmod.split_unsplitK enumB). Qed.

    Lemma unsplit_split_vsK : cancel unsplit_vs split_vs.
    Proof. rewrite/split_vs/unsplit_vs=>x.
      by rewrite (dsFdFreeLmod.unsplit_splitK enumB). Qed.
End Properties.

Section Morphisms.
  Variable (R : ringType).

  Lemma R0_nullBasis
   : to_FinType (fdBasis (R \lmod^ 0)) = void_finType.
  Proof. rewrite/lmodRingPower=>/=.
    by rewrite /dsFdFreeLmodType/dsFdFreeLmod.type enumT (unlock _).
  Qed.


  


  Lemma RSn_nullBasis (n : nat)
   : size (enum(to_FinType (fdBasis (R \lmod^(n.+1))))) = size (enum (sum_finType (to_FinType (fdBasis (R \lmod^n))) (adhoc_seq_sub_finType (iota n 1)))).
  Proof.
  rewrite -addn1.
  rewrite!/lmodRingPower!/dsFdFreeLmodType!/dsFdFreeLmod.type=>/=.
  rewrite !enumT !(unlock _)=>/=.
  have : [seq ringPower.freeRingMod R | _ <- ord_enum (n + 1)]
   = [seq ringPower.freeRingMod R | _ <- ord_enum n]
    ++ [seq ringPower.freeRingMod R | _ <- pmap insub (iota n 1)].
  rewrite /ord_enum iota_add add0n pmap_cat map_cat.
  rewrite /(iota n 1).
  Set Printing All.
  rewrite addn1.
  Set Printing All.
  fold ord_enum.
    rewrite /ord_enum.
  Qed.
  Lemma ringPowerOfSize (n : nat) : n = size (enum (to_FinType (fdBasis (R \lmod^ n)))).
  induction n.
  rewrite/lmodRingPower/dsFdFreeLmodType/dsFdFreeLmod.type=>/=.
  by rewrite !enumT !(unlock _).
  rewrite {1}IHn.
  symmetry; rewrite -addn1; symmetry.
  rewrite!/lmodRingPower!/dsFdFreeLmodType!/dsFdFreeLmod.type=>/=.
  rewrite !enumT !(unlock _)=>/=.
  rewrite /ord_enum iota_add add0n pmap_cat map_cat.
  rewrite /(iota n 1)=>/=.
  rewrite /oapp/insub.

  have: (ord_enum (n.+1)) = (Ordinal (ltn0Sn n)) :: (behead (ord_enum (n.+1))).
  clear IHn.
  rewrite /ord_enum=>/=.
  rewrite /oapp/insub/behead.
  destruct idP.
  rewrite /Sub=>/=.
  by rewrite (proof_irrelevance _ (ltn0Sn n) i).
  rewrite /not in n0.
  by contradiction (n0 (ltn0Sn n)).
  move=>J. rewrite J map_cons=>/=.
  rewrite /sum_enum size_cat size_map (unlock _) size_map -add1n=>/=.
  Check behead_map.
  rewrite -behead_map=>/=.
  clear J IHn.
  induction n=>//=.
  rewrite /ord_enum/pmap/iota/oapp/insub.
  destruct idP=>//=.
  Admitted.

  Section MatrixConversion.
    Variable (m n : nat) (f : {linear R\lmod^m -> R\lmod^n}).
    Definition to_matrix
    := \matrix_(i < n, j < m)
            lmodFinBasisProj (T := fdBasis (R\lmod^n))
              (lmodFinSet.from_ord (ringPowerOfSize _) i)
              (f ((fdBasis (R\lmod^m))(lmodFinSet.from_ord (ringPowerOfSize _) j))).
  End MatrixConversion.
  Check to_matrix.

  Section VectorConversion.
    Variable (n : nat) (x : R\lmod^n).
    Definition to_vector :=
      \matrix_(i < n, _ < 1)
        lmodFinBasisProj (T := fdBasis (R\lmod^n))
          (lmodFinSet.from_ord (ringPowerOfSize _) i) x.
  End VectorConversion.
  
  Variable (m n : nat) (f : {linear R\lmod^m -> R\lmod^n}) (x : R\lmod^m) (y : R\lmod^n).
  Lemma matrix_mul_vec : (to_matrix f) *m (to_vector x) = (to_vector (f x)).
  Proof.
    induction m.
    rewrite /mulmx=>/=.
    rewrite (unlock _) /matrix_of_fun=>/=.
  Admitted.

  Lemma linear_map_equiv_to_matrix_mul : f x = y <-> (to_matrix f) *m (to_vector x) = (to_vector y).
  Proof.
    rewrite matrix_mul_vec.
    split=>H. by rewrite H.
    induction n.
    admit.
    rewrite /to_vector in H.
  Admitted.
End Morphisms.



Open Scope ring_scope.
Module ringIBN.
  Infix "\foplus" := (dsFdFreeLmod.Pair.fdFreeLmod) (at level 36).
  Section Def.
    Definition axiom (R : ringType) :=
      forall n m : nat,
        (lmodIsomType (R\lmod^n) (R\lmod^m)) -> n == m.

    Record mixin (R : ringType) := Mixin { _ : axiom R; }.
    Record type := Pack { sort : _;  class_of : mixin sort; }.
    End Def.

    Section Result.
      Variable (R : ringType).
      Section Lemmas.
        Variable (n m : nat) (f : {linear R \lmod^m -> R \lmod^n})
        (g : {linear R \lmod^n -> R \lmod^m}) (Inj : cancel f g) (Sur : cancel g f).

        Section Lemmas2.
          Variable (X : m < n).
          Definition split_dim_raw : R \lmod^n -> R \lmod^(m + (n - m)).
            rewrite addnBCA=>//.
            by rewrite subnn addn0.
            by rewrite leq_eqVlt X -(rwP orP); right.
          Defined.

          Definition unsplit_dim_raw : R \lmod^(m + (n - m)) -> R \lmod^n.
            rewrite addnBCA=>//.
            by rewrite subnn addn0.
            by rewrite leq_eqVlt X -(rwP orP); right.
          Defined.

          Lemma split_dim_lin : linear split_dim_raw.
            rewrite/split_dim_raw/eq_rect_r/eq_rect=>r x y/=.
            by destruct(Logic.eq_sym _), (Logic.eq_sym _), (Logic.eq_sym _).
          Qed.
          
          Lemma unsplit_dim_lin : linear unsplit_dim_raw.
            rewrite/unsplit_dim_raw/eq_rect_r/eq_rect=>r x y/=.
            by destruct(Logic.eq_sym _), (Logic.eq_sym _), (Logic.eq_sym _).
          Qed.

          Definition split_dim := Linear split_dim_lin.
          Definition unsplit_dim := Linear unsplit_dim_lin.

          Definition split_vs :=    (@split_vs _ m (n - m)) \oLin split_dim.
          Definition unsplit_vs :=  unsplit_dim \oLin (@unsplit_vs _ m (n - m) ).

          Lemma split_unsplit_dimK : cancel split_dim unsplit_dim.
            Proof. simpl; rewrite /split_dim_raw/unsplit_dim_raw/eq_rect_r/eq_rect=>x/=.
            by destruct(Logic.eq_sym _), (Logic.eq_sym _), (Logic.eq_sym _).
          Qed.

          Lemma unsplit_split_dimK : cancel unsplit_dim split_dim.
            Proof. simpl; rewrite /split_dim_raw/unsplit_dim_raw/eq_rect_r/eq_rect=>x/=.
            by destruct(Logic.eq_sym _), (Logic.eq_sym _), (Logic.eq_sym _).
          Qed.

          Lemma split_unsplit_vsK : cancel split_vs unsplit_vs.
            Proof. by simpl; rewrite /split_vs/unsplit_vs=>x; rewrite -!linConChain split_unsplit_vsK split_unsplit_dimK.
          Qed.

          Lemma unsplit_split_vsK : cancel unsplit_vs split_vs.
            by simpl; rewrite /split_vs/unsplit_vs=>x; rewrite -!linConChain unsplit_split_dimK unsplit_split_vsK.
          Qed.

          Definition extend_f : {linear R\lmod^n -> R\lmod^n}
           := f \oLin (dsLmod.Pair.proj1 _ _) \oLin split_vs.

          Definition extend_g : {linear R\lmod^n -> R\lmod^n}
           := unsplit_vs \oLin (dsLmod.Pair.inj1 _ (R\lmod^(n - m)) \oLin g).
        
          Lemma extend_fgK : cancel extend_g extend_f.
            by rewrite/extend_f/extend_g=>x; rewrite -!linConChain (linConChain split_dim) (linConChain _ unsplit_dim) unsplit_split_vsK Sur.
          Qed.
        End Lemmas2.

        Definition nonsingular (h : {linear R\lmod^n -> R\lmod^n})
        := forall x, h x = 0 -> x = 0.

        Lemma nonsingular_nonzero_det (h : {linear R\lmod^n -> R\lmod^n})
         : nonsingular h -> \det(to_matrix h) != 0.
        Proof. rewrite/nonsingular-(rwP negP)/not=>H N.

        Lemma nonsingular_bijective (h : {linear R\lmod^n -> R\lmod^n})
        : nonsingular h -> bijective h.
        Proof.
          rewrite/nonsingular=>N.
        Admitted.

        Lemma nonsingular_product (h1 h2 : {linear R\lmod^n -> R\lmod^n})
        : nonsingular (h2 \oLin h1) <-> nonsingular h1 /\ nonsingular h2.
        Proof. split; rewrite/nonsingular=>/=X. {
            split=>x Z. {
              (have: (h2 (h1 x)) = 0 by rewrite Z linear0)=>H.
              rewrite linConChain in H.
              by apply (X x H).
            }
            (have: nonsingular h1 by
              rewrite/nonsingular=>x0 H;
              (have: h2 (h1 x0) = 0 by rewrite H linear0)=>H2;
              rewrite linConChain in H2;
              by apply (X x0 H2));
            rewrite/nonsingular=>H.
            destruct (nonsingular_bijective H).
            (have : h2 (h1 (g0 x)) = 0 by rewrite H1)=>H2.
            rewrite linConChain in H2.
            assert(P := X (g0 x) H2).
            apply (f_equal h1) in P.
            by rewrite H1 linear0 in P.
          }
          move=>x H; destruct X as [X1 X2].
          rewrite -linConChain in H.
          by apply (X1 x (X2 (h1 x) H)).
        Qed.

      Lemma L1 : ~~(m < n).
        apply(rwP negP); rewrite/not=>X.
        (have:(0 < n - m) by
          induction n; [inversion X|rewrite subn_gt0])=>H.
        pose(Y := \finj_(Ordinal H)^(@ringPower.fn R (n - m)) (GRing.one R)).
        pose(Y2 := unsplit_vs X (dsLmod.Pair.inj2 (R\lmod^m) _ Y)).
        (have: nonsingular ((extend_f X) \oLin (extend_g X)) by move=>x L;
        rewrite -linConChain (extend_fgK X x) in L).
        rewrite nonsingular_product=>K; destruct K as [K1 K2].
        (have: extend_f X Y2 = 0 by
          rewrite /extend_f/Y2 -!linConChain/Dimension.split_vs/Dimension.unsplit_vs
          unsplit_split_dimK (dsFdFreeLmod.unsplit_splitK (enumB R _ _));
          rewrite dsLmod.Pair.proj1_inj2K linear0)=>V.
        assert(E := K2 Y2 V).
        apply (f_equal (split_vs X)) in E.
        apply (f_equal (dsLmod.Pair.proj2 _ _)) in E.
        apply (f_equal (\fproj^(_)_(Ordinal H))) in E; move: E.
        by rewrite unsplit_split_vsK dsLmod.Pair.proj2_inj2K
        dsFdFreeLmod.proj_injK !linear0 (rwP eqP) oner_eq0.
      Qed.

      Lemma L2 : ~~(n < m).
        apply(rwP negP); rewrite/not=>X.
        (have:(0 < m - n) by induction n=>//;
          [inversion X; rewrite subn0|rewrite subn_gt0])=>H.
      Admitted.
      End Lemmas.
      End Result.

        Section Def.
        Variable (R : comRingType).
    Lemma cRingIBN : axiom R. Proof.
    move=>n m E.
    assert(A:= L1 (isomlK E) (isomKl E)).
    assert(B:= L2 (isomlK E) (isomKl E)).
    rewrite -leqNgt in A.
    rewrite -leqNgt in B.
    by rewrite eqn_leq -(rwP andP).
    Qed.

    Definition cRingToRingIBN : type
     := Pack (Mixin cRingIBN).
  End Def.

  Module Exports.
    Notation ringIBNType := type.
    Coercion sort : type >-> ringType.
    Coercion class_of : type >-> mixin.
    Notation cRingToRingIBN := cRingToRingIBN.
    Coercion cRingToRingIBN : comRingType >-> type.
  End Exports.
End ringIBN.
Export ringIBN.Exports.

Module fdFreeLmodDimension.
  Section Def.
  Definition dim {R : ringIBNType} (M : fdFreeLmodType R) : nat
    := lmodFinBasis.basis_number (fdBasis M).
  End Def.

  Section Theory.
    Variable (R : ringIBNType).
    Open Scope nat_scope.
    Lemma steinitz_exchange {M : lmodType R}
      (B1 B2 : lmodFinBasisType M) :
      (basis_number B1 <= basis_number B2).
    Proof.
    rewrite /basis_number !cardE.
    rewrite /(enum (to_FinType (lmodFinBasis.sort B1))).
    rewrite /(enum (to_FinType (lmodFinBasis.sort B2))).
    destruct(Finite.enum (to_FinType (lmodFinBasis.sort B1))) as []eqn:E=>//=.
    destruct(Finite.enum (to_FinType (lmodFinBasis.sort B2))) as []eqn:E2=>//=.
    Admitted. (*
    assert (A := fin_span B2 (B1 s)); move: A;
    rewrite /lmodFinGenSet.spanProp
      /lmodFinSet.BuildSelfSubSet/lmodFinSubSetIncl
      -big_enum enumT E2 big_nil -(rwP eqP)=>A.
    assert (D:= @typeIsNonDegenerate _ _ B1 s);
    by move: D; rewrite A eq_refl-(rwP eqP) =>D.
    Admitted.*)
    Theorem invariant_dimension {M : lmodType R}
      (B1 B2 : lmodFinBasisType M) : basis_number B1 == basis_number B2.
    Proof.
    rewrite eqn_leq.
    by rewrite -(rwP andP); split;
      [ apply (steinitz_exchange B1 B2) | apply (steinitz_exchange B2 B1) ].
    Qed.
(*
    Axiom rank_nullity : forall {M N : fdFreeLmodType R} (f : {linear M -> N}),
      (dim (fdSubLmod \image(f))) + (dim (fdSubLmod \ker(f))) == (dim M).
*)
    Lemma dim_of_DSPair : forall (M1 M2 : fdFreeLmodType R),
      dim (M1 \foplus M2) = (dim M1 + dim M2).
    Proof. move=> M1 M2.
      by rewrite /dsFdFreeLmod.Pair.fdFreeLmod/dim/basis_number card_sum.
    Qed.

    Lemma dim_of_DS : forall {F : finType} (I : F -> fdFreeLmodType R),
      dim (\fbigoplus I) = \sum_f (dim (I f)).
    Proof. move => F I.
      rewrite /dsFdFreeLmodType/dsFdFreeLmod.type -big_enum enumT =>/=;
      induction(Finite.enum F); by [
      rewrite /dim/basis_number big_nil card_void|
      rewrite dim_of_DSPair big_cons IHl].
    Qed.

(*
    Axiom dim_of_Quot : forall {M : fdFreeLmodType R} (S : subLmodType M),
      dim (fdSubLmod S) + dim (fdQuotLmod S) == dim M.
*)
    Close Scope nat_scope.
  End Theory.

  Module Exports.
    Notation "'\' 'dim' '(' M ')'" := (dim M) (at level 0, format "'\' 'dim' '(' M ')'").
  End Exports.
End fdFreeLmodDimension.
Export fdFreeLmodDimension.Exports.
Close Scope ring_scope.