(******************************************************************************)
(**)
(******************************************************************************)
(* Let R : ringType and M : lmodType R                                        *)
(******************************************************************************)
(* R\lmod^n     ==                                                            *)
(* ringIBNType  == a record consisting of a ringType 'sort' and a proof that  *)
(*                 forall n m : nat,                                          *)
(*                  lmodIsomType R\lmod^n R\lmod^m -> n == m                  *)
(*                 R : ringIBN coerces to ringType                            *)
(* Every commutative ring satisfies the IBN condition so (R : comRingType)    *)
(* coerces to ringIBNType via cRingToRingIBN                                  *)
(* cRingToRingIBN R == given R : comRingType, this is a ringIBNType           *)
(******************************************************************************)
(* Let R : ringIBNType, and let M : fdFreeLmodType R                          *) 
(******************************************************************************)
(* steinitz_exchange M == proof that all bases of M have the same size *)
(* invariant_dimension M == proof that all bases of M have the same size *)
(* \dim(M) == the unique basis number of M                *)
(* dim_of_oplus == proof \dim(A \oplus B) = \dim(A) + \dim(B) *)
(* dim_of_bigoplus == proof \dim(\bigoplus_F I) = \sum_(f : F)\dim(I f) *)
(* rank_nullity f == proof that \dim(A) = \dim(\ker(f)) + \dim(\im(f)) *)


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

Require Import Modules Linears DirectSum Basis FreeModules.

Open Scope lmod_scope.

Module ringPower.
  Section Def.
    Variable (R : ringType).

    Variable (n : nat).
    Definition fn := fun j : 'I_n => unit_fdFreeLmod R.

    Definition type := \bigoplus_(j : 'I_n) fn.
  End Def.

  Module Exports.
    Notation lmodRingPower := type.
    Notation "R \lmod^ n" := (matrix_lmodType R 1 n) (*type R n*) (at level 30).
  End Exports.
End ringPower.
Notation "R \lmod^ n" := (matrix_lmodType R 1 n) (*type R n*) (at level 30) : lmod_scope.

Open Scope lmod_scope.
Open Scope ring_scope.
Section Properties.
  Variable (R : ringType) (n m : nat).

  Definition split_fmod
    : {linear R\lmod^(n + m) -> R\lmod^n \oplus R\lmod^m}
    := \colmap(lsubmx_linear R 1 n m, rsubmx_linear R 1 n m).

  Definition row1_raw := fun x : R\lmod^n => row_mx x (0 : 'M_(1,m)).
  Definition row2_raw := fun x : R\lmod^m => row_mx (0 : 'M_(1,n)) x.
  Lemma row1_lin : linear row1_raw.
  Proof. rewrite /row1_raw=>r x y.
  by rewrite scale_row_mx scaler0 add_row_mx addr0. Qed.
  Lemma row2_lin : linear row2_raw.
  Proof. rewrite /row2_raw=>r x y.
  by rewrite scale_row_mx scaler0 add_row_mx addr0. Qed.
  Definition row1 := Linear row1_lin.
  Definition row2 := Linear row2_lin.

  Definition unsplit_fmod
    : {linear R\lmod^n \oplus R\lmod^m -> R\lmod^(n + m)}
    := \rowmap(row1, row2).


  Lemma enumB : enum (ordinal_finType (n + m)) =
    [seq unsplit i | i <- enum (sum_finType (ordinal_finType n) (ordinal_finType m))].
    Proof.
      induction n.
      rewrite !enumT (unlock _)/sum_enum map_cat -!map_comp (unlock _)/unsplit/comp=>/=.
      have H : forall x : 'I_m, rshift 0 x = id x
      by rewrite/rshift=>x; destruct x as [x i];
      rewrite -(proof_irrelevance _ i (rshift_subproof 0 (Ordinal i))).
      by rewrite (eq_map H) map_id.

      move: IHn0.
      rewrite !enumT (unlock _)/sum_enum !map_cat -!map_comp (unlock _)/unsplit/comp=>/=.
      move=> IHn0.

    Admitted.

    Lemma unsplit_fmodK : cancel split_fmod unsplit_fmod.
    Proof. simpl; rewrite/dsLmod.Pair.to_ds_raw/dsLmod.Pair.from_ds_raw=>x/=.
    by rewrite /row1_raw/row2_raw add_row_mx !addr0 !add0r hsubmxK. Qed.
    
    Lemma split_fmodK : cancel unsplit_fmod split_fmod.
    Proof. simpl; rewrite/dsLmod.Pair.to_ds_raw/dsLmod.Pair.from_ds_raw=>x/=.
      rewrite {5}(dsLmod.Pair.inj_proj_sum x); destruct x=>/=.
      by rewrite /row1_raw/row2_raw add_row_mx row_mxKl row_mxKr addr0 add0r.
    Qed.
End Properties.



Open Scope ring_scope.
Module ringIBN.
  Section Def.
    Definition axiom (R : ringType) :=
      forall n m : nat,
        (linIsomType (R\lmod^n) (R\lmod^m)) -> n == m.

    Record mixin (R : ringType) := Mixin { _ : axiom R; }.
    Record type := Pack { sort : _;  class_of : mixin sort; }.
    End Def.

    Section Result.
      Variable (R : comRingType).
      Section Lemmas.
        Variable (n m : nat) (f : {linear R \lmod^m -> R \lmod^n})
        (g : {linear R \lmod^n -> R \lmod^m}) (Inj : cancel f g) (Sur : cancel g f).

        Section Lemmas2.
          Variable (X : m < n).

          (* Given a proof that m < n, we map a vector of
          R\lmod^n to R\lmod^(m + (n - m))
          via the identity *)
          Definition partition_dim_raw : R \lmod^n -> R \lmod^(m + (n - m)).
            rewrite addnBCA=>//.
            by rewrite subnn addn0.
            by rewrite leq_eqVlt X -(rwP orP); right.
          Defined.

          Definition unpartition_dim_raw : R \lmod^(m + (n - m)) -> R \lmod^n.
            rewrite addnBCA=>//.
            by rewrite subnn addn0.
            by rewrite leq_eqVlt X -(rwP orP); right.
          Defined.

          Lemma partition_dim_raw_lin : linear partition_dim_raw.
            rewrite/partition_dim_raw/eq_rect_r/eq_rect=>r x y/=.
            by destruct(Logic.eq_sym _), (Logic.eq_sym _), (Logic.eq_sym _).
          Qed.
          
          Lemma unpartition_dim_lin : linear unpartition_dim_raw.
            rewrite/unpartition_dim_raw/eq_rect_r/eq_rect=>r x y/=.
            by destruct(Logic.eq_sym _), (Logic.eq_sym _), (Logic.eq_sym _).
          Qed.

          Definition partition_dim := Linear partition_dim_raw_lin.
          Definition unpartition_dim := Linear unpartition_dim_lin.

          Lemma unpartition_dimK : cancel partition_dim unpartition_dim.
            Proof. simpl; rewrite /partition_dim_raw/unpartition_dim_raw/eq_rect_r/eq_rect=>x/=.
            by destruct(Logic.eq_sym _), (Logic.eq_sym _), (Logic.eq_sym _).
          Qed.

          Lemma partition_dimK : cancel unpartition_dim partition_dim.
            Proof. simpl; rewrite /partition_dim_raw/unpartition_dim_raw/eq_rect_r/eq_rect=>x/=.
            by destruct(Logic.eq_sym _), (Logic.eq_sym _), (Logic.eq_sym _).
          Qed.


          Definition split_vs :=    (@split_fmod _ m (n - m)) \oLin partition_dim.
          Definition unsplit_vs :=  unpartition_dim \oLin (@unsplit_fmod _ m (n - m) ).


          Lemma unsplit_vsK : cancel split_vs unsplit_vs.
            Proof. by simpl; rewrite /split_vs/unsplit_vs=>x; rewrite -!linCompChain unsplit_fmodK unpartition_dimK.
          Qed.

          Lemma split_vsK : cancel unsplit_vs split_vs.
            by simpl; rewrite /split_vs/unsplit_vs=>x; rewrite -!linCompChain partition_dimK split_fmodK.
          Qed.

          Definition extend_f : {linear R\lmod^n -> R\lmod^n}
           := f \oLin (dsLmod.Pair.proj1 _ _) \oLin split_vs.

          Definition extend_g : {linear R\lmod^n -> R\lmod^n}
           := unsplit_vs \oLin (dsLmod.Pair.inj1 _ (R\lmod^(n - m)) \oLin g).
        
          Lemma extend_fgK : cancel extend_g extend_f.
            by rewrite/extend_f/extend_g=>x; rewrite -!linCompChain (linCompChain partition_dim) (linCompChain _ unpartition_dim) split_vsK Sur.
          Qed.
        End Lemmas2.

        Definition nonsingular (h : {linear R\lmod^n -> R\lmod^n})
        := forall x, h x = 0 -> x = 0.

        Lemma nonsingularE (h : {linear R\lmod^n -> R\lmod^n})
        : nonsingular h -> (forall y, {x : R\lmod^n | h x == y}).
        Proof.
          rewrite/nonsingular=>H y.
        Admitted.
        (*
        Lemma nonsingular_nonzero_det (h : {linear R\lmod^n -> R\lmod^n})
         : nonsingular h -> \det(lin1_mx h) != 0.
        Proof. rewrite/nonsingular-(rwP negP)/not=>H.
          rewrite -(rwP det0P) => N.
          destruct N.
          rewrite mul_rV_lin1 /to_map  in H1.
          by rewrite (H x H1) eq_refl in H0.
          (*have: h (from_row (ringPowerOfSize R n) x) = 0.
          have: from_row (ringPowerOfSize R n) (to_row (M:=R \lmod^ n) (ringPowerOfSize R n)
          (h (from_row (M:=R \lmod^ n) (ringPowerOfSize R n) x))) = 0.
          by rewrite H1 linear0.
          move=>J.
          by rewrite tofrom_rowK in J.
          move=>J.
          assert(J2 := H (from_row (ringPowerOfSize R n) x) J).
          assert(J3 : to_row (ringPowerOfSize R n) (from_row (ringPowerOfSize R n) x) = 0).
          by rewrite J2 linear0.
          rewrite fromto_rowK in J3.
          by rewrite J3 eq_refl in H0.*)
        Qed.

        Definition nonsingular_inverse_raw
        (h : {linear R\lmod^n -> R\lmod^n}) : R\lmod^n -> R\lmod^n
           := fun x => (mulmx x (invmx (lin1_mx h))).
        Lemma nonsingular_inverse_lin (h : {linear R\lmod^n -> R\lmod^n})
          : linear (nonsingular_inverse_raw h).
          Proof. rewrite/nonsingular_inverse_raw=>r x y.
          by rewrite mulmxDl scalemxAl. Qed.
        Definition nonsingular_inverse
        (h : {linear R\lmod^n -> R\lmod^n}) : {linear R\lmod^n -> R\lmod^n}
            := Linear (nonsingular_inverse_lin h).
*)
        Lemma nonsingular_bijective (h : {linear R\lmod^n -> R\lmod^n})
        : nonsingular h -> bijective h.
        Proof.
          move=>N.
          Admitted.
          (*Check mulmx.
          refine(@Bijective _ _ h (nonsingular_inverse h) _ _); simpl.
          rewrite /nonsingular_inverse_raw=>x/=.
        Admitted.*)

        Lemma nonsingular_product (h1 h2 : {linear R\lmod^n -> R\lmod^n})
        : nonsingular (h2 \oLin h1) <-> nonsingular h1 /\ nonsingular h2.
        Proof. split; rewrite/nonsingular=>/=X. {
            split=>x Z. {
              (have: (h2 (h1 x)) = 0 by rewrite Z linear0)=>H.
              rewrite linCompChain in H.
              by apply (X x H).
            }
            (have: nonsingular h1 by
              rewrite/nonsingular=>x0 H;
              (have: h2 (h1 x0) = 0 by rewrite H linear0)=>H2;
              rewrite linCompChain in H2;
              by apply (X x0 H2));
            rewrite/nonsingular=>H.
            destruct (nonsingular_bijective H).
            (have : h2 (h1 (g0 x)) = 0 by rewrite H1)=>H2.
            rewrite linCompChain in H2.
            assert(P := X (g0 x) H2).
            apply (f_equal h1) in P.
            by rewrite H1 linear0 in P.
          }
          move=>x H; destruct X as [X1 X2].
          rewrite -linCompChain in H.
          by apply (X1 x (X2 (h1 x) H)).
        Qed.

      Lemma L1 : ~~(m < n).
      Proof. apply(rwP negP); rewrite/not=>X.
        (have:(0 < n - m) by
          induction n; [inversion X|rewrite subn_gt0])=>H.
        (have: nonsingular ((extend_f X) \oLin (extend_g X)) by move=>x L;
        rewrite -linCompChain (extend_fgK X x) in L).
        rewrite nonsingular_product=>K; destruct K as [_ K2].

        pose(Y2 := unsplit_vs X (dsLmod.Pair.inj2 (R\lmod^m) _ (const_mx (GRing.one R)))).
        (have: extend_f X Y2 = 0 by
          rewrite /extend_f/Y2 -!linCompChain
          partition_dimK Dimension.split_fmodK
          dsLmod.Pair.proj1_inj20 linear0)=>V.

        assert(E := K2 Y2 V).
        apply (f_equal (split_vs X)) in E.
        apply (f_equal (dsLmod.Pair.proj2 _ _)) in E; move: E.
        rewrite /Y2 split_vsK dsLmod.Pair.proj2_inj2K
        !linear0 /(GRing.zero _) -matrixP /eqrel=>E.
        pose (K := E (Ordinal (ltnSn (0%nat))) (Ordinal H)); move:K.
        by rewrite !mxE (rwP eqP) oner_eq0.
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
      rewrite /dsFdFreeLmod.type/dsFdFreeLmod.Seq.fdFreeLmod -big_enum enumT =>/=.
      induction(Finite.enum F); by [
      rewrite /dim/basis_number big_nil card_void|
      rewrite big_cons -IHl -dim_of_DSPair /dsFdFreeLmod.Pair.fdFreeLmod/dsFdFreeLmod.Seq.basis].
    Qed.

(*
    Axiom dim_of_Quot : forall {M : fdFreeLmodType R} (S : subLmodType M),
      dim (fdSubLmod S) + dim (fdQuotLmod S) == dim M.
*)
    Close Scope nat_scope.
  End Theory.

  Module Exports.
    Notation "'\' 'dim' '(' M ')'" := (dim M) (at level 0, format "'\' 'dim' '(' M ')'") : lmod_scope.
  End Exports.
End fdFreeLmodDimension.
Export fdFreeLmodDimension.Exports.
Close Scope ring_scope.
Close Scope lmod_scope.