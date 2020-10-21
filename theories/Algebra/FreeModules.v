(* math-algebra (c) 2020 Dr Daniel Kirk                                       *)
(******************************************************************************)
(* Let R : ringType                                                           *)
(******************************************************************************)
(* freeLmodType R == a record consisting of an lmodType R 'sort' and          *)
(*                   a (lmodBasisType sort)                                   *)
(*                   M : freeLmodType M coerces to its underlying lmodType    *)
(******************************************************************************)
(* Let M : freeLmodType R                                                     *)
(* basis M             == underlying lmodBasisType object of M                *)
(* \freeBasisCoef_(b) x == \basisProj_b^(basis M) x                           *)
(******************************************************************************)
(* fdFreeLmodType R == a record consisting of an lmodType R 'sort' and        *)
(*                     a (lmodFinBasisType sort)                              *)
(*                     M : fdFreeLmodType M coerces to its underlying         *)
(*                     lmodType but not to freeLmodType                       *)
(******************************************************************************)
(* Let M : fdFreeLmodType R                                                   *)
(* fdBasis M             == underlying lmodFinBasisType object of M           *)
(* to_arb M              == converts to underlying lmodBasisType              *)
(* \fdFreeBasisCoef_(b) x == \finBasisProj_b^(fdBasis M) x                    *)
(******************************************************************************)
(*        M1 \foplus M2  == the fdFreeLmodType given by M1 \oplus M2 and      *)
(*                          Pair.basis M1 M2                                  *)
(*                          Pair.basis M1 M2 == finBasisType with index-set   *)
(*                          (fdBasis M1) + (fdBasis M2) and                   *)
(*                          elem x := match x with                            *)
(*                            |inl y => (B1 y, 0)                             *)
(*                            |inr y => (0, B2 y)                             *)
(*                          end                                               *)
(* \fbigoplus_(f in L) I == the fdFreeLmodType given by \bigoplus_(f in L) I  *)
(*                          and Seq.basis I L                                 *)
(*                          Seq.basis I nil has                               *)
(*                            index-set == null_finType                       *)
(*                            elem x    == tt                                 *)
(*                          Seq.basis I a::L has                              *)
(*                            index-set ==                                    *)
(*                              Pair.basis (fdBasis (I a)) (Seq.basis I L)    *)
(*                            elem x    ==  match x with                      *)
(*                                          |inl y => (fdBasis (I a) y, 0)    *)
(*                                          |inr y => (0, Seq.basis I L y)    *)
(*                                          end                               *)
(*       \fbigoplus_F I == equivalent to \fbigoplus_(f : F) I                 *)
(*         \fbigoplus I == equivalent to \fbigoplus_(f : F) I                 *)
(*                         where I : F -> lmodType R                          *)
(******************************************************************************)

Require Import Coq.Program.Tactics.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun seq.
From mathcomp Require Import eqtype choice fintype path bigop finfun matrix.

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

Include GRing.

Open Scope lmod_scope.
(*
  Definitions of the Free and Finite Dimensional Free Module Types
    *)

Module freeLmod.
  Section Def.
    Variable (R : ringType).
    Record mixin (M : lmodType R) := Mixin { basis : lmodBasisType M; }.
    Record type := Pack { sort : _ ;  class_of : mixin sort; }.
    Definition Build {M : lmodType R} (B : lmodBasisType M) := Pack (Mixin B).
  End Def.

  Module Exports.
  Coercion sort : type >-> lmodType.
  Coercion class_of : type >-> mixin.
    Notation freeLmodType := type.
    Notation basis := basis.
    Notation freeLmodPack := Build.
    Notation coef := (fun (R : ringType) (M : type R) b => \basisProj_b^(basis M)).
    Notation "\freeBasisCoef_( b ) x" := (@coef _ _ b x) (at level 36) : lmod_scope.
  End Exports.
End freeLmod.
Export freeLmod.Exports.

(* Finite dimenisonal free modules are compatible with finite direct sums
   That is they can be built-up and have corresponding proj and inj morphisms *)
Module fdFreeLmod.
  Section Def.
    Variable (R : ringType).
    Record mixin (M : lmodType R) := Mixin { fdBasis : lmodFinBasis.type M; }.
    Record type := Pack { sort : _ ;  class_of : mixin sort; }.
    Definition Build {M : lmodType R} (B : lmodFinBasis.type M) := Pack (Mixin B).

    Definition to_arb (F : type) := freeLmod.Build (lmodFinBasis.to_lmodBasis (fdBasis (class_of F))).
  End Def.


  Module Exports.
    Coercion sort : type >-> lmodType.
    Coercion class_of : type >-> mixin.
    Notation fdFreeLmodType := type.
    Notation fdBasis := fdBasis.
    Notation fdFreeLmodPack := Build.

    Notation coef := (fun (R : ringType) (M : type R) b => \finBasisProj_b^(fdBasis M)).
    Notation "\fdFreeBasisCoef_( b ) x" := (@coef _ _ b x) (at level 36) : lmod_scope.
  End Exports.
End fdFreeLmod.
Export fdFreeLmod.Exports.



(*
  Free Module Types of:
    the trivial modules (null basis)
    the ring as a module over itself (unit basis)
    matrix modules over a ring
    polynomial modules over a ring
    *)

Module fdFreeLmodNull.
  Section Def.
    Variable (R : ringType).
    
    Definition nullBasis_fn := fun x : void => match x with end : (lmodZero.type R).

    Lemma null_injective : injective nullBasis_fn.
    Proof. by move=>x; destruct x. Qed.

    Lemma null_nondeg : non_degenerate nullBasis_fn.
    Proof. by move=>x; destruct x. Qed.

    Definition null_set := lmodFinSet.Build null_injective null_nondeg.

    Lemma null_li : li null_set.
    Proof. move=>c H b; case b. Qed.

    Lemma null_sp : spanning null_set.
    Proof. move=>m; rewrite/lmodFinBasis.spanProj;
      refine(exist _ (fun x : null_set => match x with end) _).
      by rewrite /lmodFinBasis.spanProp/nullBasis_fn big_pred0.
    Qed.
    Definition basis := lmodFinBasis.Build null_li null_sp.
  End Def.
  Module Exports.
    Canonical null_fdFreeLmod (R : ringType) := Eval hnf in @fdFreeLmodPack R _ (fdFreeLmodNull.basis R).
  End Exports.
End fdFreeLmodNull.
Export fdFreeLmodNull.Exports.





Module freeRingModule.
  Section Def.
    Variable (R : ringType).
    Definition fn := fun _ : unit_eqType => (GRing.one R) : (ringModType R).
    Lemma fn_injective : injective fn.
      Proof. by move=>x y; destruct x, y. Qed.
    Lemma fn_nondegen : non_degenerate fn.
      Proof. rewrite /fn=>x; apply GRing.oner_neq0. Qed.

    Definition bset := lmodFinSet.Build fn_injective fn_nondegen.

    Lemma bset_li : li bset.
    Proof. move=>/=c H b; move: H.
      rewrite -big_enum big_enum_cond/fn(big_pred1 tt)
      /(GRing.scale _)=>/=;by [rewrite GRing.mulr1; case b|
      rewrite /pred1=>x; case x].
    Qed.

    Lemma bset_spanning : spanning bset.
    Proof. move=>/=x. rewrite /lmodFinBasis.spanProj.
      refine (exist _ (fun _ => linID.map _) _).
      rewrite /lmodFinBasis.spanProp -big_enum big_enum_cond/fn
      (big_pred1 tt) /(scale _); unlock linID.map=>/=;
      by [rewrite GRing.mulr1|rewrite /pred1=>x'; case x'].
    Qed.

    Definition basis : lmodFinBasisType (ringModType R) := lmodFinBasis.Build bset_li bset_spanning.
  End Def.
  Module Exports.
    Canonical unit_fdFreeLmod (R : ringType) := Eval hnf in @fdFreeLmodPack R (ringModType R) (freeRingModule.basis R).
  End Exports.
End freeRingModule.
Export freeRingModule.Exports.

Module freeLmodMatrix.
  Section Def.
    Variable (R : ringType) (m n : nat).
    Definition fn pp := @delta_mx R m n pp.1 pp.2.
    Lemma fn_injective : injective fn.
      Proof. rewrite/fn=>x y; rewrite /delta_mx -matrixP/eqrel=>H.
        assert(H := H y.1 y.2).
        rewrite !mxE !eq_refl in H; simpl in H.
        have: (y.1 == x.1) by 
          case(y.1 == x.1) as []eqn:E=>//; move: H;
          rewrite !E !(rwP eqP) eq_sym oner_eq0.
        have: (y.2 == x.2) by
          case(y.2 == x.2) as []eqn:E=>//; move: H;
          rewrite E andbC !(rwP eqP) eq_sym oner_eq0.
        destruct x, y; rewrite -!(rwP eqP)=>/=H1 H2.
        by rewrite H1 H2.
      Qed.

      Lemma fn_nondegen : non_degenerate fn.
      Proof. rewrite /fn=>x; rewrite /delta_mx -(rwP negP)-(rwP eqP)-matrixP=>H.
        assert(H := H x.1 x.2); move: H.
        by rewrite !mxE !eq_refl (rwP eqP) oner_eq0.
      Qed.

      Definition fn_bset := lmodFinSet.Build fn_injective fn_nondegen.

      Lemma fn_li : li fn_bset.
      Proof. move=>/=c H b.
        case (c b == 0) as []eqn:E=>//.
      move: H=>/=.
      pose(C := \matrix_(i,j) c(i,j) ).
      have H : forall i j, C i j = c(i,j)
      by rewrite/C=>i j; rewrite mxE.
      rewrite (eq_bigr (fun f => C f.1 f.2 *: delta_mx f.1 f.2) _); [|move=>f _; by rewrite H; destruct f].
      rewrite -big_enum enumT (unlock finEnum_unlock).
      rewrite big_allpairs=>/=.
      rewrite big_enum; under eq_bigr do rewrite big_enum=>/=.
      rewrite big_enum_val; under eq_bigr do rewrite big_enum_val=>/=.
      move=>V.

      have: \sum_(i1 < m) \sum_(i2 < n) C i1 i2 *: delta_mx i1 i2 == 0.
      admit.
      rewrite -matrix_sum_delta -(rwP eqP) -matrixP/eqrel=>P.
      assert(PP := P b.1 b.2).
      unfold C in PP.
      rewrite mxE in PP.
      destruct b.
      by rewrite PP mxE eq_refl in E.
      Admitted.
      (*rewrite big_enum; under eq_bigr do rewrite big_enum=>/=.*)

      Definition elemFun_raw : fn_bset -> 'M_(m,n) -> R
      := fun ij => fun A : 'M_(m,n) => A ij.1 ij.2.
      Lemma elemFun_sca (b : fn_bset) : scalar (elemFun_raw b).
      Proof. rewrite/elemFun_raw=>r x y.
        by rewrite mxE mxE. Qed.

      Definition elemFun : fn_bset -> {scalar 'M[R]_(m,n)}
       := fun b => Linear (elemFun_sca b).
      
    Lemma fn_spanning : spanning fn_bset.
    Proof. move=>/=A. rewrite /lmodFinBasis.spanProj.
      refine (exist _ elemFun _).
      by rewrite /lmodFinBasis.spanProp/elemFun/elemFun_raw/fn
      {2}(matrix_sum_delta A) -big_enum enumT (unlock finEnum_unlock) big_allpairs big_enum
      (eq_bigr (fun i : 'I_m => \sum_(j < n) A i j *: delta_mx i j) _)
      =>[|i H]; rewrite -big_enum.
    Qed.

    Definition basis : lmodFinBasisType (matrix_lmodType R m n) := lmodFinBasis.Build fn_li fn_spanning.
  End Def.
  Module Exports.
    Canonical Structure fdFreeLmod_matrix (R : ringType) (m n : nat) := Eval hnf in fdFreeLmodPack (basis R m n).
  End Exports.
End freeLmodMatrix.
Export freeLmodMatrix.Exports.

Section Morphisms.
  Variable (R : ringType).

  Section VectorConversion.
   Variable (M : fdFreeLmodType R) (n : nat) (E : n = size (enum (to_FinType (fdBasis M)))).

    Definition to_row_raw : M -> 'rV[R]_n  := fun x =>
    \row_(i < n)
      \fdFreeBasisCoef_(lmodFinSet.from_ord E i) x.

    Definition from_row_raw : 'rV[R]_n -> M  := fun x =>
      \sum_(b : fdBasis M)
        x (Ordinal (ltn0Sn 0)) (lmodFinSet.to_ord E b) *: (fdBasis M b).

    Lemma from_row_lin : linear from_row_raw.
    Proof. rewrite/from_row_raw=>r x y.
    rewrite scaler_sumr -big_split.
    apply eq_bigr=>i _.
    by rewrite mxE mxE scalerDl scalerA. Qed.

    Lemma to_row_lin : linear to_row_raw.
    Proof. rewrite/to_row_raw=>r x y.
      rewrite -matrixP /eqrel=>i j.
    by rewrite !mxE linearP. Qed.

    Definition from_row := Linear from_row_lin.
    Definition to_row := Linear to_row_lin.
    
    Lemma from_rowK : cancel to_row from_row.
    Proof. simpl; rewrite/from_row_raw/to_row_raw=>x.
      rewrite -{2}(lmodFinBasis.coefP (fdBasis M) x).
      apply eq_bigr=> b _.
      by rewrite mxE lmodFinSet.tofrom_ordK.
    Qed.

    Lemma to_rowK : cancel from_row to_row.
    Proof. simpl; rewrite/from_row_raw/to_row_raw=>x.
      rewrite -matrixP /eqrel=>i j.
      rewrite mxE linear_sum.
      have H : (forall (i0 : fdBasis M) (_ : true),
        (\finBasisProj_(lmodFinSet.from_ord E j)^(fdBasis M))
        ((x (Ordinal (ltn0Sn 0)) (lmodFinSet.to_ord E i0))
        *: (fdBasis M i0)) =
        (if i0 == lmodFinSet.from_ord (T:=fdBasis M) E j
          then x (Ordinal (ltn0Sn 0)) j
          else 0)) by
      move=>i0 _;
      case(i0 == lmodFinSet.from_ord E j) as []eqn:E2;rewrite scalarZ;[
      apply (rwP eqP) in E2;
      by rewrite {1}E2 lmodFinSet.fromto_ordK
      (lmodFinBasis.coefO (lmodFinSet.from_ord E j) i0) E2 eq_refl mulr1 |
      by rewrite (lmodFinBasis.coefO (lmodFinSet.from_ord E j) i0) eq_sym E2 mulr0].
      rewrite (eq_bigr _ H) -big_mkcond big_pred1_eq.
      destruct i.
      by induction m; [rewrite (proof_irrelevance _ (ltn0Sn 0) i) | inversion i].
    Qed.
  End VectorConversion.

  Section MatrixConversion.
    Variable (M N : fdFreeLmodType R)
    (m : nat) (Em : m = size (enum (to_FinType (fdBasis M))))
    (n : nat) (En : n = size (enum (to_FinType (fdBasis N)))).

    Definition to_map (f : {linear M -> N}) : {linear 'rV[R]_m -> 'rV[R]_n}
     := (to_row En) \oLin f \oLin (from_row Em).

    Definition from_map (f : {linear 'rV[R]_m -> 'rV[R]_n}) : {linear M -> N}
      := (from_row En) \oLin f \oLin (to_row Em).

    Lemma from_mapK : cancel to_map from_map.
    Proof. rewrite/from_map/to_map=>/=f.
      rewrite !eq_lin.
      apply functional_extensionality=>x.
      by rewrite -!linCompChain !from_rowK.
    Qed.
    
    Lemma to_mapK : cancel from_map to_map.
    Proof. rewrite/from_map/to_map=>f.
      rewrite !eq_lin.
      apply functional_extensionality=>x.
      by rewrite -!linCompChain !to_rowK.
    Qed.
  End MatrixConversion.
End Morphisms.





(*

  Direct Sums of Free Modules
  
    *)

Module dsFdFreeLmod.
  Module Pair.
    Section Def.
      Variable (R : ringType).
      Variable (M1 M2 : lmodType R) (B1 : lmodFinBasisType M1) (B2 : lmodFinBasisType M2).
      Definition pairBasis_fn : B1 + B2 -> M1 * M2 := 
        fun x => match x with
          |inl y => (B1 y, 0%R)
          |inr y => (0%R, B2 y)
        end.

      Lemma pair_injective : injective pairBasis_fn.
      Proof. move=>x y H; case x as [a1|a1]eqn:E1, y as [a2|a2]eqn:E2; inversion H.
        all:try by rewrite (typeIsInjective H1).
        all:assert (Y := typeIsNonDegenerate a1);
        (rewrite -H1 in Y || rewrite -H2 in Y);
        apply (rwP negP) in Y; by rewrite (eq_refl) in Y.
      Qed.
      
      Lemma pair_nondeg : non_degenerate pairBasis_fn.
      Proof. move=>x; rewrite /pairBasis_fn; apply(rwP negP).
        by case x as [a|a];
        [assert(A := typeIsNonDegenerate a)| assert(A := typeIsNonDegenerate a)];
        apply(rwP negP) in A; contradict A; apply(rwP eqP) in A; inversion A.
      Qed.

      Definition pair_set := lmodFinSet.Build pair_injective pair_nondeg.

      Lemma pair_zero (M N : lmodType R) (F G : finType) (f : F -> M) (g : G -> N) (m : M) (n : N):
        \sum_i (f i, 0)%R + \sum_i (0, g i) == (m,n)
        <-> (\sum_i f i == m /\ \sum_i g i == n).
      Proof. split; [move=> H|move=> [H1 H2]]. {
          have:(\sum_i (dsLmod.Pair.inj1 M N (f i)) + \sum_i (dsLmod.Pair.inj2 M N (g i)) == (m, n))
            by apply H.
          rewrite -!GRing.raddf_sum/dsLmod.Pair.inj1/dsLmod.Pair.inj2/(@add _) =>/=.
          rewrite /add_pair add0r addr0 -(rwP eqP)=>H0;
          by inversion H0.
        } {
          move: H1 H2; rewrite -!(rwP eqP)=>H1 H2.
          have:(\sum_i (dsLmod.Pair.inj1 _ _  (f i)) == (m, @zero N))
            by rewrite -raddf_sum/dsLmod.Pair.inj1 H1.
          have:(\sum_i (dsLmod.Pair.inj2 _ _ (g i)) == (@zero M, n))
            by rewrite -raddf_sum/dsLmod.Pair.inj2 H2=>/=.
          rewrite -!(rwP eqP)=>H H0.
          have:(\sum_i (dsLmod.Pair.inj1 _ _ (f i)) + \sum_i (dsLmod.Pair.inj2 _ _ (g i)) == (m, n))
            by rewrite H H0 {1}/(@add (pair_lmodType M N))=>/=;
            rewrite /add_pair add0r addr0.
          by rewrite /dsLmod.Pair.inj1/dsLmod.Pair.inj2 -(rwP eqP).
        }
      Qed.

      Lemma pair_li : li pair_set.
      Proof.
        move=>c H b.
        move: H; rewrite big_sumType/(scale _)=>/=.
        rewrite (eq_bigr (fun i => (c (inl i) *: B1 i, 0))) =>[|i _]/=.
        rewrite (eq_bigr (fun i => ((0, c (inr i) *: B2 i)))) =>[|j _]/=.
        move=>H.
        apply pair_zero in H as [H1 H2].
        case b as [a|a]eqn:E; [apply (typeIsLI H1 a)|apply (typeIsLI H2 a)].
        all:by rewrite /(scale _)=>/=; rewrite /scale_pair scaler0.
      Qed.

      Definition coefJoin_fn
        (b : pair_set)
        (c1 : B1 -> {scalar M1}) (c2 : B2 -> {scalar M2})
          := fun b m => match b with inl b' => c1 b' m.1|inr b' => c2 b' m.2 end.
      
      Lemma coefJoin_lin
      (b : pair_set)
      (c1 : B1 -> {scalar M1}) (c2 : B2 -> {scalar M2})
        : linear_for *%R (coefJoin_fn b c1 c2 b).
      Proof. rewrite/coefJoin_fn=>r x y.
      case b=>s; by rewrite /add linearP. Qed.
      
      Lemma pair_sp : spanning pair_set.
      Proof. move=> m; rewrite /lmodFinBasis.spanProj.
        destruct (typeIsSpanning B1 m.1) as [p1 H1], (typeIsSpanning B2 m.2) as [p2 H2].
        refine (exist _ (fun p => Linear (@coefJoin_lin p p1 p2)) _).
        rewrite /lmodFinBasis.spanProp big_sumType=>/=.
        rewrite (eq_bigr (fun i => (p1 i m.1 *: B1 i, 0)))=>[|i _]/=.
        rewrite (eq_bigr (fun i => (0, p2 i m.2 *: B2 i)))=>[|i _]/=.
        by rewrite pair_zero.
        all:by rewrite /(scale _)=>/=; rewrite /scale_pair scaler0.
      Qed.

      Definition basis : lmodFinBasisType (pair_lmodType M1 M2) := lmodFinBasis.Build pair_li pair_sp.
    End Def.

    Definition fdFreeLmod (R : ringType) (m1 m2 : fdFreeLmodType R) := fdFreeLmodPack (basis (fdBasis m1) (fdBasis m2)).
    Section Results.
    Variable (R : ringType).
    Variable (M1 M2 : fdFreeLmodType R).
    Definition inj1 : {linear M1 -> fdFreeLmod M1 M2} := dsLmod.Pair.inj1 M1 M2.
    Definition inj2 : {linear M2 -> fdFreeLmod M1 M2} := dsLmod.Pair.inj2 M1 M2.

    Definition proj1 : {linear fdFreeLmod M1 M2 -> M1} := dsLmod.Pair.proj1 M1 M2.
    Definition proj2 : {linear fdFreeLmod M1 M2 -> M2} := dsLmod.Pair.proj2 M1 M2.
    End Results.

    Module Exports.
      Canonical fdFreeLmod.
    End Exports.
  End Pair.
  Export Pair.Exports.

  Module Seq.
    Section Def.
      Variable (R : ringType) (T : eqType) (I : T -> (fdFreeLmodType R)).

      Fixpoint iterSum (L : seq T) : lmodFinBasisType (dsLmod.Seq.DS  (fun x0 : T => I x0) L)
       := match L with
      |nil => fdBasis (null_fdFreeLmod R) : lmodFinBasisType (dsLmod.Seq.DS (fun x : T => I x) [::])
      |a::L' => Pair.basis (fdBasis (I a)) (iterSum L') : lmodFinBasisType (dsLmod.Seq.DS  (fun x0 : T => I x0) (a::L'))
      end.

      Fixpoint fn (L : seq T) : (iterSum L) -> (dsLmod.Seq.DS I L) := 
        match L with
          |nil => fun=> (tt : dsLmod.Seq.DS (fun x : T => I x) [::])
          |a::L' => fun x : iterSum (a::L') => match x with
            |inl y => (fdBasis (I a) y, 0)
            |inr y => (0, @fn L' y) : dsLmod.Seq.DS  (fun x0 : T => I x0) (a::L')
          end
        end.

      Section Seq.
        Variable (L : seq T).
        Lemma fn_injective : injective (@fn L).
        Proof.
          induction L=>x y=>//.
          case x as [a1|a1]eqn:E1, y as [a2|a2]eqn:E2.
          rewrite (rwP eqP) xpair_eqE eq_refl andbT -(rwP eqP)=>H.
          by rewrite (@typeIsInjective _ _ (fdBasis (I a)) _ _ H).
          rewrite (rwP eqP) xpair_eqE -(rwP andP)=>H.
          destruct H as [H _].
          contradict H; rewrite (rwP negP);
          apply (@typeIsNonDegenerate _ _ (fdBasis (I a)) a1).
          rewrite (rwP eqP) xpair_eqE -(rwP andP)=>H.
          destruct H as [H _];
          contradict H; rewrite eq_sym (rwP negP);
          apply (@typeIsNonDegenerate _ _ (fdBasis (I a)) a2).
          rewrite (rwP eqP) xpair_eqE eq_refl andTb -(rwP eqP)=>H.
          by rewrite (IHl _ _ H).
        Qed.
        
        Lemma fn_nondeg : non_degenerate (@fn L).
        Proof.
          induction L=>x//.
          case x as [a1|a1]eqn:E.
          rewrite /fn.
          (have: ~~(fdBasis (I a) a1 == 0)
          by apply (@typeIsNonDegenerate _ _ (fdBasis (I a)) a1))=>/=H.
          rewrite /eq_op -(rwP nandP)=>/=.
          rewrite H eq_refl.
          by left.
          (have: ~~(fn a1 == 0)
          by apply (IHl a1))=>H/=.
          rewrite /eq_op -(rwP nandP)/fn eq_refl H.
          by right.
        Qed.

        Definition bset := lmodFinSet.Build fn_injective fn_nondeg.
      End Seq.

      Section Seq.
        Variable (L : seq T).
        Lemma seq_li : li (bset L).
        Proof.
          induction L=>//.
          move=>c H b.
          rewrite big_sumType in H; simpl in H.
          move:H.
          under eq_bigr do rewrite /(GRing.scale _)=>/=;
          under eq_bigr do rewrite /scale_pair scaler0=>/=;
          rewrite addrC.
          under eq_bigr do rewrite /(GRing.scale _)=>/=;
          under eq_bigr do rewrite /scale_pair scaler0=>/=;
          rewrite addrC Pair.pair_zero. move =>[H1 H2].
          case b as []eqn:E;[ apply (lmodFinBasis.li_ax (fdBasis (I a)) H1 s) | apply (IHl _ H2 s)].
        Qed.

        Lemma seq_sp : spanning (bset L).
        Proof.
          induction L=>m; [apply (fdFreeLmodNull.null_sp m)|].
          destruct (typeIsSpanning (fdBasis (I a)) m.1) as [p1 H1], (IHl m.2) as [p2 H2].

          refine (exist _ (fun p => Linear (Pair.coefJoin_lin  p p1 p2)) _).
          rewrite /lmodFinBasis.spanProp big_sumType=>/=;
          under eq_bigr do rewrite /(GRing.scale _)=>/=;
          under eq_bigr do rewrite /scale_pair scaler0=>/=;
          rewrite addrC;
          under eq_bigr do rewrite /(GRing.scale _)=>/=;
          under eq_bigr do rewrite /scale_pair scaler0=>/=;
          rewrite addrC Pair.pair_zero; split; [apply H1 | apply H2].
        Qed.

        Definition basis : lmodFinBasisType (dsLmod.Seq.DS I L) := lmodFinBasis.Build seq_li seq_sp.
      End Seq.
    End Def.

    Definition fdFreeLmod (R : ringType) (T : eqType) (I : T -> (fdFreeLmodType R)) (L : seq T) := fdFreeLmodPack (basis I L).
    
    Module Exports.
      Canonical fdFreeLmod.
    End Exports.
  End Seq.

  Section Def.
    Variable (R : ringType) (F : finType) (I : F -> (fdFreeLmodType R)).
    Definition type := Seq.fdFreeLmod I (enum F).
  End Def.
  Export Seq.Exports.
End dsFdFreeLmod.

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

Infix "\foplus" := (dsFdFreeLmod.Pair.fdFreeLmod) (at level 36).
Notation "\fbigoplus_ i F" := (dsFdFreeLmod.type (fun i => F)) : lmod_scope.
Notation "\fbigoplus F" := (dsFdFreeLmod.type F) : lmod_scope.
Notation "\fbigoplus_ ( i : t ) F" := (dsFdFreeLmod.type (fun i : t => F)) : lmod_scope.
Notation "\fbigoplus_ ( i 'in' A ) F" := (dsFdFreeLmod.Seq.fdFreeLmod (filter F (fun i => i \in A))) : lmod_scope.


Export dsFdFreeLmod.Pair.Exports.
Export dsFdFreeLmod.Seq.Exports.

Theorem UniversalProperty (R : ringType) (M : fdFreeLmodType R)
    : forall (N : lmodType R) (f : (fdBasis M) -> N), 
      exists (g : {linear M -> N}),
        f = g \o (fdBasis M).
  Proof.
    move=>N f.
    pose (g := fun x => \sum_(b : (fdBasis M)) \fdFreeBasisCoef_(b) x *: f b).
    (have: linear g
    by move=>r x y; rewrite scaler_sumr -big_split;
    apply eq_bigr=>b _;
    rewrite scalerA linearP scalerDl)=>H.
    refine(ex_intro _ (Linear H) _).
    apply functional_extensionality=>x.
    by (have: f x = g (fdBasis M x) by
    rewrite /g (eq_bigr (fun b : fdBasis M => (if b == x then f b else 0)) _);
    [by rewrite -big_mkcond big_pred1_eq|]=>b _;
    rewrite (lmodFinBasis.coefO);
    by case (b == x); [rewrite scale1r|rewrite scale0r])=>G.
  Qed.

Close Scope ring_scope.
Close Scope lmod_scope.
