(* math-algebra (c) 2020 Dr Daniel Kirk *)

Require Import Coq.Program.Tactics.
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

  Section Results.

  End Results.

  Module Exports.
    Notation freeLmodType := type.
    Notation basis := basis.
    Notation freeLmodPack := Build.
    Coercion sort : type >-> lmodType.
    Coercion class_of : type >-> mixin.
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

  Section Results.

  End Results.

  Section Basis.
    Variable (R : ringType) (M : type R).
    Local Coercion sort : type >-> lmodType.
    Local Coercion class_of : type >-> mixin.

    Definition coef : (fdBasis M) -> {scalar M} := fun b => \finBasisProj_b^(fdBasis M).
  End Basis.

  Module Exports.
    Notation fdFreeLmodType := type.
    Notation fdBasis := fdBasis.
    Notation fdFreeLmodPack := Build.
    Notation "\fdFreeBasisCoef_( b ) x" := (@coef _ _ b x) (at level 36).
    Coercion sort : type >-> lmodType.
    Coercion class_of : type >-> mixin.
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
(*
    Lemma fn_zero_lin : linear_for *%R (fun _ : (lmodZero.type R) => 0 : R).
    Proof. by move => r x y; rewrite mulr0 addr0. Qed.

    Lemma null_orth : orthonormP (B:=null_set) (fun _ : null_set => Linear fn_zero_lin).
    Proof. rewrite/orthonormP=>m1 m2; case m1, m2. Qed.

    Lemma null_basis : lmodBasis.basisP (B:=null_set) (fun _ : null_set => Linear fn_zero_lin).
    Proof. rewrite/lmodBasis.basisP=>m1 m2;
    by apply (iffP idP)=>H//=. Qed.

    Definition null_basis_set := lmodBasis.Build (O := null_orth) null_basis.
*)
    Lemma null_sp : spanning null_set.
    Proof. move=>m; rewrite/lmodFinBasis.spanProj;
      refine(exist _ (fun x : null_set => match x with end) _).
      by rewrite /lmodFinBasis.spanProp/nullBasis_fn big_pred0.
    Qed.
(*
    Lemma li_sp : li null_set.
    Proof. rewrite/li=>c H b/=.
    destruct b. Qed.
*)
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
        Proof. rewrite/fn=>x y; rewrite /delta_mx -matrixP=>H.
        assert(H := H y.1 y.2).
        assert(Gx := @mxE R m n delta_mx_key (fun i j => ((i == x.1) && (j == x.2))%:R)).
        assert(Gy := @mxE R m n delta_mx_key (fun i j => ((i == y.1) && (j == y.2))%:R)).
        rewrite /eqrel (unlock _) in H, Gx, Gy.
        rewrite (Gx y.1 y.2) (Gy y.1 y.2) !eq_refl in H; simpl in H.
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
        assert(H := H x.1 x.2).
        assert(Gx := @mxE R m n delta_mx_key (fun i j => ((i == x.1) && (j == x.2))%:R)).
        rewrite /eqrel (unlock _) in H Gx.
        by move:H; rewrite (Gx x.1 x.2) !eq_refl /(const_mx 0)
        (@mxE R m n const_mx_key (fun i j => 0%:R)) (rwP eqP) oner_eq0.
        Qed.

      Definition fn_bset := lmodFinSet.Build fn_injective fn_nondegen.

      Lemma fn_li : li fn_bset.
      Proof. move=>/=c H b; move: H=>/=.
      rewrite /fn.
      rewrite -big_enum enumT =>/=.
      rewrite (unlock finEnum_unlock)=>/=.
      rewrite {2}(matrix_sum_delta 0).
      rewrite -!big_enum enumT=>/=.
      rewrite (eq_bigr(fun i : ordinal_finType m => 0) _)=>/=.
      rewrite big_allpairs=>/=.
      rewrite big_const_seq.
      have: forall S : seq(ordinal_finType m), iter (count xpredT S) (+%R 0) 0 = 0 by
      move=>t S;
      induction S=>//=;
      rewrite IHS addr0.
      move=>H; rewrite H; clear H.
      case(c b == 0) as []eqn:E=>//.
      destruct b as [[b1 B1] [b2 B2]].
      Admitted.

      Definition elemFun_raw : fn_bset -> 'M_(m,n) -> R
      := fun ij => fun A : 'M_(m,n) => A ij.1 ij.2.
      Lemma elemFun_sca (b : fn_bset) : scalar (elemFun_raw b).
      Proof. rewrite/elemFun_raw=>r x y.
      Admitted.
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
    Canonical Structure fdFreeLmod_matrix (R : ringType) (m n : nat) := Eval hnf in fdFreeLmodPack (freeLmodMatrix.basis R m n).
  End Exports.
End freeLmodMatrix.
Export freeLmodMatrix.Exports.

Section Morphisms.
  Variable (R : ringType).

  Section VectorConversion.
   Variable (M : fdFreeLmodType R)
    (n : nat) (E : n = size (enum (to_FinType (fdBasis M)))).

    Definition to_row_raw : M -> 'rV[R]_n  := fun x =>
    \row_(i < n)
      \fdFreeBasisCoef_(lmodFinSet.from_ord E i) x.

    Definition from_row_raw : 'rV[R]_n -> M  := fun x =>
      \sum_(b : fdBasis M)
        x (Ordinal (ltn0Sn 0)) (lmodFinSet.to_ord E b) *: (fdBasis M b).

    Lemma from_row_lin : linear from_row_raw.
    Proof. rewrite/from_row_raw=>r x y.
    Admitted.
    Lemma to_row_lin : linear to_row_raw.
    Proof. rewrite/to_row_raw=>r x y.
    Admitted.

    Definition from_row := Linear from_row_lin.
    Definition to_row := Linear to_row_lin.
    
    Lemma tofrom_rowK : cancel to_row from_row.
    Proof. simpl; rewrite/from_row_raw/to_row_raw=>x.
    rewrite -{2}(lmodFinBasis.coefP (fdBasis M) x).
    refine (eq_bigr _ _)=> b _.
    rewrite /matrix_of_fun(unlock _)/matrix_of_fun_def.
    Admitted.

    Lemma fromto_rowK : cancel from_row to_row.
    Proof. simpl; rewrite/from_row_raw/to_row_raw=>x.
    Admitted.
  End VectorConversion.

  Section MatrixConversion.
    Variable (M N : fdFreeLmodType R)
    (m : nat) (Em : m = size (enum (to_FinType (fdBasis M))))
    (n : nat) (En : n = size (enum (to_FinType (fdBasis N)))).

    Definition to_map (f : {linear M -> N}) : {linear 'rV[R]_m -> 'rV[R]_n}
     := (to_row En) \oLin f \oLin (from_row Em).

    Definition from_map (f : {linear 'rV[R]_m -> 'rV[R]_n}) : {linear M -> N}
      := (from_row En) \oLin f \oLin (to_row Em).

    Lemma tofrom_mapK : cancel to_map from_map.
    Proof. simpl; rewrite/from_map/to_map=>f/=.
    Admitted.

    Lemma fromto_mapK : cancel from_map to_map.
    Proof. rewrite/from_map/to_map=>f.
    rewrite /linConcat.map -(lock _).
    Admitted.
  End MatrixConversion.
End Morphisms.





(*

  Direct Sums of Free Modules
  
    *)

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

Reserved Notation "\fproj^( I )_ f "
(at level 36, f at level 36, I at level 36,
  format "'[' \fproj^( I )_ f ']'").

Reserved Notation "\finj^( I )_ f "
(at level 36, f at level 36, I at level 36,
  format "'[' \finj^( I )_ f ']'").


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
      Infix "\foplus" := (fdFreeLmod) (at level 36).
      Canonical fdFreeLmod.
    End Exports.
  End Pair.
  Export Pair.Exports.

  Module Seq.
    Section Def.
      Variable (R : ringType) (T : eqType) (I : T -> (fdFreeLmodType R)).

      Fixpoint iterSum (L : seq T) := match L with
      |nil => to_FinType (fdBasis (null_fdFreeLmod R))
      |a::L' => (sum_finType (to_FinType (fdBasis (I a))) (iterSum L'))
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
          induction L=>/=x y H=>//.
        Admitted. (*
        case x as [a1|a1]eqn:E1, y as [a2|a2]eqn:E2; inversion H.
        have: (fdBasis (I a) a1 == fdBasis (I a) a2).
        case (fdBasis (I a) a1 == fdBasis (I a) a2) as []eqn:E=>//.
        rewrite /lmodFinSet.base/lmodFinSet.class_of in H1.
        simpl in H1.
        Check @typeIsInjective _ _ (lmodFinSet.base (lmodFinSet.class_of (fdBasis (I a)))) a1 a2.
        case (fdBasis (I a) a1 == fdBasis (I a) a2).
        admit.
        Check @typeIsNonDegenerate _ _ (fdBasis (I a)) a1.

        Check typeIsInjective H1.
        simpl in H1.
        Check IHL _ _ H1.
        case x as [sx|tx].
        case y as [sy|ty].
        
        case x as [a1|a1]eqn:E1, y as [a2|a2]eqn:E2; inversion H.
          all:try by rewrite (typeIsInjective H1).
          all:assert (Y := typeIsNonDegenerate a1);
          (rewrite -H1 in Y || rewrite -H2 in Y);
          apply (rwP negP) in Y; by rewrite (eq_refl) in Y.
        Qed.*)
        
        Lemma fn_nondeg : non_degenerate (@fn L).
        Proof. Admitted.

        Definition bset := lmodFinSet.Build fn_injective fn_nondeg.

        Lemma seq_li : li bset.
        Proof. Admitted.
  (*
        Definition coefJoin_fn
          (b : bset)
          (c1 : B1 -> {scalar M1}) (c2 : B2 -> {scalar M2})
            := fun b m => match b with inl b' => c1 b' m.1|inr b' => c2 b' m.2 end.
        
        Lemma coefJoin_lin
        (b : pair_set)
        (c1 : B1 -> {scalar M1}) (c2 : B2 -> {scalar M2})
          : linear_for *%R (coefJoin_fn b c1 c2 b).
        Proof. rewrite/coefJoin_fn=>r x y.
        case b=>s; by rewrite /add linearP. Qed.
        *)
        Lemma seq_sp : spanning bset.
        Proof. Admitted. (*move=> m; rewrite /lmodFinBasis.spanProj.
          destruct (typeIsSpanning B1 m.1) as [p1 H1], (typeIsSpanning B2 m.2) as [p2 H2].
          refine (exist _ (fun p => Linear (@coefJoin_lin p p1 p2)) _).
          rewrite /lmodFinBasis.spanProp big_sumType=>/=.
          rewrite (eq_bigr (fun i => (p1 i m.1 *: B1 i, 0)))=>[|i _]/=.
          rewrite (eq_bigr (fun i => (0, p2 i m.2 *: B2 i)))=>[|i _]/=.
          by rewrite pair_zero.
          all:by rewrite /(scale _)=>/=; rewrite /scale_pair scaler0.
        Qed.*)

        Definition basis : lmodFinBasisType (dsLmod.Seq.DS I L) := lmodFinBasis.Build seq_li seq_sp.
      End Seq.
    End Def.

    Definition fdFreeLmod (R : ringType) (T : eqType) (I : T -> (fdFreeLmodType R)) (L : seq T) := fdFreeLmodPack (basis I L).
    (*Section Results.
    Variable (R : ringType).
    Variable (T : eqType) (I : T -> (fdFreeLmodType R)) (L : seq T).
    Variable (n : 'I_(size L)).
    Definition inj : {linear dsLmod.Seq.Nth I L n -> fdFreeLmod I L} := dsLmod.Seq.inj I L.

    Definition proj : {linear fdFreeLmod M1 M2 -> M2} := dsLmod.Pair.proj2 M1 M2.
    End Results.*)

    Module Exports.
      Canonical fdFreeLmod.
    End Exports.
  End Seq.
  Export Seq.Exports.

(*Check fun (R : ringType) (T : eqType) (I : T -> (fdFreeLmodType R)) (L : seq T)
  (x : dsLmod.Seq.DS I L) b => \fdFreeBasisCoef_(b) x.*)
(*
  Module Seq.
    Section Def.
      Variable (R : ringType).
      Fixpoint type (L : seq (fdFreeLmodType R)) : fdFreeLmodType R :=
        match L with
        |nil => null_fdFreeLmod R
        |a::l => a \foplus (type l)
        end.
    End Def.
    Definition fdFreeLmod (R : ringType) (L : seq (fdFreeLmodType R)) := type L.
    (*Definition fdFreeLmod (R : ringType) (L : seq (fdFreeLmodType R))
      := fdFreeLmodPack (fdBasis (type L)).
  Canonical Seq.fdFreeLmod.*)
  End Seq.
*)
  Section Def.
    Variable (R : ringType).
    Variable (F : finType) (I : F -> (fdFreeLmodType R)).
    Definition type := Seq.fdFreeLmod I (enum F).
    (*Lemma is_ds
      : \bigoplus_(f : F)(fun f => fdFreeLmod.sort (I f)) = fdFreeLmod.sort type.
    Proof. rewrite /type/dsLmod.DS.
      by induction (enum F)=>//=; rewrite IHl.
    Qed.

    Definition to_ds_raw : type -> \bigoplus I.
    Proof. move=> x.
    by rewrite is_ds. Defined.

    Lemma to_ds_lin : linear to_ds_raw.
    Proof. rewrite /to_ds_raw/eq_rect_r/eq_rect=>r x y.
      by destruct (Logic.eq_sym is_ds). Qed.
    Definition to_ds := Linear to_ds_lin.

    Definition proj_raw (f : F) (x : type) : I f
    := (\proj_f^(I) \oLin to_ds) x.

    Lemma proj_lin (f : F) : linear (proj_raw f).
    Proof. rewrite/proj_raw=> r x y; by rewrite !GRing.linearPZ. Qed.

    Definition from_ds_raw : \bigoplus I -> type.
    Proof. move=> x. by rewrite is_ds in x. Defined.

    Lemma from_ds_lin : linear from_ds_raw.
    Proof. rewrite /from_ds_raw=>r x y; by destruct (is_ds). Qed.
    Definition from_ds := Linear from_ds_lin.

    Lemma to_from_dsK : cancel from_ds to_ds.
    Proof. simpl; rewrite/cancel/to_ds_raw/from_ds_raw=>x/=; by case (is_ds). Qed.

    Lemma from_to_dsK : cancel to_ds from_ds.
    Proof. simpl; rewrite/cancel/to_ds_raw/from_ds_raw=>x/=; by destruct (is_ds). Qed.

    Definition inj_raw (f : F) (x : I f) : type
    := (from_ds \oLin \inj_f^(I)) x.

    Lemma inj_lin (f : F) : linear (@inj_raw f).
    Proof. rewrite/inj_raw=> r x y; by rewrite !linearPZ. Qed.

    Definition proj (f : F) : {linear type -> I f} := Linear (proj_lin f).
    Definition inj (f : F) : {linear I f -> type} := Linear (@inj_lin f).*)
  End Def.
  Section Split.
  Variable (R : ringType) (F G H : finType) (I : F -> fdFreeLmodType R)
    (F_GH : G + H -> F) (enumB : enum F = map F_GH (enum (sum_finType G H))).

    Definition Jj : G -> F := fun g : G => F_GH (inl g).
    Definition Kk : H -> F := fun h : H => F_GH (inr h).
    Definition J : G -> fdFreeLmodType R := fun g : G => I (Jj g).
    Definition K : H -> fdFreeLmodType R := fun h : H => I (Kk h).
(*
    Definition split : {linear type I -> @fdFreeLmodPack _ (type J \oplus type K) (Pair.basis (fdBasis (type J)) (fdBasis (type K)))}
     := dsLmod.split _ _.*)
     End Split.
  (*
  Section Results.
    Variable (R : ringType) (F : finType) (I : F -> fdFreeLmodType R).

    Lemma proj_injK (f : F) x : proj I f (inj I f x) = x.
    Proof. by simpl; rewrite /proj_raw/inj_raw -linCompChain-linCompChain
    to_from_dsK dsLmod.proj_injK. Qed.

    Lemma proj_inj0 (f f' : F) x : f != f' -> proj I f (inj I f' x) = 0.
    Proof. by simpl; rewrite /proj_raw/inj_raw -linCompChain-linCompChain=>H; by rewrite to_from_dsK dsLmod.proj_inj0. Qed.
  End Results.

  Section Split.
    Variable (R : ringType) (F G H : finType) (I : F -> fdFreeLmodType R)
      (F_GH : G + H -> F) (enumB : enum F = map F_GH (enum (sum_finType G H))).

    Definition oF_to_oGH : ordinal_subType #|F| -> ordinal_subType #|(sum_finType G H)|.
    Proof. by rewrite !cardT enumB size_map. Defined.

    Lemma bij : bijective F_GH. Admitted.

    Definition Jj : G -> F := fun g : G => F_GH (inl g).
    Definition Kk : H -> F := fun h : H => F_GH (inr h).
    Definition J : G -> fdFreeLmodType R := fun g : G => I (Jj g).
    Definition K : H -> fdFreeLmodType R := fun h : H => I (Kk h).

    Definition dsSplit : type I -> pair_lmodType (dsLmod.DS J) (dsLmod.DS K)
     := (@dsLmod.split _ _ _ _ I F_GH) \oLin to_ds I.

    Definition split_raw : type I -> type J \foplus type K
     := fun x => (from_ds J (dsSplit x).1,from_ds K (dsSplit x).2).

    Definition unsplit_raw : type J \foplus type K -> type I
    := fun x => from_ds I (dsLmod.unsplit _ F_GH (to_ds J x.1,to_ds K x.2)).

    Lemma split_lin : linear split_raw.
    Proof. rewrite/split_raw/dsSplit=>r x y.
    by rewrite !linearP. Qed.
    Definition split := Linear split_lin.

    Lemma unsplit_lin : linear unsplit_raw.
    Proof. rewrite/unsplit_raw=>r x y.
    rewrite !linearPZ.
    rewrite -!linearPZ.
    (have: (to_ds J (r *: x.1 + y.1), to_ds K (r *: x.2 + y.2))
     = (r *: (to_ds J x.1, to_ds K x.2) +
     (to_ds J y.1, to_ds K y.2))
    by rewrite !/(scale _) !linearPZ /scale_pair)=>E.
    by rewrite E.
    Qed.
    Definition unsplit := Linear unsplit_lin.
    
    Lemma split_unsplitK : cancel split unsplit.
      Proof. simpl;
        rewrite /unsplit_raw/split_raw/dsSplit=>x.
        (have:forall p1 p2, (p1,p2).1 = p1 by []);
        (have:forall p1 p2, (p1,p2).2 = p2 by [])=> H2 H1.
        rewrite H1 H2 !to_from_dsK -!linCompChain (dsLmod.split_unsplitK bij).
        by rewrite from_to_dsK.
      Qed.

    Lemma unsplit_splitK : cancel unsplit split.
      Proof. simpl;
        rewrite /split_raw/unsplit_raw/dsSplit=>x.
        rewrite  -linCompChain to_from_dsK (dsLmod.unsplit_splitK bij).
        by rewrite !from_to_dsK; destruct x.
      Qed.

  End Split.*)
  Module Exports.
  End Exports.
  End dsFdFreeLmod.
Definition dsFdFreeLmodType (R : ringType) (F : finType) (I : F -> (fdFreeLmodType R)) := dsFdFreeLmod.type I.


Export dsFdFreeLmod.Pair.Exports.
Export dsFdFreeLmod.Seq.Exports.
Export dsFdFreeLmod.Exports.
(*
Notation "\fbigoplus_ i F" := (dsFdFreeLmodType (fun i => F)).
Notation "\fbigoplus F" := (dsFdFreeLmodType F).
Notation "\fbigoplus_ ( i : t ) F" := (dsFdFreeLmodType (fun i : t => F)).
Notation "\fbigoplus_ ( i 'in' A ) F" := (dsFdFreeLmod.Seq.fdFreeLmod (filter F (fun i => i \in A))).
Notation nullBasis := fdFreeLmodNull.basis.
Notation pairBasis := dsFdFreeLmod.Pair.basis.
*)
(*
Check fun (R : ringType) (F G H : finType)
  (I : F -> (fdFreeLmodType R)) (F_GH : G + H -> F)
  (enumB : enum F = map F_GH (enum (sum_finType G H)))
  (x : \bigoplus_(i : F) I) b => \fdFreeBasisCoef_(b) (dsLmod.split I F_GH x).
*)

(*Check fun (R : ringType) => fun M1 M2 : fdFreeLmodType R => fun (x : M1 \oplus M2) (b : _) => \fdFreeBasisProj_(b) x.*)
(*Check fun (R : ringType) (F : finType) (I : F -> (fdFreeLmodType R))
  (x : \bigoplus_(i : F) I) b => \fdFreeBasisCoef_(b) x.

Notation "\fproj^( I )_ f " := (dsFdFreeLmod.proj I f ).
Notation "\finj^( I )_ f " := (dsFdFreeLmod.inj I f ).
Notation "\fproj_ f ^( I )" := (dsFdFreeLmod.proj I f ).
Notation "\finj_ f ^( I )" := (dsFdFreeLmod.inj I f ).
*)


Close Scope ring_scope.