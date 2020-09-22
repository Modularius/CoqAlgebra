
Require Import Coq.Program.Tactics.
From Coq.Logic Require Import FunctionalExtensionality ProofIrrelevance.
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

Module lmodOrthoSet.
  Section Def.
    Variable (R : ringType) (M : lmodType R).

    Definition orthonormP (B : lmodSetType M) (proj : B -> {scalar M})
    := forall b1 b2 : B, proj b1 (B b2) = if b1 == b2 then 1 else 0.

    Record mixin (B : lmodSetType M) := Mixin {
      proj : B -> {scalar M};
      orthonormal : orthonormP proj;
    }.

    Record type := Pack { sort : _; class_of : mixin sort; }.

    Definition Build (T : eqType) (elem : T -> M)
      (I : injective elem) (ND : non_degenerate elem)
      (proj : (lmodSet.Build I ND) -> {scalar M})
      (O : orthonormP proj)
    : type := Pack (Mixin O).
  End Def.

  Module Exports.
    Notation lmodOrthoType := type.
    Notation lmodBasisProj := proj.
    Notation orthonormP := orthonormP.
    Coercion sort : type >-> lmodSetType.
    Coercion class_of : type >-> mixin.
  End Exports.
End lmodOrthoSet.
Export lmodOrthoSet.Exports.

Module lmodBasis.
  Section Def.
    Variable (R : ringType) (M : lmodType R).

    Definition basisP (B : lmodSetType M) (proj : B -> {scalar M})
     := forall m1 m2 : M, reflect (forall b : B, proj b m1 = proj b m2) (m1 == m2).


    Record mixin (T : lmodOrthoType M) := Mixin {
      is_basisP : basisP (lmodBasisProj T);
    }.

    Record type := Pack { sort : _; class_of : mixin sort; }.

    Definition Build (T : eqType) (elem : T -> M)
      (I : injective elem) (ND : non_degenerate elem)
      (proj : (lmodSet.Build I ND) -> {scalar M})
      (O : orthonormP proj)
      (B : @basisP (lmodOrthoSet.Build O) proj)
    : type := Pack (Mixin B).
  End Def.

  Module Exports.
    Notation lmodBasisType := type.
    Notation basisP := basisP.
    Coercion class_of : type >-> mixin.
    Coercion sort : type >-> lmodOrthoType.
  End Exports.
End lmodBasis.
Export lmodBasis.Exports.
(*
Module lmodFinSubSet.
  Section Def.
    Variable (R : ringType) (M : lmodType R) (B : lmodSetType M).
    Record type  := Pack { sort : finType; incl : sort -> B; _ : injective incl; }.

    Definition sigmaType (T : type) := {m : M | [exists b, B (@incl T b) == m]}.
    Definition sigmaEnum (T : type) := map (fun b => B (incl b)) (enum (sort T)).
    Definition to_sigma (T : type) := Eval hnf in [subFinType of (seq_sub (sigmaEnum T))].

    Definition Empty : type
     := Pack (fun x y : void_finType =>
      match x as x return
          ((match x return B with end = match y return B with end)
            -> (x = y))
        with end).

    Definition intersection_finType (F1 F2 : type)
     := [subFinType of {f1 : sort F1 | [exists f2 , incl f1 == @incl F2 f2]}].

    Program Definition Intersection (F1 F2 : type) : type
     := @Pack (intersection_finType F1 F2) (fun x => incl (sval x)) _.
    Next Obligation.
     move=>[x Hx] [y Hy]/=.
     destruct F1 as [F1 L1 I1]=>H.
     apply I1 in H; destruct H.
     apply eq_sig_hprop=>//=z; apply proof_irrelevance.
    Qed.

    Definition difference_finType (F1 F2 : type)
     := [subFinType of {f1 : sort F1 | ~~[exists f2 , incl f1 == @incl F2 f2]}].

    Program Definition Difference (F1 F2 : type) : type
     := @Pack (difference_finType F1 F2) (fun x => incl (sval x)) _.
    Next Obligation.
     move=>[x Hx] [y Hy]/=.
     destruct F1 as [F1 L1 I1]=>H.
     apply I1 in H; destruct H.
     apply eq_sig_hprop=>//=z; apply proof_irrelevance.
    Qed.
(*
    Program Definition DisjointUnion (F1 F2 : type) (_ : Intersection F1 F2 = Empty) : type
     := @Pack (sum_finType (sort F1) (sort F2))
         (fun x => match x with inl x' => incl x'|inr x' => incl x' end)
          _.
    Next Obligation.
    move=> x y.
    destruct F1 as [F1 L1 I1].
    destruct F2 as [F2 L2 I2].
    destruct x, y=>H1.
    apply I1 in H1; by destruct H1.

    case H.
    rewrite /Intersection/Empty in H. simpl in H.
    destruct s, s0; simpl in H1; destruct H1.
    assert((exist
    (fun x0 : sort (Pack I1) =>
     ~~ ~~ FiniteQuant.quant0b (T:=sort F2)
       (fun f2 : sort F2 => FiniteQuant.ex (, incl x0 == incl f2) f2)
       ) x i)
            = (exist _ x i0)).
    apply eq_sig_hprop=>//=z; apply proof_irrelevance.
    by destruct H.

    move=>/=H1.
    destruct s as [s Hs]; simpl in H1.
    Admitted.


    Definition Union (F1 F2 : type) : type
     := DisjointUnion .*)
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

    Definition to_set  : lmodSetType M
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
    Notation lmodLISetType := type.
  End Exports.
End lmodLISet.
Export lmodLISet.Exports.
*)
(*
Module lmodBasis.
  Section Def.
    Variable (R : ringType) (M : lmodType R).

    Record class (T : lmodSet.type M) := Class {
      li_mixin_of : lmodLISet.mixin T;
      gen_mixin_of : lmodSpanningSet.mixin T;
    }.

    Record type := Pack { sort : _; class_of : class sort; }.

    Definition Build (T : eqType) (elem : T -> M)
      (I : injective elem) (ND : non_degenerate elem)
      (proj : (lmodSet.Build I ND) -> {scalar M})
      (LI : li (lmodSet.Build I ND))
      (Sp : lmodSpanningSet.spanP proj)
      (Sp1 : lmodSpanningSet.span1 proj)
    := Pack (Class (lmodLISet.Mixin LI) (lmodSpanningSet.Mixin Sp Sp1)).

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


Module lmodLocalFinGenSet.
  Section Def.
    Variable (R : ringType) (M : lmodType R).

    Definition spanProp (B : lmodSetType M) (F : lmodFinSubSetType B) (proj : F -> {scalar M}) (m : M)
     := (\sum_(f : F) proj f m *: B (lmodFinSubSetIncl f)) == m.
    Definition spanProj (B : lmodSetType M) (F : lmodFinSubSetType B) (m : M)
      := exists proj : F -> {scalar M}, spanProp proj m.
    Definition spanSubSet (B : lmodSetType M) (m : M)
     := {F : lmodFinSubSetType B | spanProj F m}.
    Definition spanning (B : lmodSetType M) :=
      forall m : M, spanSubSet B m.

    Record mixin (T : lmodSetType M) := Mixin {_ : spanning T; }.

    Record class (T : lmodOrthoType M) := Class {
      mixin_of : mixin T;
    }.

    Record type := Pack {sort : _; class_of : class sort;}.

    Lemma typeIsLocallySpanning (T : type) : spanning (sort T).
    Proof. by destruct (mixin_of (class_of T)). Qed.
  End Def.

  Module Exports.
    Notation spanning := spanning.
    Notation typeIsSpanning := typeIsLocallySpanning.
    Coercion sort : type >-> lmodOrthoType.
  End Exports.
  Export Exports.

  Section Results.
    Variable (R : ringType) (M : lmodType R) (B : type M).
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

    Section Lemmas.
    Variable (T : type).
    Definition to_set
    := lmodSet.Pack (base (class_of T)).

    Variable (n : nat) (K : n = size (enum (sort T))).
    Definition to_ord
      : sort T -> 'I_n :=
    eq_rect_r (fun n : nat => sort T -> 'I_n) 
      (eq_rect #|sort T| (fun n : nat => sort T -> 'I_n)
        enum_rank (size (enum (sort T))) (cardT (sort T))) K.

    Definition from_ord
      : 'I_n -> sort T :=
    eq_rect_r (fun n : nat => 'I_n -> sort T) 
      (eq_rect #|sort T| (fun n : nat => 'I_n -> sort T)
        enum_val (size (enum (sort T))) (cardT (sort T))) K.

    Lemma tofrom_ordK : cancel to_ord from_ord.
    Proof.
      rewrite/to_ord/from_ord/eq_rect_r/eq_rect.
      destruct (cardT (sort T)), (Logic.eq_sym K)=>x.
      by rewrite enum_rankK.
    Qed.

    Lemma fromto_ordK : cancel from_ord to_ord.
    Proof.
      rewrite/to_ord/from_ord/eq_rect_r/eq_rect.
      destruct (cardT (sort T)), (Logic.eq_sym K)=>x.
      by rewrite enum_valK.
    Qed.
    End Lemmas.
(*
    Definition BuildSelfSubSet (F : type) : lmodFinSubSetType (to_set F)
    := @lmodFinSubSet.Pack _ _ (to_set F) (sort F) id (fun (x1 x2 : (sort F)) => id).*)
  End Def.

  Module Exports.
    Notation lmodFinSetType := type.
    Notation to_FinType := sort.
    Coercion to_set : type >-> lmodSetType.
  End Exports.
End lmodFinSet.
Export lmodFinSet.Exports.
(*
Module lmodFinGenSet.
  Section Def.
    Variable (R : ringType) (M : lmodType R).


    Record mixin (F : lmodFinSetType M) := Mixin {_ : spanning F; }.

    Record class (F : lmodFinSetType M) := Class {
      mixin_of : mixin F;
    }.

    Record type := Pack {sort : _; class_of : class sort;}.

    Lemma typeSpanning (T : type) : spanning (sort T).
    Proof. by destruct (mixin_of (class_of T)). Qed.
  End Def.

  Module Exports.
    Notation lmodFinGenType := type.
    Notation spanning := spanning.
    Notation typeIsSpanning := typeSpanning.
    Coercion sort : type >-> lmodFinSetType.
  End Exports.
  Export Exports.

  Section Results.
    Variable (R : ringType) (M : lmodType R) (B : type M).
  End Results.
End lmodFinGenSet.
Export lmodFinGenSet.Exports.
*)

Module lmodFinBasis.
  Section Def.
    Variable (R : ringType) (M : lmodType R).

    (* Linear Independence Of A Finite Set *)
    Definition li (F : lmodFinSetType M) :=
        forall (c : F -> R), (\sum_(f : F) (c f) *: (F f)) == 0
          -> forall b, c b == 0.
    
    (* Linear Independence Implies All Linear Combinations
      of the Same Element are Equal *)
    Lemma li_coefs_eq (F : lmodFinSetType M)
     : li F -> forall (c1 c2 : F -> R), (\sum_(f : F) (c1 f) *: (F f)) == (\sum_(f : F) (c2 f) *: (F f)) -> c1 = c2.
    Proof. move=> L c1 c2 E.
      rewrite -GRing.subr_eq0 -GRing.sumrB in E.
      assert(\sum_i (c1 i - c2 i) *: F i == 0). {
        apply (rwP eqP) in E.
        rewrite -(rwP eqP) -{2}E.
        apply eq_bigr=>i _; apply GRing.scalerBl.
      }
      apply (functional_extensionality)=>x.
      apply (rwP eqP).
      by rewrite -GRing.subr_eq0 (L _ H x).
    Qed.

    (* The spanning property of a finite set *)
    Definition spanProp (F : lmodFinSetType M) (proj : F -> {scalar M}) (m : M)
     := (\sum_(f : F) proj f m *: F f) == m.
    Definition spanProj (F : lmodFinSetType M) (m : M)
      := {proj : F -> {scalar M} | spanProp proj m}.
    Definition spanning (F : lmodFinSetType M) :=
      forall m : M, spanProj F m.

    Record mixin (T : lmodFinSet.type M) := Mixin {
      li_ax : li T;
      span_ax : spanning T;
    }.

    Record type := Pack { sort : _; class_of : mixin sort; }.

    Definition Build (T : finType) (elem : T -> M)
      (I : injective elem) (ND : non_degenerate elem)
      (LI : li (lmodFinSet.Build I ND))
      (Sp : spanning (lmodFinSet.Build I ND))
    : type := Pack (Mixin LI Sp).

    Definition basis_number (B : type) := #|(to_FinType (sort B))|.

    Lemma typeSpanning (T : type) : spanning (sort T).
    Proof. by destruct (class_of T). Qed.

    Lemma typeLI (T : type) : li (sort T).
    Proof. by destruct (class_of T). Qed.
  End Def.

  Module Exports.
    Notation basis_number := basis_number.
    Notation lmodFinBasisType := type.
    Notation li := li.
    Notation spanning := spanning.
    Notation typeIsSpanning := typeSpanning.
    Notation typeIsLI := typeLI.
    Coercion class_of : type >-> mixin.
    Coercion sort : type >-> lmodFinSetType.
  End Exports.
  Export Exports.

  Section Results.
    Variable (R : ringType) (M : lmodType R) (T : type M).

    Definition coef_fn (t : T) : M -> R
      := fun m => (sval ((span_ax T) m)) t m.
  
    Lemma coef_sca (t : T) : scalar (coef_fn t).
    Proof. rewrite/coef_fn=> r m1 m2/=.
      destruct T as [T' [li sp]]=>/=; simpl in t.
      destruct sp as [c H], sp as [c1 H1], sp as [c2 H2] =>/=.
      rewrite /spanProp in H, H1, H2.
      apply (rwP eqP) in H1; apply (rwP eqP) in H2.
      rewrite -{2}H1 -{2}H2 GRing.scaler_sumr -big_split in H.
      assert(forall i (_ : true),
        (r *: (c1 i m1 *: T' i) + c2 i m2 *: T' i)
          =
          (((r * c1 i m1) + c2 i m2) *: T' i)
      ). move =>i _;
      by rewrite GRing.scalerA GRing.scalerDl.
      rewrite (eq_bigr _ H0) in H.
      by apply (equal_f (li_coefs_eq li H) t).
    Qed.

    Definition coef (t : T) : {scalar M}
      := Linear (coef_sca t).

  Lemma coefP (m : M) : \sum_f coef f m *: T f = m.
  Proof. rewrite/coef=>/=; rewrite/coef_fn.
    destruct (span_ax T m) as [c H]=>/=.
    rewrite /spanProp in H.
    apply (rwP eqP) in H.
    by rewrite H.
  Qed.

  Definition coefAtBase (t : T) : T -> R
    := fun b : T => if b == t then 1 else 0.

  Lemma coefO : orthonormP coef.
  Proof. rewrite/orthonormP=>b1 b2; move: b1.
    apply equal_f.
    apply (li_coefs_eq (li_ax T)).
    destruct (span_ax T (lmodFinSet.base (lmodFinSet.class_of T) b2)) as [c H].
    rewrite /spanProp in H.
    assert(\sum_f (if f == b2 then 1 else 0) *: T f
    = \sum_f (if f == b2 then T f else 0)).
    apply (eq_bigr _). move=> i _.
    case (i == b2); [apply GRing.scale1r|apply GRing.scale0r].
    by rewrite H0 -big_mkcond big_pred1_eq coefP.
  Qed.

  Lemma coefB : lmodBasis.basisP coef.
  Proof. rewrite/coef=>b1 b2.
    apply (iffP idP).
    rewrite -(rwP eqP)=>H.
    by destruct H.

    rewrite /coef_fn=>/= H.
    destruct (span_ax T b1) as [c1 H1],
      (span_ax T b2) as [c2 H2]; simpl in H.
    rewrite /spanProp in H1, H2.
    apply (rwP eqP) in H1; apply (rwP eqP) in H2.
    rewrite -H1 -H2 -(rwP eqP).
    assert(H' : forall b : T, true -> c1 b b1 *: T b = c2 b b2 *: T b).
    move=>b _; by rewrite (H b).
    refine (eq_bigr _ H').
  Qed.

  Definition to_lmodBasis
  := @lmodBasis.Build _ _ _ _ (@typeIsInjective _ _ (sort T)) (@typeIsNonDegenerate _ _ (sort T)) coef coefO coefB.

  End Results.
  Module Exports2.
    Notation lmodFinBasisProj := coef.
  End Exports2.
End lmodFinBasis.
Export lmodFinBasis.Exports.
Export lmodFinBasis.Exports2.

Section Results.
(*
    Variable (R : ringType) (M : lmodType R) (B : lmodBasisType M).

    Lemma ZeroLemma : forall b1 b2 : B, reflect (b1 <> b2) (lmodBasisProj B b1 (B b2) == 0).
    Proof.
      move=>b1 b2.
      apply (iffP idP)=>H.
      rewrite /not=>N.
      rewrite N in H.
      rewrite (lmodSpanningSet.span_one B b2) in H.
      by rewrite GRing.oner_eq0 in H.
      case (b1 == b2) as []eqn:E.
      apply (rwP eqP) in E.
      by destruct E.
      assert(
        false -> lmodBasisProj B b1 (B b2) == 0
      ).
      by [].
      rewrite -E in H0.
      apply H0.
      assert(
        (lmodBasisProj B b1 (B b2) - lmodBasisProj B b1 (B b1)) *: (B b1) == 0
      ).
      assert (A : rwP (lmodSpanningSet.span B (B b1) (B b2))).
      assert(B b == 1 *: B b).
      apply (rwP (lmodSpanningSet.span B (B b) (1 *: (B b)))).
      by rewrite GRing.scale1r.
      assert((lmodBasisProj B b (B b) - 1) *: B b == 0).
      apply (rwP (lmodSpanningSet.span B ((lmodBasisProj B b (B b) - 1) *: B b) 0))=>b1.
      rewrite GRing.linear0 GRing.linearZ.
      rewrite GRing.mulrBl.
      rewrite GRing.scalerBl.
      apply .
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
*)
End Results.
(*
Lemma fin_span (R : ringType) (M : lmodType R) (B : lmodFinBasisType M)
 : forall m : M, @lmodLocalFinGenSet.spanProp _ _ B (lmodFinSet.BuildSelfSubSet B) m.
Proof. rewrite/lmodLocalFinGenSet.spanProp=>m.
rewrite/lmodFinSet.BuildSelfSubSet/lmodFinSubSetIncl.
destruct (typeIsSpanning B m) as [F S].
rewrite/lmodLocalFinGenSet.spanProp in S.
Admitted.
*)
Close Scope ring_scope.
