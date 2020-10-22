(******************************************************************************)
(**)
(******************************************************************************)
(* Let R : ringType and M : lmodType R                                        *)
(******************************************************************************)
(* lmodSetType M == a record consisting of a type 'sort' a function           *)
(*                'elem' : sort -> M, and proofs of (injective elem)          *)
(*                and (non_degenerate elem).                                  *)
(*                injective elem == forall x y : T, elem x = elem y -> x = y  *)
(*                non_degenerate elem == forall x : T, elem x != 0            *)
(*                S : lmodSetType M coerces to its type T and function elem   *)
(*                so b : S is shorthand for b : (sort S)                      *)
(*                and S b for (elem S) b.                                     *)
(******************************************************************************)
(* Let S : lmodSetType M                                                      *)
(******************************************************************************)
(* typeIsNonDegenerate S == the proof that S is non_degenerate                *)
(* typeIsInjective S == the proof that S  is injective                        *)
(******************************************************************************)
(* lmodOrthoType S == a record consisting of a function                       *)
(*                    'proj' : S -> {scalar M} and a proof of                 *)
(*                    (orthonormP proj)                                       *)
(*                    orthonormP proj == forall b1 b2 : S, proj b1 (S b2)     *)
(*                                         = if b1 == b2 then 1 else 0        *)
(*                    O : lmodOrthoType S coerces to S                        *)
(*                    so b : O and O b work as for lmodSetType                *)
(******************************************************************************)
(* Let O : lmodOrthoType S                                                    *)
(******************************************************************************)
(* orthonormP O     == orthonormP (lmodBasisProj O)                          *)
(* lmodBasisProj O  == the 'proj : O -> {scalar M} function                   *)
(* \basisProj_b^(O) == lmodBasisProj O b : {scalar M}                         *)
(* typeIsNonDegenerate O == the proof that O is non_degenerate                *)
(* typeIsInjective O == the proof that O is injective                         *)
(******************************************************************************)
(* lmodBasisType O == a record consisting of a proof of                       *)
(*                    basisP (lmodBasisProj O)                                *)
(*                    basisP proj == forall m1 m2 : M,                        *)
(*                      reflect (forall b : O, proj b m1 = proj b m2)         *)
(*                              (m1 == m2)                                    *)
(*                    B : lmodBasisType O coerces to O                        *)
(*                    so b : B and B b work as for lmodSetType                *)
(******************************************************************************)
(* Let B : lmodBasisType O                                                    *)
(******************************************************************************)
(* basisP B              == basisP (lmodBasisProj O)                          *)
(* lmodBasisProj B       == the 'proj : B -> {scalar M} function              *)
(* \basisProj_b^(B)      == lmodBasisProj B b : {scalar M}                    *)
(* typeIsNonDegenerate B == the proof that B is non_degenerate                *)
(* typeIsInjective B     == the proof that B is injective                     *)
(******************************************************************************)
(* lmodFinSetType M == a record consisting of a finType 'sort' and the        *)
(*                     mixin of an lmodSetType for type sort.                 *)
(*                     F : lmodBasisType M coerces to an lmodSetType          *)
(*                     so f : F and F f work as for lmodSetType               *)
(*                     However lmodFinSetType does not coerce to a finType    *)
(*                     There is an explicit function for this *)
(******************************************************************************)
(* Let F : lmodFinSetType M                                                   *)
(******************************************************************************)
(* typeIsNonDegenerate F == the proof that F is non_degenerate                *)
(* typeIsInjective F == the proof that F  is injective                        *)
(* to_FinType F == the underlying finType of F                                *)
(******************************************************************************)
(* Note that all F : lmodFinSetType M are bijective to some ordinal type,     *)
(* to establish the bijection we require:                                     *)
(*  1) n : nat                                                                *)
(*  2) and a proof K : n = size (enum (to_FinType F))                         *)
(*  to_ord F f ==     *)
(*  from_ord F f ==     *)
(******************************************************************************)
(* lmodFinBasisType O == a record consisting of a proof of                       *)
(*                    basisP (lmodBasisProj O)                                *)
(*                    basisP proj == forall m1 m2 : M,                        *)
(*                      reflect (forall b : O, proj b m1 = proj b m2)         *)
(*                              (m1 == m2)                                    *)
(*                    B : lmodBasisType O coerces to O                        *)
(*                    so b : B and B b work as for lmodSetType                *)



Require Import Coq.Program.Tactics.
From Coq.Logic Require Import FunctionalExtensionality ProofIrrelevance.
From mathcomp Require Import ssreflect ssrfun eqtype fintype seq bigop.

Require Import Modules Linears.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Open Scope ring_scope.
Set Implicit Arguments.
Unset Strict Implicit.


Reserved Notation "\basisProj_ b ^( B )"
  (at level 36, B at level 36, b at level 0,
    right associativity,
          format "'[' \basisProj_ b '^(' B ) ']'").

Reserved Notation "\finBasisProj_ b ^( B )"
(at level 36, B at level 36, b at level 0,
  right associativity,
        format "'[' \finBasisProj_ b '^(' B ) ']'").

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

    Local Coercion sort : type >-> lmodSetType.
    Local Coercion class_of : type >-> mixin.
    Definition coef (B : type) (b : B) : {scalar M} := @proj B B b.
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

Notation "\basisProj_ b ^( B )" := (@lmodOrthoSet.coef _ _ B b) : lmod_scope.

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
Notation "\finBasisProj_ b ^( B )" := (@lmodFinBasisProj _ _ B b) : lmod_scope.


Section Results.

End Results.

Close Scope ring_scope.
