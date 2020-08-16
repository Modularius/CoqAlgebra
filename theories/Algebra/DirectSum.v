From Coq.Init Require Import Notations Datatypes.
Require Import Coq.Program.Tactics.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun seq.
From mathcomp Require Import eqtype choice fintype bigop generic_quotient tuple finfun.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool ssrnat.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Require Import Algebras Submodule Classes Morphism.
Open Scope ring_scope.
Set Implicit Arguments.
Unset Strict Implicit.

Module dsPair.
  Section Def.
    Variable (R : ringType) (m1 m2 : lmodType R).

    Definition in1 : predPredType (m1*m2) := fun x => x.2 == 0.
    Lemma factor1_subModule : GRing.submod_closed (subLmod.qualSubElem in1).
      Proof. split=>[|r x y]; rewrite qualifE !unfold_in; [by rewrite eq_refl| rewrite -!(rwP eqP)=>/=Hx Hy];
      by rewrite Hx Hy GRing.scaler0 GRing.addr0. Qed.
    Definition sub1 := subLmodPack factor1_subModule.

    Definition in2 : predPredType (m1*m2) := fun x => x.1 == 0.
    Lemma factor2_subModule : GRing.submod_closed (subLmod.qualSubElem in2).
      Proof. split=>[|r x y]; rewrite qualifE !unfold_in; [by rewrite eq_refl| rewrite -!(rwP eqP)=>/=Hx Hy];
      by rewrite Hx Hy GRing.scaler0 GRing.addr0. Qed.
    Definition sub2 := subLmodPack factor1_subModule.

    Definition inj1 := fun x : m1 => (x,GRing.zero m2) : pair_lmodType m1 m2.
    Definition inj2 := fun x : m2 => (GRing.zero m1, x) : pair_lmodType m1 m2.

    Lemma inj1_lin : linear inj1.
    Proof. rewrite /(additive (pair^~0%R))/morphism_2=>r x y.
      rewrite /GRing.scale/GRing.add=>/=.
      by rewrite /add_pair/scale_pair GRing.scaler0 GRing.addr0. Qed.
    Lemma inj2_lin : linear inj2.
    Proof. rewrite /(additive (pair^~0%R))/morphism_2=>r x y.
      rewrite /GRing.scale/GRing.add=>/=.
      by rewrite /add_pair/scale_pair GRing.scaler0 GRing.addr0. Qed.

    Lemma inj1_injective : injective inj1.
    Proof. by move=>x y H; inversion H. Qed.
    Lemma inj2_injective : injective inj2.
    Proof. by move=>x y H; inversion H. Qed.


    Definition proj1 := fun x : pair_lmodType m1 m2 => x.1.
    Definition proj2 := fun x : pair_lmodType m1 m2 => x.2.

    Lemma proj1_lin : linear proj1.
    Proof. by rewrite /morphism_2. Qed.
    Lemma proj2_lin : linear proj2.
    Proof. by rewrite /morphism_2. Qed.

    Lemma proj1_inj1K x : proj1 (inj1 x) = x. Proof. by []. Qed.
    Lemma proj2_inj2K x : proj2 (inj2 x) = x. Proof. by []. Qed.
    Lemma proj1_inj2K x : proj2 (inj1 x) = 0. Proof. by []. Qed.
    Lemma proj2_inj1K x : proj1 (inj2 x) = 0. Proof. by []. Qed.
  End Def.

End dsPair.

Canonical proj1Lin {R : ringType} {m1 m2 : lmodType R}
:= Eval hnf in Linear (@dsPair.proj1_lin R m1 m2).
Canonical proj2Lin {R : ringType} {m1 m2 : lmodType R}
:= Eval hnf in Linear (@dsPair.proj2_lin R m1 m2).

Canonical inj1Lin {R : ringType} {m1 m2 : lmodType R}
:= Eval hnf in Linear (@dsPair.inj1_lin R m1 m2).
Canonical inj2Lin {R : ringType} {m1 m2 : lmodType R}
:= Eval hnf in Linear (@dsPair.inj2_lin R m1 m2).

Notation lmodDSPairType := pair_lmodType.




Module seq_dsLmod.
  Section Def.
    Variable (R : ringType) (T : eqType) (I : T -> lmodType R).
    Definition oI := (fun o => match o with Some t => I t|None => lmodZero.type R end).
    Definition seqnth := (fun L n => oI (seq.nth None (map Some L) n)).

    Fixpoint DS (L : seq T) : lmodType R
    := match L with
      |nil => lmodZero.type R
      |a'::L' => pair_lmodType (I a') (DS L')
    end.

    Fixpoint inj (L : seq T) (n : nat) {struct n} :
      seqnth L n -> DS L
    := match L as LL return seqnth LL n -> DS LL with
      |nil => fun _ => tt
      |a::L' => match n as nn return seqnth (a::L') nn -> DS (a::L') with
        |0    => fun x => @dsPair.inj1 R (I a) (DS L') x
        |S n' => fun x => @dsPair.inj2 R (I a) (DS L') ((@inj L' n') x)
        end
      end.

    Fixpoint proj (L : seq T) (n : nat) {struct n} :
      DS L -> seqnth L n
    := match L as LL return DS LL -> seqnth LL n with
      |nil => match n as nn return lmodZero.type R -> seqnth nil nn with
        |0    => fun _ => tt
        |S n' => fun _ => tt
        end
      |a::L' => match n as nn return DS (a::L') -> seqnth (a::L') nn with
        |0    => fun x => @dsPair.proj1 R (I a) (DS L') x
        |S n' => fun x => (@proj L' n') (@dsPair.proj2 R (I a) (DS L') x)
        end
      end.

    Section Properties.
      Lemma inj_lin (L : seq T) (n : nat) : linear (@inj L n).
      Proof. rewrite /morphism_2.
        move: n; induction L=>//=. {
        induction n=>//=. }{
        move : L IHL; induction n=>//=.
        move=> r x y; apply (GRing.linearP (@inj1Lin R (I a) (DS L))).
        move=> r x y; rewrite -(GRing.linearP (@inj2Lin R (I a) (DS L)))=>/=.
        by rewrite (IHL n)=>/=. }
      Qed.

      Lemma inj_injective
        (L : seq T) (n : nat) : injective (@inj L n).
      Proof.
        move: n.
        induction L=>//=. { induction n; by move=> x y; destruct x, y. }
        move: L IHL.
        induction n; move=> x y H; [
        apply (@dsPair.inj1_injective R _ _ x y H) |
        apply (IHL n x y (@dsPair.inj2_injective R _ _ (@inj L n x) (@inj L n y) H)) ].
      Qed.

      Lemma proj_lin (L : seq T) (n : nat) : linear (@proj L n).
      Proof. rewrite /morphism_2.
        move: n.
        induction L=>//=. {
        induction n=>//=. }{
        move: L IHL; induction n=>//=.
        by move=> r x y; rewrite -(IHL n) (GRing.linearP (@proj2Lin R (I a) (DS L))). }
      Qed.
    End Properties.
  
    Section Results.
      Variable (L : seq T).

      Lemma ord_revP (P : 'I_(size L) -> Prop)
       : (forall (n : 'I_(size L)), P n) <-> (forall (n : 'I_(size L)), P (rev_ord n)).
      Proof. 
        split=>H n.
        destruct n as [n N]; induction n=>//.
        destruct n as [n N]; induction n;
        by rewrite -(rev_ordK (Ordinal N)).
      Qed.
  
      Lemma nthS {a d} {n : nat}
      : seq.nth d (a::L) (S n) = seq.nth d L n.
      Proof. by induction n. Qed.
  
      Lemma inj_cons n a x : @inj (a::L) (S n) x = dsPair.inj2 (I a) (@inj L n x).
      Proof. induction n, L=>//. Qed.
  
      Lemma proj_cons n a x : @proj (a::L) (S n) (dsPair.inj2 (I a) x) = @proj L n x.
      Proof. induction n, L=>//. Qed.
  
      Lemma proj_inj_cons (n : nat) a x
       : @proj (a::L) (S n) (@inj (a::L) (S n) x) = @proj L n (@inj L n x).
       Proof. induction n, L=>//. Qed.
  
      Lemma proj_injK (n : 'I_(size L)) x : @proj L n (@inj L n x) = x.
      Proof.
        induction L=>/=.
        induction n=>//=.
        destruct n as [n N].
        induction n=>//=; simpl in x, IHl, IHn, N.
        rewrite -ltn_predRL in N; simpl in N.
        apply (IHl (Ordinal N) x).
      Qed.
  
  
      Canonical listProjLin (L : seq T) (n : nat)
        := Linear (@proj_lin L n).
  
      Lemma proj_inj0 (n n' : 'I_(size L)) x : (nat_of_ord n) != n' -> @proj L n (@inj L n' x) = 0.
      Proof.
        induction L=>/=.
          induction n=>//=.
        destruct n as [n N], n' as [n' N'].
        simpl in x, IHl, N, N'=>/=H.
        induction n=>/=.
          apply (rwP negP) in H.
          by induction n'=>/=; [contradiction H|].
        induction n'=>/=;[by rewrite GRing.linear0|].
          move: N N'; rewrite -!ltn_predRL=> N N'.
          rewrite eqSS in H.
          by apply (IHl (Ordinal N) (Ordinal N') x H).
      Qed.
  
    End Results.
  End Def.
End seq_dsLmod.
Canonical seqInjLin {R : ringType} {T : eqType} {I : T -> lmodType R} (L : seq T) (n : nat)
    : {linear seq_dsLmod.seqnth I L n ->  seq_dsLmod.DS I L}
:= Linear (@seq_dsLmod.inj_lin R T I L n).

Canonical seqProjLin  {R : ringType} {T : eqType} {I : T -> lmodType R} (L : seq T) (n : nat)
    : {linear seq_dsLmod.DS I L -> seq_dsLmod.seqnth I L n}
:= Linear (@seq_dsLmod.proj_lin R T I L n).

Reserved Notation "\bigoplus_ i F"
(at level 36, F at level 36, i at level 0,
  right associativity,
        format "'[' \bigoplus_ i '/ ' F ']'").

Reserved Notation "\bigoplus F"
(at level 36, F at level 36,
  right associativity,
        format "'[' \bigoplus F ']'").

Reserved Notation "\bigoplus_ ( i : t ) F"
(at level 36, F at level 36, i at level 50,
        format "'[' \bigoplus_ ( i : t ) '/ ' F ']'").

Reserved Notation "\bigoplus_ ( i < n ) F"
(at level 36, F at level 36, i, n at level 50,
        format "'[' \bigoplus_ ( i < n ) F ']'").

Reserved Notation "\bigoplus_ ( i 'in' A ) F"
(at level 36, F at level 36, i, A at level 50,
        format "'[' \bigoplus_ ( i 'in' A ) '/ ' F ']'").

Module dsLmod.
  Section Def.
    Variable (R : ringType) (F : finType) (I : F -> (lmodType R)).

    Definition DS : lmodType R := seq_dsLmod.DS I (enum F).

    Section Components.
      Variable (f : F).

      Lemma cardElt : nat_of_ord (enum_rank f) < size (enum F).
      Proof. rewrite -cardE; apply ltn_ord. Qed.

      Definition DS_ord := Ordinal cardElt.
      Definition DS_nth := seq_dsLmod.seqnth I (enum F) DS_ord.

      Section TypeConversion.
        Lemma nth_If_eq : DS_nth = I f.
        Proof. by rewrite /DS_nth/seq_dsLmod.seqnth/seq_dsLmod.oI
          -codomE nth_codom enum_rankK.
        Qed.
        Lemma If_nth_eq : I f = DS_nth.
        Proof. by rewrite nth_If_eq. Qed.

        Definition nthToIf : DS_nth -> I f
        := (fun fn : DS_nth -> DS_nth => eq_rect_r (fun M : lmodType R => DS_nth -> M) fn If_nth_eq) id.

        Definition nthToIf_lin : linear nthToIf.
        Proof. rewrite /nthToIf/eq_rect_r/eq_rect=>r x y.
          by destruct If_nth_eq. Qed.

        Definition nthToIfLin : {linear DS_nth -> I f}
        := Linear nthToIf_lin.

        Definition IfToNth : I f -> DS_nth
        := (fun fn : DS_nth -> DS_nth => eq_rect_r (fun M : lmodType R => M -> DS_nth) fn If_nth_eq) id.

        Definition IfToNth_lin : linear IfToNth.
        Proof. rewrite /IfToNth/eq_rect_r/eq_rect=>r x y.
          by destruct If_nth_eq. Qed.

        Definition IfToNthLin : {linear I f -> DS_nth}
        := Linear IfToNth_lin.
      End TypeConversion.
    
      Definition proj (x : DS) : I f
      := nthToIfLin (@seq_dsLmod.proj R F I (enum F) DS_ord x).
      
      Lemma proj_lin : linear proj.
      Proof. rewrite/proj=> r x y.
      by rewrite !GRing.linearPZ. Qed.

      Definition projLin : {linear DS -> I f} := Linear proj_lin.

      Definition inj (x : I f) : DS
      := @seq_dsLmod.inj R F I (enum F) DS_ord (IfToNthLin x).

      Lemma inj_lin : linear inj.
      Proof. rewrite/inj=> r x y.
        by rewrite !GRing.linearPZ. Qed.

      Lemma If_nth_K : cancel IfToNth nthToIf.
      Proof. rewrite/IfToNth/nthToIf/eq_rect_r/eq_rect.
        by destruct (Logic.eq_sym If_nth_eq).
      Qed.

      Lemma nth_If_K : cancel nthToIf IfToNth.
      Proof. rewrite/IfToNth/nthToIf/eq_rect_r/eq_rect.
        by destruct (Logic.eq_sym If_nth_eq).
      Qed.
    End Components.

    Section Properties.
      Lemma inj_injective (f : F) : injective (@inj f).
      Proof. move=> x y H.
        pose (A := @seq_dsLmod.inj_injective R F I (enum F) (DS_ord f) _ _ H).
        inversion A.
        assert(nthToIf (IfToNth x) = nthToIf (IfToNth y)).
        by rewrite H1.
        by rewrite !If_nth_K in H0.
      Qed.

      Lemma proj_injK (f : F) x : proj f (inj x) = x.
      Proof. rewrite /proj/inj.
        rewrite seq_dsLmod.proj_injK=>/=.
        by rewrite If_nth_K.
      Qed.

      Lemma proj_inj0 (f f' : F) x : f != f' -> @proj f (@inj f' x) = 0.
      Proof.
        rewrite/proj/inj-(rwP negP)/not=>H.
        case((nat_of_ord (enum_rank f) != enum_rank f')) as []eqn:E.
        by rewrite (@seq_dsLmod.proj_inj0 _ _ _ _ (DS_ord f) (DS_ord f') _ E) GRing.linear0.
        assert (E' := contraFeq (fun B : enum_rank f != enum_rank f' => B) E).
        apply enum_rank_inj in E'.
        rewrite E' eq_refl in H.
        assert (H' := H is_true_true).
        by [].
      Qed.
    End Properties.
  End Def.
End dsLmod.

Canonical projLin (R : ringType) (F : finType) (I : F -> (lmodType R)) (f : F) := Linear (@dsLmod.proj_lin R F I f).
Canonical injLin (R : ringType) (F : finType) (I : F -> (lmodType R)) (f : F) := Linear (@dsLmod.inj_lin R F I f).

Notation "\bigoplus_ i F" := (dsLmod.DS (fun i => F i)).
Notation "\bigoplus F" := (dsLmod.DS F).
Notation "\bigoplus_ ( i : t ) F" := (dsLmod.DS (fun i : t => F i)).
Notation "\bigoplus_ ( i 'in' A ) F" := (seq_dsLmod.DS (filter F (fun i => i \in A))).

Theorem DS_cat_theory (R : ringType) (F : finType)
  (I : F -> (lmodType R))
    : forall (f : forall i : F, {linear \bigoplus I -> (I i)}), 
      exists (g : forall i : F, {linear (I i) -> (I i)}),
        forall i : F, linConcat.map (injLin I i) (f i) = g i.
Proof. move=> fi.
  by refine(ex_intro _ (fun i => linConcat.map (injLin I i) (fi i)) _ ).
Qed.