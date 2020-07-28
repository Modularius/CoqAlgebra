From Coq.Init Require Import Notations Datatypes.
Require Import Coq.Program.Tactics.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun seq.
From mathcomp Require Import eqtype choice fintype bigop generic_quotient tuple finfun.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Require Import Algebras Submodule Classes.
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

    Definition inj1 := fun x : m1 => (x,GRing.zero m2).
    Definition inj2 := fun x : m2 => (GRing.zero m1, x).

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
(*
  Section Monoid.
    Variable (R : ringType).

    Section Associative.
      Variable (m1 m2 m3 : lmodType R).
      Definition pairIsomA := fun p : (pair_lmodType m1 (pair_lmodType m2 m3)) => ((p.1, p.2.1), p.2.2).
      Definition invPairIsomA := fun p : (pair_lmodType (pair_lmodType m1 m2) m3) => (p.1.1, (p.1.2, p.2)).
      Lemma pairIsomA_lin : linear pairIsomA.
      Proof. rewrite/pairIsomA=>r x y/=.
      by repeat (rewrite !/(GRing.scale _)=>/=; rewrite /scale_pair)=>/=.
      Qed.
    End Associative.

    Section LeftID.
      Variable (m : lmodType R).
      Definition pairIsomIl := fun p : (pair_lmodType (lmodZero.type R) m) => p.2.
      Definition invPairIsomIl := fun p : m => (0 : lmodZero.type R,p).
      Lemma pairIsomIl_lin : linear pairIsomIl.
      Proof. by rewrite /pairIsomIl. Qed.
    End LeftID.

    Section RightID.
    Variable (m : lmodType R).
    Definition pairIsomIr := fun p : (pair_lmodType m (lmodZero.type R)) => p.1.
    Definition invPairIsomIr := fun p : m => (p, 0 : lmodZero.type R).
    Lemma pairIsomIr_lin : linear pairIsomIr.
    Proof. by rewrite /pairIsomIr. Qed.
    End RightID.

    Lemma pair_lmodTypeA : associative (@pair_lmodType R).
    Proof. move => m1 m2 m3.
      refine (CosetIrrelevance (lmodIso.Build (@pairIsomA_lin m1 m2 m3) _)).
      refine(@Bijective _ _ _ (@invPairIsomA m1 m2 m3) _  _).
      rewrite /cancel/invPairIsomA/pairIsomA=>x/=;
      by destruct x as [x1 [x21 x22]].
      rewrite /cancel/invPairIsomA/pairIsomA=>x/=;
      by destruct x as [[x11 x12] x2].
    Qed.

    Lemma pair_lmodType_Il : left_id (lmodZero.type R) (@pair_lmodType R).
    Proof. move => m.
      refine (CosetIrrelevance (lmodIso.Build (@pairIsomIl_lin m) _)).
      refine(@Bijective _ _ _ (@invPairIsomIl m) _  _).
      rewrite /cancel/invPairIsomIl/pairIsomIl=>x/=;
      by destruct x as [x1 x2]=>/=; case x1.
      by rewrite /cancel/invPairIsomIr/pairIsomIr=>x/=.
    Qed.

    Lemma pair_lmodType_Ir : right_id (lmodZero.type R) (@pair_lmodType R).
    Proof. move => m.
      refine (CosetIrrelevance (lmodIso.Build (@pairIsomIr_lin m) _)).
      refine(@Bijective _ _ _ (@invPairIsomIr m) _  _).
      rewrite /cancel/invPairIsomIr/pairIsomIr=>x/=;
      by destruct x as [x1 x2]=>/=; case x2.
      by rewrite /cancel/invPairIsomIr/pairIsomIr=>x/=.
    Qed.
  End Monoid.*)
End dsPair.

Canonical proj1Lin {R : ringType} {m1 m2 : lmodType R}
:= Eval hnf in Linear (@dsPair.proj1_lin R m1 m2).
Canonical proj2Lin {R : ringType} {m1 m2 : lmodType R}
:= Eval hnf in Linear (@dsPair.proj2_lin R m1 m2).

Canonical inj1Lin {R : ringType} {m1 m2 : lmodType R}
:= Eval hnf in Linear (@dsPair.inj1_lin R m1 m2).
Canonical inj2Lin {R : ringType} {m1 m2 : lmodType R}
:= Eval hnf in Linear (@dsPair.inj2_lin R m1 m2).
(*
Canonical DSMonoid {R : ringType} := Monoid.Law (@dsPair.pair_lmodTypeA R) (@dsPair.pair_lmodType_Il R) (@dsPair.pair_lmodType_Ir R).
*)
Notation lmodDSPairType := pair_lmodType.


(*
Module dsList.
  Section Def.
    Variable (R : ringType) (F : finType) (m : F -> lmodType R) (f' : F).
    Inductive ds_seq_lmodType (L : seq (lmodType R)) :=
    |ds_seq_nil : (L = nil) -> ds_seq_lmodType L
    |ds_seq_cons : forall (a : lmodType R) (l : seq (lmodType R)),
      (L = a::l)-> a -> ds_seq_lmodType l -> ds_seq_lmodType L.

    Program Fixpoint ds_seq_zero (L : seq (lmodType R)) := match L with
    |nil => @ds_seq_nil _ (erefl nil)
    |a::l => @ds_seq_cons L a l _ 0 (@ds_seq_zero l)
    end.
    Print ds_seq_zero.

    Program Fixpoint ds_seq_neg (L : seq (lmodType R)) := fun x : ds_seq_lmodType
       => match x with
       |ds_seq_nil => @ds_seq_nil _ (erefl nil)
       |ds_seq_cons => ds_seq_cons _ (erefl nil)
       end
    |nil => fun _ => @ds_seq_nil _ _
    |a::l => fun x => @ds_seq_cons L a l _ (-x.1) (@ds_seq_neg l (proj2Lin x))
    end.
    
    Section List.
      Variable (L : seq (lmodType R)).
      Definition ds_seq_zmodMixin (L : seq (lmodType R)) := @ZmodMixin (ds_seq_lmodType L) (ds_seq_zero L) 4.

    End List.
*) (*
    (* This is the type of iterated pairs of elements of a finite list of modules *)
    Fixpoint pair_seq_lmodType (L : seq F) : lmodType R
      := match L with
      |nil => lmodZeroType R
      |a::l => pair_lmodType (m a) (pair_seq_lmodType l)
      end.

    Definition pair_fin_lmodType := pair_seq_lmodType (enum F).
    Fixpoint sum_seq_lmodType_get (L : seq F) : Type
    
    (* This is the type of iterated sums of elements, i.e. disjoint union *)
    Fixpoint sum_seq_lmodType (L : seq F) : Type
      := match L with
      |nil => lmodZeroType R
      |a::l => (m a) + (sum_seq_lmodType l)
      end.

    (* This is the null element of the above *)
    Fixpoint sum_seq_lmodType_null (L : seq F) : sum_seq_lmodType L
      := match L with
      |nil => (0 : lmodZeroType R)
      |a::l => @inr (m a) (sum_seq_lmodType l) (sum_seq_lmodType_null l)
      end.
    
    (* This converts an element of the iterated pairs to an element of the iterated sum *)
    Fixpoint pair_to_sum (L : seq F) : pair_seq_lmodType L -> sum_seq_lmodType L :=
      match L with nil => fun _ => 0
      |f::l => fun x : pair_lmodType (m f) (pair_seq_lmodType l)
        => if f == f' then inl (proj1Lin x) else inr (@pair_to_sum l (proj2Lin x))
      end.

    Fixpoint sum_to_pair (L : seq F) : sum_seq_lmodType L -> pair_seq_lmodType L :=
      match L with nil => fun _ => 0
      |f::l => fun x : (m f) + (sum_seq_lmodType l)
        => match x with
          |inl y => inj1Lin (m2:=pair_seq_lmodType l) y
          |inr Y => inj2Lin (m1:=m f) (sum_to_pair Y)
          end
      end.

    Definition convertTypeFrom (f : F) (e : f == f') : m f' -> m f.
      by apply (rwP eqP) in e; rewrite e. Defined.

    Program Definition testFrom (f : F) (l : seq F) (next : m f' -> (sum_seq_lmodType l)) : m f' -> (m f) + (sum_seq_lmodType l)
     := fun x => match f == f' with
     |true => inl (convertTypeFrom _ x)
     |false => inr (next x)
     end.

    Fixpoint to_sum (L : seq F) : m f' -> sum_seq_lmodType L :=
      match L with nil => fun _ => sum_seq_lmodType_null nil
      |f::l => testFrom f (to_sum l)
      end.

    Definition convertTypeTo (f : F) (e : f == f') : m f -> m f'.
    by apply (rwP eqP) in e; rewrite e. Defined. (* not needed *)

    Program Fixpoint from_sum (L : seq F) : sum_seq_lmodType L -> m f' :=
      match L with nil => fun _ => 0
      |f::l => fun x : (m f) + (sum_seq_lmodType l) => match f == f' with
        |true => 
          match x with inl y => (convertTypeTo _ y) |_ => 0 end
        |false =>
          match x with inr y => from_sum y |_ => 0 end
        end
      end. (* not needed *)
      Print Bool.reflect_rect.

    Program Definition testTo (f : F) (l : seq F) (next : pair_seq_lmodType l -> m f')
     : pair_lmodType (m f) (pair_seq_lmodType l) -> m f'
    := fun x => match f == f' with
    |true => (eq_rect (A:=F) f m (proj1Lin x) f' (_))
    |false => next (proj2Lin x)
    end.
    Next Obligation.
      symmetry in Heq_anonymous.
      by apply (rwP eqP) in Heq_anonymous.
    Qed.
    
    Fixpoint from_pair (L : seq F) {struct L} : pair_seq_lmodType L -> m f' :=
      match L with nil => fun _ => 0
      |f::l => testTo (f:=f) (from_pair (L:=l))
      end.


    Definition inj (L : seq F) : m f' -> pair_seq_lmodType L :=
    fun x => sum_to_pair (to_sum L x).

    Definition proj (L : seq F) : pair_seq_lmodType L -> m f' :=
      fun x => (from_pair x).

    Section Results.
      Variable (L : seq F).
      Lemma proj_lin : linear (proj (L:=L)).
        Proof. rewrite /(additive _)/morphism_2=>r x y.
          induction L=>//=.
          by rewrite GRing.scaler0 GRing.addr0.
          case (f'==a) as []eqn:E.
          apply (rwP eqP) in E.
          destruct E.
          rewrite /testTo. simpl.
          rewrite eq_refl.

          rewrite /inj/to_sum.
          rewrite /GRing.scale/GRing.add=>/=.
          by rewrite /add_pair/scale_pair GRing.scaler0 GRing.addr0. Qed.

      Lemma inj_lin : linear (inj L).
        Proof. rewrite /(additive (pair^~0%R))/morphism_2=>r x y.
          induction L=>//.
          rewrite /inj/to_sum.
          rewrite /GRing.scale/GRing.add=>/=.
          by rewrite /add_pair/scale_pair GRing.scaler0 GRing.addr0. Qed.
      Lemma inj2_lin : linear inj2.
      Proof. rewrite /(additive (pair^~0%R))/morphism_2=>r x y.
        rewrite /GRing.scale/GRing.add=>/=.
        by rewrite /add_pair/scale_pair GRing.scaler0 GRing.addr0. Qed.
  
  End Def.
End dsList.
*)




Module seq_dsLmod.
  Section Def.
    Variable (R : ringType).

    Fixpoint DS (L : seq (lmodType R)) : lmodType R
    := match L with
      |nil => lmodZero.type R
      |a'::L' => pair_lmodType a' (DS L')
      end.

    Fixpoint inj (L : list (lmodType R))
      (n : nat) {struct n} :
      seq.nth (lmodZero.type R) L n -> DS L
    := match L with
      |nil => match n with
        |0    => fun _ : (lmodZero.type R) => tt
        |S n' => fun _ : (lmodZero.type R) => tt
        end
      |a::L' => match n with
        |0    => fun x => @dsPair.inj1 R a (DS L') x
        |S n' => fun x => @dsPair.inj2 R a (DS L') ((@inj L' n') x)
        end
      end.

    Fixpoint proj (L : list (lmodType R))
      (n : nat) {struct n} :
      DS L -> seq.nth (lmodZero.type R) L n
    := match L with
      |nil => match n as n0 return (lmodZero.type R) -> (nth (lmodZero.type R) nil n0) with
        |0    => fun _ : (lmodZero.type R) => tt
        |S n' => fun _ : (lmodZero.type R) => tt
        end
      |a::L' => match n with
        |0    => fun x => @dsPair.proj1 R a (DS L') x
        |S n' => fun x => (@proj L' n') (@dsPair.proj2 R a (DS L') x)
        end
      end.

    Section Properties.
      Lemma inj_lin (L : list (lmodType R)) (n : nat) : linear (@inj L n).
      Proof. rewrite /morphism_2.
        move: n; induction L=>//=. {
        induction n=>//=. }{
        move : L IHL; induction n=>//=.
        move=> r x y; apply (GRing.linearP (@inj1Lin R a (DS L))).
        move=> r x y; rewrite -(GRing.linearP (@inj2Lin R a (DS L)))=>/=.
        by rewrite (IHL n)=>/=. }
      Qed.

      Lemma inj_injective
        (L : list (lmodType R)) (n : nat) : injective (@inj L n).
      Proof.
        move: n.
        induction L=>//=. { induction n; by move=> x y; destruct x, y. }
        move: L IHL.
        induction n; move=> x y H; [
        apply (@dsPair.inj1_injective R _ _ x y H) |
        apply (IHL n x y (@dsPair.inj2_injective R _ _ (@inj L n x) (@inj L n y) H)) ].
      Qed.

      Lemma proj_lin (L : list (lmodType R)) (n : nat) : linear (@proj L n).
      Proof. rewrite /morphism_2.
        move: n.
        induction L=>//=. {
        induction n=>//=. }{
        move: L IHL; induction n=>//=.
        by move=> r x y; rewrite -(IHL n) (GRing.linearP (@proj2Lin R a (DS L))). }
      Qed.
    End Properties.
  End Def.
  Section Results.
    Variable (R : ringType).
    Lemma nthS {a d} {n : nat} (L : list (lmodType R))
    : seq.nth d (a::L) (S n) -> seq.nth d L n.
    Proof. by induction n. Qed.

    Lemma inj_cons n a (L : list (lmodType R)) x : @inj R (a::L) (S n) x = dsPair.inj2 a (@inj R L n x).
    Proof. induction n, L=>//. Qed.

    Lemma proj_cons n a (L : list (lmodType R)) x : @proj R (a::L) (S n) (dsPair.inj2 a x) = @proj R L n x.
    Proof. induction n, L=>//. Qed.

    Lemma proj_inj_cons (n : nat) a (L : list (lmodType R)) x
     : @proj R (a::L) (S n) (@inj R (a::L) (S n) x) = @proj R L n (@inj R L n x).
     Proof. induction n, L=>//. Qed.


    Lemma proj_injK (n : nat) (L : list (lmodType R)) x : @proj R L n (@inj R L n x) = x.
    Proof.
      induction n=>//.
      induction L=>//.
      by rewrite /proj/inj; case x.
      move: n x IHn.
      induction L=>n x IHn//.
      by rewrite /proj/inj; case x.
      rewrite proj_inj_cons.
    Admitted.
  End Results.
End seq_dsLmod.
Canonical listInjLin {R : ringType} (L : list (lmodType R)) (n : nat)
    : {linear seq.nth (lmodZero.type R) L n ->  seq_dsLmod.DS L}
:= Linear (@seq_dsLmod.inj_lin R L n).

Canonical listProjLin {R : ringType} (L : list (lmodType R)) (n : nat)
    : {linear seq_dsLmod.DS L -> seq.nth (lmodZero.type R) L n}
:= Linear (@seq_dsLmod.proj_lin R L n).





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
    Definition DS : lmodType R := seq_dsLmod.DS (map I (enum F)).

    Section TypeConversion.
      Definition ListToDS (f : F) : seq_dsLmod.DS (map I (enum F)) -> DS := id.
      Definition DStoList (f : F) : DS -> seq_dsLmod.DS (map I (enum F)) := id.

      Lemma nth_If_eq {f : F} :
        seq.nth (lmodZero.type R) (map I (enum F)) (enum_rank f) = I f.
      Proof. rewrite (seq.nth_map f (lmodZero.type R)).
        by rewrite -(enum_val_nth f) (enum_rankK f).
        by rewrite -cardE.
      Qed.

      Definition nthToIf {f : F} :
        seq.nth (lmodZero.type R) (map I (enum F)) (enum_rank f) -> I f
      := (fun fn : I f -> I f => eq_rect_r (fun M : lmodType R => M -> I f) fn nth_If_eq) id.

      Definition nthToIf_lin {f : F} : linear (@nthToIf f).
      Proof. rewrite /nthToIf/eq_rect_r/eq_rect=>r x y.
      by destruct (Logic.eq_sym (@nth_If_eq f)). Qed.

      Definition nthToIfLin {f : F} :
        {linear seq.nth (lmodZero.type R) (map I (enum F)) (enum_rank f) -> I f}
      := Linear (@nthToIf_lin f).

      Definition IfToNth {f : F} :
        I f -> seq.nth (lmodZero.type R) (map I (enum F)) (enum_rank f)
      := (fun fn : I f -> I f => eq_rect_r (fun M : lmodType R => I f -> M) fn nth_If_eq) id.

      Definition IfToNth_lin {f : F} : linear (@IfToNth f).
      Proof. rewrite /IfToNth/eq_rect_r/eq_rect=>r x y.
      by destruct (Logic.eq_sym (@nth_If_eq f)). Qed.

      Definition IfToNthLin {f : F} :
        {linear I f -> seq.nth (lmodZero.type R) (map I (enum F)) (enum_rank f)}
      := Linear (@IfToNth_lin f).
    End TypeConversion.

    Definition proj (f : F) (x : DS) : I f
    := nthToIfLin (@seq_dsLmod.proj R (map I (enum F)) (enum_rank f) x).

    Lemma proj_lin (f : F) : linear (proj f).
    Proof. rewrite/proj=> r x y.
    by rewrite !GRing.linearPZ. Qed.

    Definition projLin (f : F) : {linear DS -> I f} := Linear (proj_lin f).

    Definition inj (f : F) (x : I f) : DS
    := @seq_dsLmod.inj R (map I (enum F)) (enum_rank f) (IfToNthLin x).

    Lemma inj_lin (f : F) : linear (@inj f).
    Proof. rewrite/inj=> r x y.
    by rewrite !GRing.linearPZ. Qed.

    Definition injLin (f : F) : {linear I f -> DS} := Linear (@inj_lin f).

    Lemma inj_injective (f : F) : injective (@inj f).
    Proof. move=> x y H.
      pose (A := @seq_dsLmod.inj_injective R (map I (enum F)) (enum_rank f) _ _ H).
      inversion A; rewrite /IfToNth/eq_rect_r/eq_rect in H1.
      by destruct(Logic.eq_sym (@nth_If_eq f)).
    Qed.

    Axiom inj_index_injective : forall (f g : F) (x : I f) (y : I g),
      @inj f x = @inj g y -> f = g.

    Lemma projinjK (f : F) x : @proj f (@inj f x) = x.
    Proof. rewrite /proj/inj seq_dsLmod.proj_injK=>/=.
      rewrite /nthToIf/IfToNth/IfToNth/eq_rect_r/eq_rect.
      by destruct(Logic.eq_sym (@nth_If_eq f)).
    Qed.
  End Def.
End dsLmod.

Notation "\bigoplus_ i F" := (dsLmod.DS (fun i => F i)).
Notation "\bigoplus F" := (dsLmod.DS F).
Notation "\bigoplus_ ( i : t ) F" := (dsLmod.DS (fun i : t => F i)).
Notation "\bigoplus_ ( i 'in' A ) F" := (seq_dsLmod.DS (filter F (fun i => i \in A))).


  (*

    Module Exports.
    
      Notation "\bigoplus_ ( a : t | P ) F " := (dsType.DS (fun a => F)) (at level 41, F at level 41, a at level 41).

      Notation "[ f --> inj]( x )" := (inj _ f x) (at level 0).
      Notation "[proj --> f ]( x )" := (proj _ f x) (at level 0).
    End Exports.
  End idx.
  Export idx.Exports.

  Module inf.
    Open Scope ring_scope.
    Section Def.
    Variable (R : ringType) (T : eqType) (I : T -> (lmodType R)).
    Record DS := InfType {
      FinSubType : finType;
      FinSubFun : FinSubType -> T;
      elem : GRing.Lmodule.sort (List.DS (map (I \o FinSubFun) (enum FinSubType)));
    }.
    Definition Add (x y : DS) : DS.
  destruct x, y.
  case(
  := \sum_(ex : elem x)\sum_(ey : elem y) ex 
    Definition DS_zmodMixin := ZmodMixin 4.
  *)


Module linExt.
  Section Def.
    Variable (R : ringType) (F1 F2 : finType).
    Variable (I1 : F1 -> (lmodType R)) (I2 : F2 -> (lmodType R))
    (fn : forall (f1 : F1) (f2 : F2), {linear (I1 f1) -> (I2 f2)} ).
    Definition ExtendLinearly  (x : \bigoplus I1) : \bigoplus I2 :=
      \sum_(f2 : F2)
        \sum_(f1 : F1)
          @dsLmod.inj _ _ I2 f2
            (fn f1 f2
              (@dsLmod.proj _ _ I1 f1 x)
            ).

    Lemma ExtendLinearly_lin : linear ExtendLinearly.
    Proof. rewrite /ExtendLinearly =>r x y.
      rewrite GRing.scaler_sumr -big_split=>/=.
      refine (eq_bigr _ _) => f2 _.
      rewrite GRing.scaler_sumr -big_split=>/=.
      refine (eq_bigr _ _) => f1 _.
      by rewrite -!GRing.linearPZ=>/=.
    Qed.
    Definition ExtendLinearlyLin : {linear (\bigoplus_f I1) -> (\bigoplus_f I2)}
        := Linear ExtendLinearly_lin.
  End Def.

  Section FromDef.
    Variable (R : ringType) (F : finType)
      (I : F -> (lmodType R)) (V : lmodType R)
      (fn : forall (f : F), {linear (I f) -> V}).
    Definition ExtendLinearlyFrom (x : \bigoplus I) : V
      := \sum_(f : F)
            fn f (@dsLmod.proj _ _ I f x).

    Lemma ExtendLinearlyFrom_lin : linear ExtendLinearlyFrom.
    Proof. rewrite /ExtendLinearlyFrom=>r x y.
      rewrite GRing.scaler_sumr-big_split=>/=.
      refine (eq_bigr _ _) => f2 _.
      by rewrite -!GRing.linearPZ=>/=.
    Qed.

    Definition ExtendLinearlyFromLin : {linear (\bigoplus I) -> V}
        := Linear ExtendLinearlyFrom_lin.
  End FromDef.

  Section ToDef.
    Variable (R : ringType) (F : finType) (I : F -> (lmodType R))
      (U : lmodType R) (fn : forall (f : F), {linear U -> (I f)}).
    Definition ExtendLinearlyTo (x : U) : \bigoplus I :=
      \sum_(f : F)
          @dsLmod.inj _ _ I f (fn f x).

    Lemma ExtendLinearlyTo_lin : linear ExtendLinearlyTo.
    Proof. rewrite /ExtendLinearlyTo=>r x y.
      rewrite GRing.scaler_sumr-big_split=>/=.
      refine (eq_bigr _ _) => f _.
      by rewrite -!GRing.linearPZ=>/=.
    Qed.

    Definition ExtendLinearlyToLin : {linear U -> \bigoplus I}
      := Linear ExtendLinearlyTo_lin.  
  End ToDef.
End linExt.

Canonical linExt.ExtendLinearlyLin.
Canonical linExt.ExtendLinearlyFromLin.
Canonical linExt.ExtendLinearlyToLin.
