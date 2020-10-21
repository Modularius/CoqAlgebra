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

Open Scope ring_scope.
Set Implicit Arguments.
Unset Strict Implicit.
Include GRing.


Reserved Notation "\bigoplus_ i F"
(at level 41, F at level 41, i at level 50,
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

Reserved Notation "\proj^( I )_ f "
(at level 36, f at level 36, I at level 36,
  format "'[' \proj^( I )_ f ']'").

Reserved Notation "\inj^( I )_ f "
(at level 36, f at level 36, I at level 36,
  format "'[' \inj^( I )_ f ']'").

Reserved Notation "\proj_ f ^( I ) "
(at level 36, f at level 36, I at level 36,
  format "'[' \proj_ f '^(' I ) ']'").

Reserved Notation "\inj_ f ^( I )"
(at level 36, f at level 36, I at level 36,
  format "'[' \inj_ f '^(' I ) ']'").


Module BigOplus.
  Module Pair.
    Section Def.
    Variable (R : ringType).
    Section ClassDef.
      Variable (lmodExtra : Type) (make : lmodExtra -> lmodType R).
      Local Coercion make : lmodExtra >-> lmodType.

      Section Mixin.
        Variable (oplus : lmodExtra -> lmodExtra -> lmodExtra).
        Structure mixin := Mixin {
          incl1_raw : forall (m1 m2 : lmodExtra), m1 -> (oplus m1 m2);
          incl2_raw : forall (m1 m2 : lmodExtra), m2 -> (oplus m1 m2);
          proj1_raw : forall (m1 m2 : lmodExtra), (oplus m1 m2) -> m1;
          proj2_raw : forall (m1 m2 : lmodExtra), (oplus m1 m2) -> m2;
        }.
        Structure prop_mixin (mx : mixin) := PropMixin {
          incl1_lin : forall (m1 m2 : lmodExtra), linear (@incl1_raw mx m1 m2);
          incl1 := fun (m1 m2 : lmodExtra) => locked (Linear (@incl1_lin m1 m2));
          incl2_lin : forall (m1 m2 : lmodExtra), linear (@incl2_raw mx m1 m2);
          incl2 := fun (m1 m2 : lmodExtra) => locked (Linear (@incl2_lin m1 m2));
          proj1_lin : forall (m1 m2 : lmodExtra), linear (@proj1_raw mx m1 m2);
          proj1 := fun (m1 m2 : lmodExtra) => locked (Linear (@proj1_lin m1 m2));
          proj2_lin : forall (m1 m2 : lmodExtra), linear (@proj2_raw mx m1 m2);
          proj2 := fun (m1 m2 : lmodExtra) => locked (Linear (@proj2_lin m1 m2));
          proj1_incl1K_raw : forall (m1 m2 : lmodExtra) x, @proj1_raw mx m1 m2 (@incl1_raw mx m1 m2 x) = x;
          proj2_incl2K_raw : forall (m1 m2 : lmodExtra) x, @proj2_raw mx m1 m2 (@incl2_raw mx m1 m2 x) = x;
          proj1_incl20_raw : forall (m1 m2 : lmodExtra) x, @proj1_raw mx m1 m2 (@incl2_raw mx m1 m2 x) = 0;
          proj2_incl10_raw : forall (m1 m2 : lmodExtra) x, @proj2_raw mx m1 m2 (@incl1_raw mx m1 m2 x) = 0;
          incl_proj_sum_raw : forall (m1 m2 : lmodExtra) x, x = @incl1_raw mx m1 m2 (@proj1_raw mx m1 m2 x) + @incl2_raw mx m1 m2 (@proj2_raw mx m1 m2 x);
        }.
      End Mixin.

      Section Results.
        Variable (oplus : lmodExtra -> lmodExtra -> lmodExtra).
        Variable (mx : mixin oplus) (pmx : prop_mixin mx).
        Lemma proj1_incl1K : forall (m1 m2 : lmodExtra) x, proj1 pmx m1 m2 (incl1 pmx m1 m2 x) = x.
        Proof. rewrite/proj1/incl1=>m1 m2 x=>/=; unlock (locked _);
        by apply (proj1_incl1K_raw pmx). Qed.
        Lemma proj2_incl2K : forall (m1 m2 : lmodExtra) x, proj2 pmx m1 m2 (incl2 pmx m1 m2 x) = x.
        Proof. rewrite/proj2/incl2=>m1 m2 x=>/=; unlock (locked _);
        by apply (proj2_incl2K_raw pmx). Qed.
        Lemma proj1_incl20 : forall (m1 m2 : lmodExtra) x, proj1 pmx m1 m2 (incl2 pmx m1 m2 x) = 0.
        Proof. rewrite/proj1/incl2=>m1 m2 x=>/=; unlock (locked _);
        by apply (proj1_incl20_raw pmx). Qed.
        Lemma proj2_incl10 : forall (m1 m2 : lmodExtra) x, proj2 pmx m1 m2 (incl1 pmx m1 m2 x) = 0.
        Proof. rewrite/proj2/incl1=>m1 m2 x=>/=; unlock (locked _);
        by apply (proj2_incl10_raw pmx). Qed.
        Lemma incl_proj_sum : forall (m1 m2 : lmodExtra) x, x = incl1 pmx m1 m2 (proj1 pmx m1 m2 x) + incl2 pmx m1 m2 (proj2 pmx m1 m2 x).
        Proof. rewrite/proj1/incl1/proj2/incl2=>m1 m2 x=>/=; unlock (locked _);
        by apply (incl_proj_sum_raw pmx). Qed.
      End Results.

      Structure class := Class { oplus : _; mixin_of : mixin oplus; prop_mixin_of : prop_mixin mixin_of}.
    End ClassDef.

    Structure type := Pack { sort : Type; to_lmod : sort -> lmodType R ; class_of : class to_lmod}.
    End Def.

    Module Exports.
      Coercion sort : type >-> Sortclass.
      Coercion class_of : type >-> class.
      Coercion mixin_of : class >-> mixin.
      Coercion prop_mixin_of : class >-> prop_mixin.

      Infix "\oplus" := (oplus _) (at level 35).
      Notation "\proj1^( m1 , m2 )" := (proj1 _ m1 m2).
      Notation "\proj2^( m1 , m2 )" := (proj2 _ m1 m2).
      Notation "\incl1^( m1 , m2 )" := (incl1 _ m1 m2).
      Notation "\incl2^( m1 , m2 )" := (incl2 _ m1 m2).
    End Exports.
  End Pair.

  Module Seq.
    Section Def.
      Variable (R : ringType).
      Section ClassDef.
      Variable (lmodExtra : Type) (make : lmodExtra -> lmodType R) (lmodZero : lmodExtra).
      Local Coercion make : lmodExtra >-> lmodType.


      Section Mixin.
        Variable (oplus : lmodExtra -> lmodExtra -> lmodExtra).

        Definition Nth (T : eqType) (I : T -> lmodExtra) := (fun L n
        => match (seq.nth None (map Some L) n) with
        |Some t => I t
        |None => lmodZero
        end).

        Fixpoint DS (T : eqType) (I : T -> lmodExtra) (L : seq T) : lmodExtra
        := match L with
          |nil => lmodZero
          |a'::L' => oplus (I a') (DS I L')
        end.

        Structure mixin := Mixin {
          incl_raw : forall (T : eqType) (I : T -> lmodExtra) L n, Nth I L n -> DS I L;
          proj_raw : forall (T : eqType) (I : T -> lmodExtra) L n, DS I L -> Nth I L n;
        }.
        Structure prop_mixin (mx : mixin) := PropMixin {
          incl_lin : forall (T : eqType) (I : T -> lmodExtra) L n, linear (@incl_raw mx T I L n);
          incl := fun (T : eqType) (I : T -> lmodExtra) L n => locked (Linear (@incl_lin T I L n));
          proj_lin : forall (T : eqType) (I : T -> lmodExtra) L n, linear (@proj_raw mx T I L n);
          proj := fun (T : eqType) (I : T -> lmodExtra) L n => locked (Linear (@proj_lin T I L n));
          proj_inclK_raw : forall (T : eqType) (I : T -> lmodExtra) L n x, @proj_raw mx T I L n (@incl_raw mx T I L n x) = x;
          proj_incl0_raw : forall (T : eqType) (I : T -> lmodExtra) L n n' x, (n != n') -> @proj_raw mx T I L n (@incl_raw mx T I L n' x) = 0;
          incl_proj_sum_raw : forall (T : eqType) (I : T -> lmodExtra) L x, x = \sum_(n : 'I_(size L))@incl_raw mx T I L n (@proj_raw mx T I L n x);
        }.
      End Mixin.

      Section Results.
        Variable (oplus : lmodExtra -> lmodExtra -> lmodExtra).
        Variable (mx : mixin oplus) (pmx : prop_mixin mx).
        Lemma proj_inclK : forall (T : eqType) (I : T -> lmodExtra) L n x, proj pmx I L n (incl pmx I L n x) = x.
        Proof. rewrite/proj/incl=>T I L n x=>/=; unlock (locked _);
        by apply (proj_inclK_raw pmx). Qed.
        Lemma proj_incl0 : forall (T : eqType) (I : T -> lmodExtra) L n n' x, (n != n') -> proj pmx I L n (incl pmx I L n' x) = 0.
        Proof. rewrite/proj/incl=>T I L n n' x H=>/=; unlock (locked _);
        by apply (proj_incl0_raw pmx). Qed.
        Lemma incl_proj_sum : forall (T : eqType) (I : T -> lmodExtra) L x, x = \sum_(n : 'I_(size L))incl pmx I L n (proj pmx I L n x).
        Proof. rewrite/proj/incl=>T I L x=>/=.
        (have : forall (n : 'I_(size L)) (_ : true),
        locked (Linear (incl_lin pmx (I:=I) (L:=L) (n:=n))) (locked (Linear (proj_lin pmx (I:=I) (L:=L) n)) x)
         = incl_raw mx (I:=I) (L:=L) (n:=n) (proj_raw mx (I:=I) (L:=L) n x)
        by move=>n _; unlock (locked _)=>/=)=>H.
        by rewrite (eq_bigr _ H) -(incl_proj_sum_raw pmx). Qed.
      End Results.

      Structure class := Class { oplus : _;
        pair_mixin_of : Pair.mixin make oplus;
        pair_prop_mixin_of : Pair.prop_mixin pair_mixin_of;
        mixin_of : mixin oplus;
        prop_mixin_of : prop_mixin mixin_of}.
    End ClassDef.

    Structure type := Pack { sort : Type; zero : sort; to_lmod : sort -> lmodType R ; class_of : class to_lmod zero}.
    End Def.

    Module Exports.
      Coercion sort : type >-> Sortclass.
      Coercion class_of : type >-> class.
      Coercion mixin_of : class >-> mixin.
      Coercion prop_mixin_of : class >-> prop_mixin.
      Coercion pair_mixin_of : class >-> Pair.mixin.
      Coercion pair_prop_mixin_of : class >-> Pair.prop_mixin.

      Notation "\bigoplus_ ( i 'in' A ) F" := (DS (filter F (fun i => i \in A))).
    End Exports.
  End Seq.
  Module Fin.
    Section Def.
      Variable (R : ringType).
      Section ClassDef.
        Variable (lmodExtra : Type) (make : lmodExtra -> lmodType R) (lmodZero : lmodExtra).
        Local Coercion make : lmodExtra >-> lmodType.
        Section Mixin.
          Variable (oplus : lmodExtra -> lmodExtra -> lmodExtra).

          Definition DS (F : finType) (I : F -> lmodExtra) : lmodType R
           := @Seq.DS lmodExtra lmodZero oplus F I (enum F).

          Structure mixin := Mixin {
            incl_raw : forall (F : finType) (I : F -> lmodExtra) f, I f -> DS I;
            proj_raw : forall (F : finType) (I : F -> lmodExtra) f, DS I -> I f;
          }.
          Structure prop_mixin (mx : mixin) := PropMixin {
            incl_lin : forall (F : finType) (I : F -> lmodExtra) f, linear (@incl_raw mx F I f);
            incl := fun (F : finType) (I : F -> lmodExtra) f => locked (Linear (@incl_lin F I f));
            proj_lin : forall (F : finType) (I : F -> lmodExtra) f, linear (@proj_raw mx F I f);
            proj := fun (F : finType) (I : F -> lmodExtra) f => locked (Linear (@proj_lin F I f));
            proj_inclK_raw : forall (F : finType) (I : F -> lmodExtra) f x, @proj_raw mx F I f (@incl_raw mx F I f x) = x;
            proj_incl0_raw : forall (F : finType) (I : F -> lmodExtra) f f' x, (f != f') -> @proj_raw mx F I f (@incl_raw mx F I f' x) = 0;
            incl_proj_sum_raw : forall (F : finType) (I : F -> lmodExtra) x, x = \sum_(f : F)@incl_raw mx F I f (@proj_raw mx F I f x);
          }.
        End Mixin.

        Section Results.
        Variable (oplus : lmodExtra -> lmodExtra -> lmodExtra).
        Variable (mx : mixin oplus) (pmx : prop_mixin mx).
          Lemma proj_inclK : forall (F : finType) (I : F -> lmodExtra) f x, proj pmx I f (incl pmx I f x) = x.
          Proof. rewrite/proj/incl=>F I f x=>/=; unlock (locked _);
          by apply (proj_inclK_raw pmx). Qed.
          Lemma proj_incl0 : forall (F : finType) (I : F -> lmodExtra) f f' x, (f != f') -> proj pmx I f (incl pmx I f' x) = 0.
          Proof. rewrite/proj/incl=>F I f x=>/=; unlock (locked _);
          by apply (proj_incl0_raw pmx). Qed.
          Lemma incl_proj_sum : forall (F : finType) (I : F -> lmodExtra) x, x = \sum_(f : F)incl pmx I f (proj pmx I f x).
          Proof. rewrite/proj/incl=>F I x=>/=.
            (have : forall (f : F) (_ : true),
            locked (Linear (incl_lin pmx (I:=I) (f:=f))) (locked (Linear (proj_lin pmx (I:=I) f)) x)
            = incl_raw mx (I:=I) (f:=f) (proj_raw mx (I:=I) f x)
            by move=>n _; unlock (locked _)=>/=)=>H.
            by rewrite (eq_bigr _ H) -(incl_proj_sum_raw pmx). Qed.
        End Results.

        Structure class := Class { oplus : _;
                                  pair_mixin_of : Pair.mixin make oplus;
                                  pair_prop_mixin_of : Pair.prop_mixin pair_mixin_of;
                                  seq_mixin_of : Seq.mixin make lmodZero oplus;
                                  seq_prop_mixin_of : Seq.prop_mixin seq_mixin_of;
                                  mixin_of : mixin oplus;
                                  prop_mixin_of : prop_mixin mixin_of}.
      End ClassDef.
    End Def.
      
    Structure type := Pack { sort : Type; R : ringType; zero : sort; to_lmod : sort -> lmodType R ; class_of : class to_lmod zero}.
    Module Exports.
      Coercion sort : type >-> Sortclass.
      Coercion class_of : type >-> class.
      Coercion mixin_of : class >-> mixin.
      Coercion prop_mixin_of : class >-> prop_mixin.
      Coercion seq_mixin_of : class >-> Seq.mixin.
      Coercion seq_prop_mixin_of : class >-> Seq.prop_mixin.
      Coercion pair_mixin_of : class >-> Pair.mixin.
      Coercion pair_prop_mixin_of : class >-> Pair.prop_mixin.

      Notation "\bigoplus_ i F" := (DS (fun i => F i)).
      Notation "\bigoplus F" := (DS F).
      Notation "\bigoplus_ ( i : t ) F" := (DS (fun i : t => F i)).
      Notation "\proj^( I )_ f " := (proj I f).
      Notation "\inj^( I )_ f " := (incl I f).
      Notation "\proj_ f ^( I )" := (proj I f).
      Notation "\inj_ f ^( I )" := (incl I f).
    End Exports.
  End Fin.
End BigOplus.

Export BigOplus.Fin.Exports.