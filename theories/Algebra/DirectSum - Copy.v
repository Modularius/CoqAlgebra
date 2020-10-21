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
Include GRing.

Open Scope  lmod_scope.

Section Helpers.
  Variable (R : ringType).
  Section LinearSumSimpl.
    Variable (A B C D E : lmodType R) (Ty : finType) (f : {linear A -> B}) (g : {linear B -> C}) (h : {linear C -> D}) (k : {linear D -> E}) (x : Ty -> A).
    Lemma linear2_sum :
    g (f (\sum_(i : Ty) (x i))) = \sum_(i : Ty) g (f (x i)).
    Proof. by rewrite !linear_sum. Qed.
  End LinearSumSimpl.

  Section LinearSumSimpl.
    Variable (S : finType) (X : lmodType R) (f : S*S -> X).
    Lemma big_pair_diag_eq :
      \sum_(i : S*S | i.2 == i.1)f i
        = \sum_(i : S) f (i, i).
    Proof.
      have : forall (i : S) (_ : true), f (i, i) = \sum_(j : S) if (j == i) then f (i, j) else 0
      by move=>i _;
      rewrite -big_mkcond (big_pred1 i).
      move=> H; rewrite (eq_bigr _ H); clear H.
      by rewrite pair_bigA -big_mkcond
      (eq_bigr (fun i => f (i.1,i.2)) _)=>/=;
        [|move=>i _; destruct i=>/=].
    Qed.
  End LinearSumSimpl.

End Helpers.



Reserved Notation "\bigoplus_ i F"
(at level 36, F at level 36, i at level 50,
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


Module dsLmod.
  Module Pair.
    Section Def.
      Variable (R : ringType) (m1 m2 : lmodType R).

      Section Submodule.
        Definition in1 : predPredType (m1*m2) := fun x => x.2 == 0.
        Lemma factor1_subModule : submod_closed (subLmod.qualSubElem in1).
          Proof. split=>[|r x y]; rewrite qualifE !unfold_in; [by rewrite eq_refl| rewrite -!(rwP eqP)=>/=Hx Hy];
          by rewrite Hx Hy scaler0 addr0. Qed.
        Definition sub1 := subLmodPack factor1_subModule.

        Definition in2 : predPredType (m1*m2) := fun x => x.1 == 0.
        Lemma factor2_subModule : submod_closed (subLmod.qualSubElem in2).
          Proof. split=>[|r x y]; rewrite qualifE !unfold_in; [by rewrite eq_refl| rewrite -!(rwP eqP)=>/=Hx Hy];
          by rewrite Hx Hy scaler0 addr0. Qed.
        Definition sub2 := subLmodPack factor1_subModule.
      End Submodule.

      Section Injection.
        Definition inj1_raw := fun x : m1 => (x,zero m2) : pair_lmodType m1 m2.
        Definition inj2_raw := fun x : m2 => (zero m1, x) : pair_lmodType m1 m2.

        Lemma inj1_lin : linear inj1_raw.
        Proof. rewrite /(additive (pair^~0%R))/morphism_2=>r x y.
          rewrite /scale/add=>/=.
          by rewrite /add_pair/scale_pair scaler0 addr0. Qed.
        Lemma inj2_lin : linear inj2_raw.
        Proof. rewrite /(additive (pair^~0%R))/morphism_2=>r x y.
          rewrite /scale/add=>/=.
          by rewrite /add_pair/scale_pair scaler0 addr0. Qed.

        Lemma inj1_injective : injective inj1_raw.
        Proof. by move=>x y H; inversion H. Qed.
        Lemma inj2_injective : injective inj2_raw.
        Proof. by move=>x y H; inversion H. Qed.

        Definition inj1 := Linear inj1_lin.
        Definition inj2 := Linear inj2_lin.

        Lemma inj1_unraw x : inj1_raw x = inj1 x. Proof. by []. Qed.
        Lemma inj2_unraw x : inj2_raw x = inj2 x. Proof. by []. Qed.
      End Injection.

      Section Projection.
        Definition proj1_raw := fun x : pair_lmodType m1 m2 => x.1.
        Definition proj2_raw := fun x : pair_lmodType m1 m2 => x.2.

        Lemma proj1_lin : linear proj1_raw.
        Proof. by rewrite /morphism_2. Qed.
        Lemma proj2_lin : linear proj2_raw.
        Proof. by rewrite /morphism_2. Qed.

        Definition proj1 := Linear proj1_lin.
        Definition proj2 := Linear proj2_lin.

        Lemma proj1_unraw x : proj1_raw x = proj1 x. Proof. by []. Qed.
        Lemma proj2_unraw x : proj2_raw x = proj2 x. Proof. by []. Qed.

        Lemma proj1_inj1K x : proj1 (inj1 x) = x. Proof. by []. Qed.
        Lemma proj2_inj2K x : proj2 (inj2 x) = x. Proof. by []. Qed.
        Lemma proj1_inj20 x : proj1 (inj2 x) = 0. Proof. by []. Qed.
        Lemma proj2_inj10 x : proj2 (inj1 x) = 0. Proof. by []. Qed.
      End Projection.

      Lemma inj_proj_sum x : x = inj1 (proj1 x) + inj2 (proj2 x).
      Proof.
        rewrite /inj1/proj1/inj2/proj2/(add _)=>/=;
        rewrite /add_pair addr0 add0r;
        by destruct x.
      Qed.
    End Def.

    Section MorphismsToDS.
      Variable (R : ringType) (M N1 N2 : lmodType R)
        (f1 : {linear M -> N1}) (f2 : {linear M -> N2}).

      Definition to_ds_raw : M -> (pair_lmodType N1 N2)
        := fun x => (inj1 _ _ (f1 x)) + (inj2  _ _ (f2 x)).

      Lemma to_ds_lin : linear to_ds_raw.
      Proof. rewrite/to_ds_raw=>r x y.
      by rewrite !linearP addrACA scalerDr. Qed.
      Definition to_ds : {linear M -> (pair_lmodType N1 N2)}
        := Linear to_ds_lin.

    End MorphismsToDS.

    Section MorphismsFromDS.
      Variable (R : ringType) (M1 M2 N : lmodType R)
        (f1 : {linear M1 -> N}) (f2 : {linear M2 -> N}).

      Definition from_ds_raw : (pair_lmodType M1 M2) -> N
        := fun x => (f1 (proj1 _ _ x)) + (f2 (proj2  _ _ x)).

      Lemma from_ds_lin : linear from_ds_raw.
      Proof. rewrite/from_ds_raw=>r x y.
      by rewrite !linearP addrACA scalerDr. Qed.

      Definition from_ds : {linear (pair_lmodType M1 M2) -> N}
        := Linear from_ds_lin.

    End MorphismsFromDS.

    Section MorphismsDiag.
      Variable (R : ringType) (M1 M2 N1 N2 : lmodType R)
        (f1 : {linear M1 -> N1}) (f2 : {linear M2 -> N2}).

      Definition diag_raw : (pair_lmodType M1 M2) -> (pair_lmodType N1 N2)
        := fun x => (inj1 _ _ (f1 (proj1 _ _ x))) + (inj2 _ _ (f2 (proj2  _ _ x))).

      Lemma diag_lin : linear diag_raw.
      Proof. rewrite/diag_raw=>r x y.
      by rewrite !linearP addrACA scalerDr. Qed.

      Definition diag : {linear (pair_lmodType M1 M2) -> (pair_lmodType N1 N2)}
        := Linear diag_lin.

    End MorphismsDiag.
    Section MorphismsDiag.
    Variable (R : ringType) (M1 M2 N1 N2 O1 O2 : lmodType R)
      (f1 : {linear M1 -> N1}) (f2 : {linear M2 -> N2})
      (g1 : {linear N1 -> O1}) (g2 : {linear N2 -> O2}).
      Lemma diag_comp : (diag g1 g2) \o (diag f1 f2) = diag (g1 \oLin f1) (g2 \oLin f2).
      Proof. simpl. rewrite/diag_raw=>/=. Admitted.
    End MorphismsDiag.


    Module Exports.
      (*Canonical proj1 {R : ringType} {m1 m2 : lmodType R}
        := locked (proj1 m1 m2).
      Canonical proj2 {R : ringType} {m1 m2 : lmodType R}
        := proj2 m1 m2.

      Canonical inj1 {R : ringType} {m1 m2 : lmodType R}
        := inj1 m1 m2.
      Canonical inj2Lin {R : ringType} {m1 m2 : lmodType R}
        := inj2Lin m1 m2.*)

      Notation lmodDSPairType := pair_lmodType.
      Infix "\oplus" := (pair_lmodType) (at level 35).
      Infix "\linPlusDiag" := (diag) (at level 35).
      Infix "\linPlusRow" := (from_ds) (at level 35).
      Infix "\linPlusCol" := (to_ds) (at level 35).
    End Exports.
  End Pair.
  Export Pair.Exports.



  Module Seq.
    Section Ring.
    Variable (R : ringType).
    Section Environment.
      Variable (T : eqType) (I : T -> lmodType R).

      Section Def.
        Definition Nth := (fun L n
         => match (seq.nth None (map Some L) n) with
         |Some t => I t
         |None => lmodZero.type R
         end).

        Fixpoint DS (L : seq T) : lmodType R
        := match L with
          |nil => lmodZero.type R
          |a'::L' => (I a') \oplus (DS L')
        end.
      End Def.

      Section Submodule.
        Variable (L : seq T) (n : 'I_(size L)).
      End Submodule.

      Section Injection.
      Fixpoint inj_raw (L : seq T) (n : nat) {struct n} :
        Nth L n -> DS L
      := match L as LL return Nth LL n -> DS LL with
        |nil => fun _ => tt
        |a::L' => match n as nn return Nth (a::L') nn -> DS (a::L') with
          |0    => fun x => @Pair.inj1 R (I a) (DS L') x
          |S n' => fun x => @Pair.inj2 R (I a) (DS L') ((@inj_raw L' n') x)
          end
        end.

        Lemma inj_lin (L : seq T) (n : nat) : linear (@inj_raw L n).
        Proof. rewrite /morphism_2.
          move: n; induction L=>//=. {
          induction n=>//=. }{
          move : L IHL; induction n=>//=.
          move=> r x y; apply (linearP (@Pair.inj1 R (I a) (DS L))).
          move=> r x y; rewrite -(linearP (@Pair.inj2 R (I a) (DS L)))=>/=.
          by rewrite (IHL n)=>/=. }
        Qed.

        Lemma inj_injective
          (L : seq T) (n : nat) : injective (@inj_raw L n).
        Proof.
          move: n.
          induction L=>//=. { induction n; by move=> x y; destruct x, y. }
          move: L IHL.
          induction n; move=>/= x y H.
          apply (@Pair.inj1_injective R _ _ x y H).
          apply (IHL n x y (@Pair.inj2_injective R _ _ (@inj_raw L n x) (@inj_raw L n y) H)).
        Qed.
      End Injection.
      Definition inj (L : seq T) (n : nat)
        := Linear (@inj_lin L n).

      Lemma inj_unraw (L : seq T) (n : nat) x : inj_raw x = inj L n x. Proof. by []. Qed.

      Section Projection.
        Fixpoint proj_raw (L : seq T) (n : nat) {struct n} :
        DS L -> Nth L n
      := match L as LL return DS LL -> Nth LL n with
        |nil => match n as nn return lmodZero.type R -> Nth nil nn with
          |0    => fun _ => tt
          |S n' => fun _ => tt
          end
        |a::L' => match n as nn return DS (a::L') -> Nth (a::L') nn with
          |0    => fun x => @Pair.proj1 R (I a) (DS L') x
          |S n' => fun x => (@proj_raw L' n') (@Pair.proj2 R (I a) (DS L') x)
          end
        end.
        
        Lemma proj_lin (L : seq T) (n : nat) : linear (@proj_raw L n).
        Proof. rewrite /morphism_2.
          move: n.
          induction L=>//=. { induction n=>//=. }
          move: L IHL; induction n=>//=; move=> r x y.
          rewrite !Pair.proj2_unraw linearP.
          by rewrite -(IHL n).
        Qed.
      End Projection.
      Definition proj (L : seq T) (n : nat)
        := Linear (@proj_lin L n).
    
      Lemma proj_unraw (L : seq T) (n : nat) x : proj_raw n x = proj L n x. Proof. by []. Qed.

      Section Results.
        Section Lemmas.
          Variable (L : seq T).    
          Lemma nth_cons {a d} {n : nat} : seq.nth d (a::L) (S n) = seq.nth d L n.
          Proof. by induction n. Qed.
      
          Lemma inj_cons n a x : @inj (a::L) (S n) x = Pair.inj2 (I a) _ (@inj L n x).
          Proof. by []. Qed.
      
          Lemma proj_cons n a x : @proj (a::L) (S n) (Pair.inj2 (I a) _ x) = @proj L n x.
          Proof. by []. Qed.

          Lemma proj_inj_cons (n n' : nat) a x
          : @proj (a::L) (n.+1) (@inj (a::L) (n'.+1) x) = @proj L n (@inj L n' x).
          Proof. by []. Qed.
        End Lemmas.
        Variable (L : seq T).

        (* The following two lemmas are used for cancellation *)
        Lemma proj_injK_ofsize (n : 'I_(size L)) x : @proj L (nat_of_ord n) (@inj L (nat_of_ord n) x) = x.
        Proof.
          induction L=>/=. induction n=>//=.
          destruct n as [n N].
          induction n=>//=; simpl in x, IHl, N.
          rewrite -ltn_predRL in N; simpl in N.
          unlock Pair.proj2 Pair.inj2=>/=.
          apply (IHl (Ordinal N) x).
        Qed.

        Lemma proj_inj0_ofsize (n n' : 'I_(size L)) x : (nat_of_ord n) != n' -> @proj L n (@inj L n' x) = 0.
        Proof.
          induction L=>/=.
            induction n=>//=.
          destruct n as [n N], n' as [n' N'].
          simpl in x, IHl, N, N'=>/=H.
          induction n.
            apply (rwP negP) in H.
            by induction n'=>/=; [contradiction H|].
          induction n'=>/=.
            by rewrite proj_unraw linear0.
          rewrite eqSS in H;
          rewrite ltnS in N;
          rewrite ltnS in N';
          by apply (IHl (Ordinal N) (Ordinal N') x H).
        Qed.
        
        (* The following two lemmas are the same as above but more versitile,
        in that they don't require the index to be an ordinal of size L, simply
        that they are naturals less than size L *)
        Lemma proj_injK (n : nat) x (M : n < size L) : @proj L n (@inj L n x) = x.
        Proof. apply (@proj_injK_ofsize (Ordinal M)). Qed.
    
        Lemma proj_inj0 m1 m2 (n : 'I_m1) (n' : 'I_m2) x (M1 : m1 <= (size L)) (M2 : m2 <= (size L))
          : (nat_of_ord n) != n' -> @proj L n (@inj L n' x) = 0.
        Proof. apply (@proj_inj0_ofsize (widen_ord M1 n) (widen_ord M2 n')). Qed.

        (* this lemma expresses any element as a sum of projections *)
        Lemma inj_proj_sum x : x = \sum_(n < size L) inj L (nat_of_ord n) (@proj L (nat_of_ord n) x).
        Proof.
          induction L.
          by rewrite /size big_ord0; case x.
          destruct x as [Ia DSl].
          by rewrite big_ord_recl {1}(IHl DSl)
          (Pair.inj_proj_sum (Ia, _)) linear_sum.
        Qed.
      End Results.

      (* Given a direct sum indexed by a seq, we define a function to reform
      the direct sum into the direct sum of two smaller direct sums. *)
      Section Operations.
        Variable (L1 L2 : seq T).
        (*Tr = truncate, Ap = Append, R = right, L = left*)
        Section L1.
          Variable (n : 'I_(size L1)).
          Lemma catTrR_eq : (Nth (L1 ++ L2) n) = (Nth L1 n).
          Proof. destruct n as [n' H].
          by rewrite/Nth map_cat nth_cat size_map H. Qed.

          Definition catTrR : (Nth (L1 ++ L2) n) -> (Nth L1 n).
          Proof. by rewrite catTrR_eq. Defined.

          Definition catApR : (Nth L1 n) -> (Nth (L1 ++ L2) n).
          Proof. by rewrite catTrR_eq. Defined.

          Lemma catTrApR_lin : linear catTrR /\ linear catApR.
          Proof. split; rewrite/catTrR/catApR=>r x y; by destruct(catTrR_eq). Qed.

          Lemma catApTrRK : cancel catTrR catApR /\ cancel catApR catTrR.
          Proof. split; rewrite/catApR/catTrR=>x; by destruct(catTrR_eq). Qed.

          Definition catR : lmodIsomType (Nth (L1 ++ L2) n) (Nth L1 n)
           := lmodIsomBuildPack catTrApR_lin catApTrRK.
        End L1.
        Section L2.
          Variable (n : 'I_(size L2)).
      
          Lemma catTrL_eq : (Nth (L1 ++ L2) (rshift (size L1) n)) = (Nth L2 n).
          Proof. by simpl; rewrite/Nth map_cat nth_cat size_map
          -{2}(addn0 (size L1)) ltn_add2l addnC addnK. Qed.

          Definition catTrL : (Nth (L1 ++ L2) (rshift (size L1) n)) -> (Nth L2 n).
          Proof.  by rewrite catTrL_eq. Defined.

          Definition catApL : (Nth L2 n) -> (Nth (L1 ++ L2) (rshift (size L1) n)).
          Proof. by rewrite catTrL_eq. Defined.

          Lemma catTrApL_lin : linear catTrL /\ linear catApL.
          Proof. split; rewrite/catTrL/catApL=>r x y;by destruct (catTrL_eq). Qed.
          
          Lemma catApTrLK : cancel catTrL catApL /\ cancel catApL catTrL.
          Proof. split; rewrite/catApL/catTrL=>x; by destruct(catTrL_eq). Qed.

          Definition catL : lmodIsomType (Nth (L1 ++ L2) (rshift (size L1) n)) (Nth L2 n)
           := lmodIsomBuildPack catTrApL_lin catApTrLK.
        End L2.

        Definition split_raw : DS (L1 ++ L2) -> DS L1 \oplus DS L2
          := fun x =>
          (\sum_(n < size L1)(inj L1 n \oLin catR n \oLin proj (L1 ++ L2) n ) x,
           \sum_(n < size L2)(inj L2 n \oLin catL n \oLin proj (L1 ++ L2) (rshift (size L1) n)) x).

        Definition unsplit_raw : DS L1 \oplus DS L2 -> DS (L1 ++ L2)
        := fun x =>
          \sum_(n < size L1)((inj (L1 ++ L2) n                     \oLin inv(catR n) \oLin proj L1 n) x.1) +
          \sum_(n < size L2)((inj (L1 ++ L2) (rshift (size L1) n)  \oLin inv(catL n) \oLin proj L2 n) x.2).

        Lemma split_lin : linear split_raw.
        Proof. rewrite/split_raw=>r x y/=.
          by rewrite (rwP eqP)/eq_op -(rwP andP) -!(rwP eqP)=>/=;
          rewrite !scaler_sumr -!big_split !(eq_bigr _ (fun i _ => linearP _ _ _ _)).
        Qed.

        Lemma unsplit_lin : linear unsplit_raw.
        Proof. rewrite/unsplit_raw=>r x y/=.
          by rewrite !(eq_bigr _ (fun i _ => linearP _ _ _ _)) !big_split=>/=;
          rewrite -!scaler_sumr scalerDr !addrA (addrC _ (r *: _)) !addrA (addrC (r *: _) (r *: _)).
        Qed.

        Definition split := Linear split_lin.
        Definition unsplit := Linear unsplit_lin.

        Lemma splitsK : cancel split unsplit.
        Proof. simpl; rewrite /unsplit_raw/split_raw=>x.
          rewrite (eq_bigr _ (fun i _ => linear_sum _ _ _ _))
                  (eq_bigr _ (fun i _ => linear_sum _ _ _ _))
          !pair_bigA.
          rewrite (eq_bigr (fun p : 'I_(size L1)*'I_(size L1)
           => if p.2 == p.1
            then inj (L1 ++ L2) p.1 (proj (L1 ++ L2) p.1 x)
            else 0 ) _).
          rewrite (eq_bigr (fun p : 'I_(size L2)*'I_(size L2)
            => if p.2 == p.1
            then inj (L1 ++ L2) (rshift (size L1) p.2) (proj (L1 ++ L2) (rshift (size L1) p.2) x)
            else 0 ) _).
          rewrite -!big_mkcond !big_pair_diag_eq.
          rewrite (eq_bigr (fun p : 'I_(size L1) => inj _  _ (proj _ p x)) _);[|by move].
          rewrite (eq_bigr (fun p : 'I_(size L2) => inj _ _ (proj _ (rshift (size L1) p) x)) _);[|by move].
          by rewrite {3}(@inj_proj_sum _ x) size_cat (@big_split_ord _ _ _ (size L1) (size L2)).
          by move=>p _;
          case (p.2 == p.1) as []eqn:E; rewrite -!linCompChain;
          [apply (rwP eqP) in E; rewrite E proj_injK_ofsize (isomlK (catL p.1)) |
           rewrite proj_inj0_ofsize; [rewrite !linear0|
             rewrite eq_sym/eq_op in E; simpl in E; rewrite E]].
          by move=>p _;
          case (p.2 == p.1) as []eqn:E; rewrite -!linCompChain;
          [ apply (rwP eqP) in E; rewrite E proj_injK_ofsize (isomlK (catR p.1))|
          rewrite proj_inj0_ofsize; [rewrite !linear0|
            rewrite eq_sym/eq_op in E; simpl in E; rewrite E]].
        Qed.

        Lemma splitKs : cancel unsplit split.
        Proof. simpl; rewrite /unsplit_raw/split_raw=>x.
        rewrite (eq_bigr (fun n : 'I_(size L1)
        => (inj _ n \oLin catR n \oLin proj _ n)
            (\sum_(n0 < _) (inj _ n0 \oLin inv(catR n0) \oLin proj _ n0) x.1)
         + (inj _ n \oLin catR n \oLin proj _ n)
            (\sum_(n0 < _) (inj _ (rshift _ n0) \oLin inv(catL n0) \oLin proj _ n0) x.2))
        ); [|by move=>p _; rewrite !raddfD].
            
        rewrite (eq_bigr (fun n : 'I_(size L2)
        => (inj _ n \oLin catL n \oLin proj _ (rshift _ n))
            (\sum_(n0 < _) (inj _ n0 \oLin inv(catR n0) \oLin proj _ n0) x.1)
         + (inj _ n \oLin catL n \oLin proj _ (rshift _ n))
            (\sum_(n0 < _) (inj _ (rshift _ n0) \oLin inv(catL n0) \oLin proj _ n0) x.2))
        ); [|by move=>p _; rewrite !raddfD].

        rewrite !big_split !(eq_bigr _ (fun i _ => linear_sum _ _ _ _)) !pair_bigA.
        rewrite (eq_bigr (fun p : 'I_(size L1)*'I_(size L1)
         => if(p.2 == p.1)
          then inj L1 p.1 (proj L1 p.1 x.1)
          else 0) _).
        rewrite (eq_bigr (fun p : 'I_(size L2)*'I_(size L2)
         => if(p.2 == p.1)
          then inj L2 p.2 (proj L2 p.2 x.2)
          else 0) _).
        {
          destruct x as [x1 x2];
          rewrite -!big_mkcond !big_pair_diag_eq
          (eq_bigr (fun p : 'I_(size L1) => inj _ p (proj _ p x1)) _);[|by move].
          rewrite (eq_bigr (fun p : 'I_(size L2) => inj _ p (proj _ p x2)) _); [| by []].
          rewrite {4}(inj_proj_sum x1) {4}(inj_proj_sum x2) (rwP eqP) /eq_op -(rwP andP).
          split; rewrite -subr_eq0.

          rewrite {1}addrC addrA addNr add0r (eq_bigr (fun _ => 0) _).
          rewrite big_const cardE /iter enumT;
          induction(Finite.enum _)=>//=; by rewrite add0r.

          move =>[[p1 H1] [p2 H2]] _;
          rewrite -!linCompChain proj_inj0;[by rewrite !linear0 |by rewrite size_cat leq_addr|by rewrite size_cat|];
          rewrite -(rwP negP)/not -(rwP eqP)=>/=N;
          by rewrite N -{2}(addn0 (size L1)) ltn_add2l in H1.

          rewrite -addrA addrN addr0 (eq_bigr (fun _ => 0) _).
          rewrite big_const cardE /iter enumT;
          induction(Finite.enum _)=>//=; by rewrite add0r.

          move =>[[p1 H1] [p2 H2]] _;
          rewrite -!linCompChain proj_inj0;[by rewrite !linear0 |by rewrite size_cat|by rewrite size_cat leq_addr|];
          rewrite -(rwP negP)/not -(rwP eqP)=>/=N.
          by rewrite -N -{2}(addn0 (size L1)) ltn_add2l in H2.
        }
        move=>p _; case(p.2 == p.1) as []eqn:E.
        apply (rwP eqP) in E; rewrite E -!linCompChain.
        rewrite proj_injK; [by rewrite isomKl|].
        destruct p as [[p1 H1] [p2 H2]].
        by rewrite size_cat ltn_add2l.
        rewrite -!linCompChain proj_inj0; [by rewrite !linear0|by rewrite size_cat|by rewrite size_cat|].
        rewrite /eq_op in E; simpl in E.
        by rewrite /rshift eqn_add2l eq_sym E.

        move=>p _; case(p.2 == p.1) as []eqn:E.
        apply (rwP eqP) in E; rewrite -E -!linCompChain.
        rewrite proj_injK; [by rewrite isomKl|].
        destruct p as [[p1 H1] [p2 H2]]=>/=.
        by rewrite size_cat addnC (ltn_addl _ H2).
        rewrite -!linCompChain proj_inj0; [by rewrite !linear0|by rewrite size_cat leq_addr|by rewrite size_cat leq_addr|].
        rewrite /eq_op in E; simpl in E.
        by rewrite eq_sym E.
        Qed.
      End Operations.
    End Environment.
    
    Section Hom.
    Variable (S T : eqType) (I : T -> lmodType R) (T_S : S -> T).

    Fixpoint hom_raw (L : seq S) : DS (fun s => I (T_S s)) L -> DS I (map T_S L)
      := match L with
      |nil => id
      |a::l => fun x => (x.1 , hom_raw x.2)
      end.
    Fixpoint unhom_raw (L : seq S) : DS I (map T_S L) -> DS (fun s => I (T_S s)) L
      := match L with
      |nil => id
      |a::l => fun x => (x.1 , unhom_raw x.2)
      end.
    
    Variable (L : seq S).
    Lemma hom_lin : linear (@hom_raw L) /\ linear (@unhom_raw L).
    Proof. split; induction L=>//=r x y;
      by rewrite IHl/hom_raw/unhom_raw.
    Qed.
    Lemma homK : cancel (@hom_raw L) (@unhom_raw L) /\ cancel (@unhom_raw L) (@hom_raw L).
    Proof. split; induction L=>//=x; destruct x;
      by rewrite IHl.
    Qed.
    Definition hom := lmodIsomBuildPack hom_lin homK.
    End Hom.

    Section Bijection.
      Variable (S T : eqType) (I : T -> lmodType R)
          (T_S : S -> T) (S_T : T -> S) (Inj : cancel S_T T_S) (Surj : cancel T_S S_T).
      Fixpoint bij_raw (L : seq T) : DS I L -> DS (fun s => I (T_S s)) (map S_T L)
      := match L with
      |nil => id
      |a::l => fun x => (eq_rect_r (fun t : T => I t) x.1 (Inj a), bij_raw x.2)
      end.

      Fixpoint bijI_raw (L : seq T) : DS (fun s => I (T_S s)) (map S_T L) -> DS I L
      := match L with
      |nil => id
      |a::l => fun x => (eq_rect_r (fun t : T => I t -> I a)
        id (Inj a) x.1, bijI_raw x.2)
      end.

      Variable (L : seq T).
      Lemma bijIK : cancel (@bij_raw L) (@bijI_raw L).
      Proof. induction L=>x//=.
        rewrite /eq_rect_r/eq_rect IHl=>/=.
        by destruct(Logic.eq_sym (Inj a)), x=>/=.
      Qed.

      Lemma bijKI : cancel (@bijI_raw L) (@bij_raw L).
      Proof. induction L=>x//=;
        rewrite /eq_rect_r/eq_rect IHl=>/=;
        by destruct x, (Logic.eq_sym (Inj a))=>/=.
      Qed.

      Lemma bij_lin : linear (@bij_raw L).
      Proof. induction L=>r x y//=; rewrite /eq_rect_r/eq_rect IHl;
      by destruct (Logic.eq_sym (Inj a)). Qed.

      Lemma bijInv_lin : linear (@bijI_raw L).
      Proof. induction L=>r x y//=; rewrite /eq_rect_r/eq_rect IHl.
      by destruct (Inj a). Qed.

      Definition bij := Linear bij_lin.
      Definition bijI := Linear bijInv_lin.
      Definition bijection := Bijective bijIK bijKI.
    End Bijection.
    End Ring.
  End Seq.









  Section General.
    Variable (R : ringType).
    Section Def.
      Variable (F : finType) (I : F -> lmodType R).

      Definition DS : lmodType R := Seq.DS I (enum F).

      Section Components.
        Variable (f : F).

        Lemma cardElt : nat_of_ord (enum_rank f) < size (enum F).
        Proof. rewrite -cardE; apply ltn_ord. Qed.

        Definition Ord := Ordinal cardElt.
        Definition Nth := Seq.Nth I (enum F) Ord.

        Section TypeConversion.
          Lemma Nth_If_eq : Nth = I f.
          Proof. by rewrite /Nth/Seq.Nth
            -codomE nth_codom enum_rankK. Qed.
          Lemma If_Nth_eq : I f = Nth.
          Proof. by rewrite Nth_If_eq. Qed.

          Definition NthToIf : Nth -> I f := (fun fn : Nth
            -> Nth => eq_rect_r (fun M : lmodType R => Nth -> M)
              fn If_Nth_eq) id.

          Definition IfToNth : I f -> Nth := (fun fn : Nth
            -> Nth => eq_rect_r (fun M : lmodType R => M -> Nth)
              fn If_Nth_eq) id.

          Lemma NthToIf_lin : linear NthToIf /\ linear IfToNth.
          Proof. split; by rewrite /NthToIf/IfToNth=>r x y; destruct If_Nth_eq. Qed.

          Lemma Nth_IfK : cancel NthToIf IfToNth /\ cancel IfToNth NthToIf.
          Proof. split; by rewrite/IfToNth/NthToIf; destruct (If_Nth_eq). Qed.

        Definition Nth_If := lmodIsomBuildPack NthToIf_lin Nth_IfK.

        End TypeConversion.
      
        Section Projection.
          Definition proj_raw : DS -> I f
          := Nth_If \oLin (@Seq.proj R F I (enum F) Ord).
          
          Lemma proj_lin : linear proj_raw.
          Proof. rewrite/proj_raw=> r x y; by rewrite !linearPZ. Qed.

          Definition proj : {linear DS -> I f} := Linear proj_lin.
          Lemma proj_unraw x : proj_raw x = proj x. Proof. by []. Qed.
        End Projection.
        
        Section Injection.
          Definition inj_raw : I f -> DS
          := (@Seq.inj R F I (enum F) Ord) \oLin inv(Nth_If).

          Lemma inj_lin : linear inj_raw.
          Proof. rewrite/inj_raw=> r x y; by rewrite !linearPZ. Qed.

          Lemma inj_injective : injective inj_raw.
          Proof. rewrite/inj_raw; unlock linConcat.map =>/= x y H.
            pose (A := Seq.inj_injective H).
            have : (Nth_If (inv(Nth_If) x) = Nth_If (inv(Nth_If) y))
            by simpl; rewrite A.
            by rewrite !(isomKl Nth_If).
          Qed.

          Definition inj : {linear I f -> DS} := Linear inj_lin.
          Lemma inj_unraw x : inj_raw x = inj x. Proof. by []. Qed.
        End Injection.
      End Components.

      Section Results.
        Lemma proj_injK (f : F) x : proj f (inj f x) = x.
        Proof. simpl;
          rewrite /proj_raw/inj_raw -!linCompChain.
          rewrite Seq.proj_injK; [rewrite -{2}(isomKf (Nth_If f) x) | apply cardElt].
          by rewrite /lmodIsom.isom_map/lmodIsom.isom_mapI.
        Qed.

        Lemma proj_inj0 (f f' : F) x : f != f' -> @proj f (@inj f' x) = 0.
        Proof. simpl.
          rewrite/proj_raw/inj_raw-(rwP negP)/not -!linCompChain=>H.
          case((nat_of_ord (enum_rank f) != enum_rank f')) as []eqn:E.
          rewrite (@Seq.proj_inj0_ofsize _ _ _ _ (Ord f) (Ord f') _ E).
          by rewrite linear0.
          assert (E' := contraFeq (fun B : enum_rank f != enum_rank f' => B) E).
          apply enum_rank_inj in E'.
          rewrite E' eq_refl in H.
          by assert (H' := H is_true_true).
        Qed.

        Lemma inj_proj_sum x : x = \sum_(f : F) inj f (proj f x).
        Proof.
          rewrite big_enum_val=>/=.
          rewrite {1}(Seq.inj_proj_sum x) -!big_enum  -cardT=>/=.
          refine (eq_bigr _ _).
          move=> i _; rewrite /inj_raw/proj_raw/Seq.inj/Seq.proj
          -!linCompChain (isomlK (Nth_If _))/Ord=>/=.
          by rewrite enum_valK.
        Qed.

        Lemma inj_proj_idem x : \sum_(f : F) inj f (proj f (\sum_(f : F) inj f (proj f x))) = \sum_(f : F) inj f (proj f x).
        Proof. by rewrite -inj_proj_sum. Qed.
      End Results.
    End Def.
    Section Bijection.
      Variable (F G : finType) (I : F -> lmodType R) (J : G -> lmodType R)
        (F_G : G -> F) (G_F : F -> G)
        (I_J : I = fun f => J (G_F f)) (J_I : J = fun g => I (F_G g))
        (Inj : cancel F_G G_F) (Surj : cancel G_F F_G) (enumB : enum F = map F_G (enum G)).
    End Bijection.

    Section Operations.
      Variable (F G H : finType) (I : F -> lmodType R)
        (F_GH : G + H -> F) (B : bijective F_GH)
        (enumB : enum F = map F_GH (enum (sum_finType G H))).

      Definition Jj : G -> F := fun g : G => F_GH (inl g).
      Definition Kk : H -> F := fun h : H => F_GH (inr h).

      Lemma enumF_cat : enum F = (map Jj (enum G)) ++ (map Kk (enum H)).
      Proof. rewrite enumB (enumT (sum_finType _ _))  (unlock _)=>/=.
      by rewrite /sum_enum/Jj/Kk -!map_comp map_cat -!map_comp.
      Qed.

      Definition J : G -> lmodType R := fun g : G => I (Jj g).
      Definition K : H -> lmodType R := fun h : H => I (Kk h).

      Definition cat_raw : DS I -> Seq.DS I ((map Jj (enum G)) ++ (map Kk (enum H))).
        by rewrite -enumF_cat.
      Defined.
      Definition uncat_raw : Seq.DS I ((map Jj (enum G)) ++ (map Kk (enum H))) -> DS I.
        by rewrite -enumF_cat.
      Defined.
      Lemma cat_lin : linear cat_raw /\ linear uncat_raw.
      Proof. split; rewrite/cat_raw/uncat_raw=>r x y;
      by destruct enumF_cat. Qed.
      Lemma catK : cancel cat_raw uncat_raw /\ cancel uncat_raw cat_raw.
      Proof. split; rewrite/cat_raw/uncat_raw=>x;
      by destruct enumF_cat. Qed.
      Definition cat := lmodIsomBuildPack cat_lin catK.
(*
      Definition unspl : (DS J) \oplus (DS K) -> (Seq.DS I (map Jj (enum G)) \oplus (Seq.DS I (map Kk (enum H)))).
        rewrite /J/K/Jj/Kk/DS.
        induction (enum G)=>//x.
        induction (enum H)=>//=.
        apply (x.1, (x.2.1, (IHl (x.1,x.2.2)).2)).
        apply((x.1.1, (IHl (x.1.2, x.2)).1), (IHl (x.1.2, x.2)).2).
      Defined.

      Definition unspl2 : (Seq.DS I (map Jj (enum G)) \oplus (Seq.DS I (map Kk (enum H)))) -> (DS J) \oplus (DS K).
        rewrite /J/K/Jj/Kk/DS.
        induction (enum G)=>//x.
        induction (enum H)=>//=.
        apply (x.1, (x.2.1, (IHl (x.1,x.2.2)).2)).
        apply((x.1.1, (IHl (x.1.2, x.2)).1), (IHl (x.1.2, x.2)).2).
      Defined.
      Lemma unspl_lin : linear unspl /\ linear unspl2.
      Proof.
        split; rewrite/unspl/unspl2/list_rect=>r x y/=.
      Admitted.
      
      Lemma unsplK : cancel unspl unspl2 /\ cancel unspl2 unspl.
      Proof. 
        split; rewrite/unspl/unspl2/list_rect=>x/=.
      by destruct enumF_cat. Qed.
*)
      Definition split : {linear DS I -> DS J \oplus DS K}
       := Pair.diag
            (inv(Seq.hom I Jj _))
            (inv(Seq.hom I Kk _))
          \oLin (Seq.split I _ _) \oLin cat.

      Definition unsplit : {linear DS J \oplus DS K -> DS I}
      := inv(cat) \oLin (Seq.unsplit I _ _) \oLin
        Pair.diag
          (Seq.hom I Jj _)
          (Seq.hom I Kk _).
(*
      Lemma split_lin : linear split_raw.
        Proof. rewrite /split_raw=>r x y; by rewrite !linearP.
      Qed.

      Lemma unsplit_lin : linear unsplit_raw.
        Proof. rewrite /unsplit_raw=>r x y.
        destruct x, y.
        rewrite linearP.
        rewrite linearP.
        rewrite Seq.unsplit_lin.
      Qed.
  *)      
      (*
      Definition split_raw : DS I -> DS J \oplus DS K
(*       := Seq.split I (map Jj (enum G)) (map Kk (enum H)).
         := fun x => (Seq.split (fun gh => I (F_GH gh)) (map (@inl G H) (enum G)) (map (@inr G H) (enum H)) x).
 *)    := fun x =>
         (\sum_(g : G)(inj J g) (proj I (F_GH (inl g)) x),
          \sum_(h : H)(inj K h) (proj I (F_GH (inr h)) x)).

      Definition unsplit_raw : DS J \oplus DS K -> DS I
        := fun x =>
          \sum_(g : G) inj I (F_GH (inl g)) (proj J g x.1) +
          \sum_(h : H) inj I (F_GH (inr h)) (proj K h x.2).
      
      Lemma split_lin : linear split_raw.
      Proof. rewrite/split_raw=>r x y.
        rewrite (rwP eqP)/eq_op -(rwP andP) -!(rwP eqP).
        (have:forall p1 p2, (p1,p2).1 = p1 by []);
        (have:forall p1 p2, (p1,p2).2 = p2 by [])=> H2 H1.
        rewrite !H1 !H2
        !(eq_bigr _ (fun i _ => linCompChain _ _ _))
        !(eq_bigr _ (fun i _ => linearP _ _ _ _));
        by rewrite !scaler_sumr !big_split.
      Qed.

      Lemma unsplit_lin : linear unsplit_raw.
      Proof. rewrite/unsplit_raw=>r x y.
        rewrite !(eq_bigr _ (fun i _ => linCompChain _ _ _))
        !(eq_bigr _ (fun i _ => linearP _ _ _ _))
        !big_split  -!scaler_sumr.
        by rewrite scalerDr !addrA (addrC _ (r *: _)) !addrA (addrC (r *: _) (r *: _)).
      Qed.

      Definition split := Linear split_lin.
      Definition unsplit := Linear unsplit_lin.*)
  
      Lemma unsplitK : cancel split unsplit.
      Proof. rewrite /unsplit/split=>x.
      rewrite -!linCompChain.
      rewrite (linCompChain (_ \linPlusDiag _) (_ \linPlusDiag _)). Admitted.
      
      Lemma splitK : cancel unsplit split.
      Proof. rewrite /unsplit/split=>x.
      rewrite -!linCompChain isomKl Seq.splitKs.
      Admitted.
  (*
      Lemma split_unsplitK : cancel split unsplit.
        Proof.destruct B=>/=.
        rewrite /unsplit_raw/split_raw/J/K=>x.
        rewrite !(eq_bigr _ (fun i _ => linCompChain _ _ _))
         !(eq_bigr _ (fun i _ => linear_sum _ _ _ _))
         !pair_bigA/Ord.
        rewrite (eq_bigr (fun p : G*G => if p.2 == p.1 then
          Seq.inj _ _ (enum_rank (F_GH (inl p.1)))
            (Seq.proj _ _ (enum_rank (F_GH (inl p.1))) x)
            else 0) _).
        rewrite (eq_bigr (fun p : H*H => if p.2 == p.1 then
          Seq.inj _ _ (enum_rank (F_GH (inr p.1)))
            (Seq.proj _ _ (enum_rank (F_GH (inr p.1))) x)
            else 0) _).
        {
          rewrite -!big_mkcond {3}(inj_proj_sum x)
          big_pair_diag_eq big_pair_diag_eq=>/=.
          rewrite (@reindex _ _ _ _ _ F_GH _ (fun f => inj _ _ (proj _ f x)))=>/=.
          rewrite /inj_raw/proj_raw/Ord big_sumType=>/=; symmetry.
          rewrite (eq_bigr (fun i : G => Seq.inj _ _ _ (Seq.proj _ _ (enum_rank (F_GH (inl i))) x)) _); [|move=>p _; by rewrite -!linCompChain (isomlK (Nth_If _ _))];
          by rewrite (eq_bigr (fun i : H => Seq.inj _ _ _ (Seq.proj _ _ (enum_rank (F_GH (inr i))) x)) _); [|move=>p _; by rewrite -!linCompChain (isomlK (Nth_If _ _))].
          apply (onW_bij _ B).
        }
        move=>p _; case (p.2 == p.1) as []eqn:E.
        apply (rwP eqP) in E.
        rewrite E /inj_raw/proj_raw/Seq.inj/Seq.proj -!linCompChain
        Seq.proj_injK;
        [ by rewrite (isomKl (Nth_If _ _))(isomlK (Nth_If _ _))|
          by destruct (enum_rank p.2)=>/=; rewrite -cardE].
        rewrite /inj_raw/proj_raw/Seq.inj/Seq.proj -!linCompChain.
        rewrite Seq.proj_inj0;
        [by rewrite !linear0|
          destruct (enum_rank p.2)=>/=; by rewrite -cardE|
          destruct (enum_rank p.2)=>/=; by rewrite -cardE|].
        rewrite -(rwP negP)/not-(rwP eqP)=>N.
        have/eqP X: enum_rank p.1 == enum_rank p.2
        by rewrite /eq_op; apply/eqP.
        by rewrite (enum_rank_inj X) eq_refl in E.

        move=>p _; case (p.2 == p.1) as []eqn:E.
        apply (rwP eqP) in E.
        rewrite E /inj_raw/proj_raw/Seq.inj/Seq.proj -!linCompChain
        Seq.proj_injK;
        [ by rewrite (isomKl (Nth_If _ _))(isomlK (Nth_If _ _))|
          by destruct (enum_rank p.2)=>/=; rewrite -cardE].
        rewrite /inj_raw/proj_raw/Seq.inj/Seq.proj -!linCompChain Seq.proj_inj0;
          [by rewrite !linear0|
            destruct (enum_rank p.2)=>/=; by rewrite -cardE|
            destruct (enum_rank p.2)=>/=; by rewrite -cardE|].
        rewrite -(rwP negP)/not-(rwP eqP)=>N.
        have/eqP X : enum_rank p.1 == enum_rank p.2
        by rewrite /eq_op; apply/eqP.
        by rewrite (enum_rank_inj X) eq_refl in E.
      Qed.
 
      Lemma enum_rank_GH_lt_F (gh : G + H) : enum_rank (F_GH gh) < size (enum F).
      Proof.
        rewrite enumB size_map/enum_rank/enum_rank_in/insubd/odflt/oapp/insub.
        destruct(idP).
        assert(ii := i).
        by rewrite cardT {2}enumB size_map in ii.
        rewrite -cardT -(rwP (card_gt0P _)).
        apply(ex_intro _ gh is_true_true).
      Qed.

      Lemma unsplit_splitK : cancel unsplit split.
      Proof.
      destruct B=>/=.
      rewrite /unsplit_raw/split_raw=>x.
      rewrite (eq_bigr (fun g : G =>
          inj J g (proj I (F_GH (inl g)) (\sum_g1
            inj I (F_GH (inl g1)) (proj J g1 x.1)))
        + inj J g (proj I (F_GH (inl g)) (\sum_h
            inj I (F_GH (inr h)) (proj K h x.2)))) _);
        [rewrite big_split|move=>p _; by rewrite !raddfD].
      rewrite (eq_bigr (fun h : H =>
          inj K h (proj I (F_GH (inr h)) (\sum_g1
            inj I (F_GH (inl g1)) (proj J g1 x.1)))
        + inj K h (proj I (F_GH (inr h)) (\sum_h
        inj I (F_GH (inr h)) (proj K h x.2)))) _);
        [rewrite big_split|move=>p _; by rewrite !raddfD].
      
      rewrite !(eq_bigr _ (fun i _ => linear2_sum _ _ _)) !pair_bigA.
      destruct x as [x1 x2].
      rewrite {5}(inj_proj_sum x1) {5}(inj_proj_sum x2).
      rewrite (eq_bigr (fun p : G*G
      => if(p.2 == p.1)
      then inj J p.1 (proj J p.1 x1)
      else 0)).
      rewrite (eq_bigr (fun p : H*H
      => if(p.2 == p.1)
      then inj K p.1 (proj K p.1 x2)
      else 0)).
      {
        rewrite (eq_bigr (fun _ : G*H => 0)).
          rewrite big_const cardE /iter enumT;
          induction(Finite.enum _)=>//=; [rewrite addr0| by rewrite add0r IHl].
        rewrite (eq_bigr (fun _ : H*G => 0)).
          rewrite big_const cardE /iter enumT;
          induction(Finite.enum _)=>//=; [rewrite add0r| by rewrite add0r IHl].
        by rewrite -!big_mkcond !big_pair_diag_eq.

        move=>hg _.
        rewrite !inj_unraw !proj_unraw proj_inj0; [by rewrite !linear0|].
        rewrite /Ord -(rwP negP)/not -(rwP eqP)=>/=N.
        have: (enum_rank (F_GH (inr hg.1)) = enum_rank (F_GH (inl hg.2)))
        by rewrite (rwP eqP)/eq_op=>/=; rewrite N. clear N=>N.
        assert(V := f_equal g (enum_rank_inj N)).
        rewrite !H0 in V.
        by inversion V.

        
        move=>gh _.
        rewrite proj_inj0; [by rewrite !linear0|].
        rewrite /Ord -(rwP negP)/not -(rwP eqP)=>/=N.
        have: (enum_rank (F_GH (inl gh.1)) = enum_rank (F_GH (inr gh.2)))
        by rewrite (rwP eqP)/eq_op=>/=; rewrite -N. clear N=>N.
        assert(V := f_equal g (enum_rank_inj N)).
        rewrite !H0 in V.
        by inversion V.
      }
      all:move=>p _; case (p.2 == p.1) as []eqn:E; [
        by apply (rwP eqP) in E;
        rewrite E proj_injK
        |  ];
        rewrite  proj_inj0; [by rewrite !linear0|];
        rewrite /Ord -(rwP negP)/not -(rwP eqP)=>/=N.

      have: (enum_rank (F_GH (inr p.1)) = enum_rank (F_GH (inr p.2)))
      by rewrite (rwP eqP)/eq_op=>/=; rewrite -N. clear N=>N.
      assert(V := f_equal g (enum_rank_inj N));
      rewrite !H0 in V;
      inversion V;
      by rewrite H3 eq_refl in E.

      have: (enum_rank (F_GH (inl p.1)) = enum_rank (F_GH (inl p.2)))
        by rewrite (rwP eqP)/eq_op=>/=; rewrite -N. clear N=>N.
      assert(V := f_equal g (enum_rank_inj N));
      rewrite !H0 in V;
      inversion V;
      by rewrite H3 eq_refl in E.
    Qed.*)
    End Operations.

  End General.
End dsLmod.

Definition dsProj (R : ringType) (F : finType) (I : F -> (lmodType R)) (f : F) := @dsLmod.proj R F I f.
Definition dsInj (R : ringType) (F : finType) (I : F -> (lmodType R)) (f : F) := @dsLmod.inj R F I f.




Export dsLmod.Pair.Exports.
Notation "\bigoplus_ i F" := (dsLmod.DS (fun i => F i)) : lmod_scope.
Notation "\bigoplus F" := (dsLmod.DS F) : lmod_scope.
Notation "\bigoplus_ ( i : t ) F" := (dsLmod.DS (fun i : t => F i)) : lmod_scope.
Notation "\bigoplus_ ( i 'in' A ) F" := (dsLmod.Seq.DS (filter F (fun i => i \in A))) : lmod_scope.
Notation "\proj^( I )_ f " := (dsLmod.proj I f ) : lmod_scope.
Notation "\inj^( I )_ f " := (dsLmod.inj I f ) : lmod_scope.
Notation "\proj_ f ^( I )" := (dsLmod.proj I f ) : lmod_scope.
Notation "\inj_ f ^( I )" := (dsLmod.inj I f ) : lmod_scope.

Theorem DS_cat_theory (R : ringType) (F : finType)
  (I : F -> (lmodType R))
    : forall (f : forall i : F, {linear \bigoplus I -> (I i)}), 
      exists (g : forall i : F, {linear (I i) -> (I i)}),
        forall i : F, f i \oLin \inj_i^(I) = g i.
Proof. move=> f.
  by refine(ex_intro _ (fun i => f i \oLin \inj_i^(I)) _ ).
Qed.

Close Scope  lmod_scope.
Close Scope  ring_scope.