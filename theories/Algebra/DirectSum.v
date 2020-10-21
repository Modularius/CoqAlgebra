(******************************************************************************)
(**)
(******************************************************************************)
(*         M1 \oplus M2 == the lmodType given by pair_lmodType in ssralg.v    *)
(*                         This is an implementation of the direct sum of two *)
(*                         lmodTypes of the same ring.                        *)
(* \bigoplus_(f in L) I == the lmodType built up iteratively, where L : seq S *)
(*                         for S : eqType and I : S -> lmodType R             *)
(*                         \bigoplus_(f in nil) I is lmodNull R whilst        *)
(*                         \bigoplus_(f in a::L) I is                         *)
(*                               (I a) \oplus (\bigoplus_(f in L) I)          *)
(*                         This is an implementation of the direct sum of an  *)
(*                         arbitrary number of lmodTypes. Note that L is not  *)
(*                         a list of lmodTypes but of some eqType S, which    *)
(*                         are 'converted' to lmodTypes by                    *)
(*                           I : S -> lmodType R.                             *)
(*  \bigoplus_(f : F) I == the lmodType equal to \bigoplus_(f in (enum F)) I  *)
(*        \bigoplus_F I == equivalent to \bigoplus_(f : F) I                  *)
(*          \bigoplus I == equivalent to \bigoplus_(f : F) I                  *)
(*                         where I : F -> lmodType R                          *)
(******************************************************************************)
(* The following constructions and lemmas relate to M1 \oplus M2,             *)
(* the direct sum of the pair of lmodTypes M1 and M2                          *)
(******************************************************************************)
(*  \proj1^(M1,M2)   == the linear projection from M1 \oplus M2 to M1         *)
(*  \proj2^(M1,M2)   == the linear projection from M1 \oplus M2 to M2         *)
(*  \incl1^(M1,M2)   == the linear inclusion from M1 to M1 \oplus M2          *)
(*  \incl2^(M1,M2)   == the linear inclusion from M2 to M1 \oplus M2          *)
(*  incl1_injective  == a proof that \incl1^(M1,M2) is injective              *)
(*  incl2_injective  == a proof that \incl2^(M1,M2) is injective              *)
(*  proj1_incl1K     == a proof of \proj1^(M1,M2) (\incl1^(M1,M2) x = x       *)
(*  proj2_incl2K     == a proof of \proj2^(M1,M2) (\incl2^(M1,M2) x = x       *)
(*  proj1_incl20     == a proof of \proj1^(M1,M2) (\incl2^(M1,M2) x = 0       *)
(*  proj2_incl10     == a proof of \proj2^(M1,M2) (\incl1^(M1,M2) x = 0       *)
(*  incl_proj12_sum  == a proof that any x : M1 \oplus M2 can be written      *)
(*                         x = \incl1^(U,V) (proj1^(U,V) x)                   *)
(*                              + \incl2^(U,V) (proj2^(U,V) x)                *)
(*  incl_proj12_idem == a proof that rewriting with incl_proj12_sum is        *)
(*                         idempotent                                         *)
(******************************************************************************)
(* The following constructions and lemmas relate to \bigoplus_(f : F) I,      *)
(* the direct sum of the lmodTypes given by (I : F -> lmodType R), and F is a *)
(* finite index set (i.e. a finType)                                          *)
(******************************************************************************)
(*  \proj_f^(I)    == the linear projection from \bigoplus I to (I f),        *)
(*                 for f : F. This function is surjective                     *)
(*  \incl_f^(I)    == the linear inclusion from (I f) to \bigoplus I,         *)
(*                 for f : F. This function is injective                      *)
(*  incl_injective == a proof that \incl_f^(I) is injective for f : F         *)
(*  proj_inclK     == a proof that \incl_f^(I) and \proj_f^(I) cancel         *)
(*  proj_incl0     == a proof that \incl_f^(I) and \proj_(f')^(I) equals zero *)
(*                    if f != f'                                              *)
(*  incl_proj_sum  == rewrites element x : \bigoplus I as                     *)
(*                        \sum_(f : F)\incl_f^(I) (\proj_f^(I) x)             *)
(*  incl_proj_idem       ==  a proof that rewriting with incl_proj_sum is     *)
(*                         idempotent                                         *)
(******************************************************************************)
(* The following constructions are used to split and unsplit the direct sum   *)
(* of two direct sums, that is (\bigoplus J) \oplus (\bigoplus K).            *)
(* Doing this involves:                                                       *)
(*  1) three index sets F, G and H,                                           *)
(*  2) a function GH_F : G + H -> F, connecting the sum of G and H to F       *)
(*  3) a proof enumB : enum F = map F_GH (enum sum_finType G H) which         *)
(* establishes that GH_F is an 'isomorphism' of G + H and F as finTypes,      *)
(* and the notations J = I \o GH_F \o inl and K = I \o GH_F \o inr.           *)
(******************************************************************************)
(*     split == a linear function from \bigoplus I to                         *)
(*                    (\bigoplus J) \oplus (\bigoplus K)                      *)
(*   unsplit == a linear function from (\bigoplus J) \oplus (\bigoplus K)     *)
(*                    to \bigoplus I                                          *)
(*  splitK   == a proof that split and unsplit cancel                         *)
(*  unsplitK == a proof that unsplit and split cancel                         *)
(******************************************************************************)

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
    (*Lemma linear2_sum :
    g (f (\sum_(i : Ty) (x i))) = \sum_(i : Ty) g (f (x i)).
    Proof. by rewrite !linear_sum. Qed.*)
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

      Lemma diag_id : diag (\id_M1) (\id_M2) = \id_(pair_lmodType M1 M2).
      Proof.
        rewrite linear_eq.
        apply functional_extensionality=>x/=.
        by rewrite /diag_raw /linID.map -!(lock) -(inj_proj_sum x).
      Qed.

      Lemma diag_comp : (diag g1 g2) \oLin (diag f1 f2) = diag (g1 \oLin f1) (g2 \oLin f2).
      Proof.
        rewrite linear_eq.
        apply functional_extensionality=>x.
        rewrite -!linCompChain=>/=.
        rewrite /diag_raw -!linCompChain=>/=.
        by rewrite addr0 add0r.
      Qed.
    End MorphismsDiag.


    Module Exports.

      Notation lmodDSPairType := pair_lmodType.
      Infix "\oplus" := (pair_lmodType) (at level 35).
      Notation "\diagmap( f , g )" := (diag f g) (at level 35).
      Notation "\rowmap( f , g )" := (from_ds f g) (at level 35).
      Notation "\colmap( f , g )" := (to_ds f g) (at level 35).
    End Exports.
  End Pair.
  Export Pair.Exports.



  Module Seq.
    Section Ring.
      Variable (R : ringType).
      Section Environment.
        Variable (T : eqType) (I : T -> lmodType R).

        Section Def.
          Definition Nth := (fun L n => match (seq.nth None (map Some L) n) with
          |Some t => I t
          |None => lmodZero.type R
          end).

          Fixpoint DS (L : seq T) : lmodType R := match L with
            |nil => lmodZero.type R
            |a'::L' => (I a') \oplus (DS L')
          end.
        End Def.

        Section Submodule.
          Variable (L : seq T) (n : 'I_(size L)).
          (* Todo *)
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
          Proof. move: n; induction L=>//=. {
            induction n=>//=. }
            move : L IHL; induction n=>//= r x y.
            apply (linearP (@Pair.inj1 _ (I a) (DS L))).
            by rewrite -(linearP (@Pair.inj2 _ (I a) (DS L))) (IHL n).
          Qed.

          Lemma inj_injective
            (L : seq T) (n : nat) : injective (@inj_raw L n).
          Proof. move: n; induction L=>//=.
          { induction n; by move=> x y; destruct x, y. }
            move: L IHL.
            induction n=>/= x y H.
            apply (@Pair.inj1_injective R _ _ x y H).
            apply (IHL n x y (@Pair.inj2_injective R _ _ (@inj_raw L n x) (@inj_raw L n y) H)).
          Qed.
        End Injection.
        Definition inj (L : seq T) (n : nat)
          := Linear (@inj_lin L n).

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
          Proof. move: n; induction L=>//=. { induction n=>//=. }
            move: L IHL; induction n=>//=; move=> r x y.
            by rewrite !Pair.proj2_unraw linearP -(IHL n).
          Qed.
        End Projection.
        Definition proj (L : seq T) (n : nat)
          := Linear (@proj_lin L n).

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
            induction L=>//; destruct n as [n N]=>//.
            induction n=>//; move:x; simpl (Ordinal N : nat)=>x.
            rewrite -ltn_predRL in N.
            by rewrite proj_inj_cons (IHl (Ordinal N)).
          Qed.

          Lemma proj_inj0_ofsize (n n' : 'I_(size L)) x : (nat_of_ord n) != n' -> @proj L n (@inj L n' x) = 0.
          Proof.
            induction L; destruct n as [n N], n' as [n' N']=>//.
            simpl in x, IHl, N, N'=>H.
            induction n.
              apply (rwP negP) in H.
              by induction n'=>/=; [contradiction H|].
            induction n'=>//=.
              by (have: proj l n 0 = 0 by rewrite linear0).
            clear IHn' IHn;
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

            Definition catifyL1 : linIsomType (Nth (L1 ++ L2) n) (Nth L1 n)
            := linIsomBuildPack catTrApR_lin catApTrRK.
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

            Definition catifyL2 : linIsomType (Nth (L1 ++ L2) (rshift (size L1) n)) (Nth L2 n)
            := linIsomBuildPack catTrApL_lin catApTrLK.
          End L2.

          Definition split_raw : DS (L1 ++ L2) -> DS L1 \oplus DS L2
            := fun x =>
            (\sum_(n < size L1)(inj L1 n \oLin catifyL1 n \oLin proj (L1 ++ L2) n ) x,
            \sum_(n < size L2)(inj L2 n \oLin catifyL2 n \oLin proj (L1 ++ L2) (rshift (size L1) n)) x).

          Definition unsplit_raw : DS L1 \oplus DS L2 -> DS (L1 ++ L2)
          := fun x =>
            \sum_(n < size L1)((inj (L1 ++ L2) n                     \oLin inv(catifyL1 n) \oLin proj L1 n) x.1) +
            \sum_(n < size L2)((inj (L1 ++ L2) (rshift (size L1) n)  \oLin inv(catifyL2 n) \oLin proj L2 n) x.2).

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

          Lemma unsplitK : cancel split unsplit.
          Proof. simpl; rewrite /unsplit_raw/split_raw=>x.
            under eq_bigr do rewrite linear_sum.
            under eq_bigr do under eq_bigr do rewrite -!linCompChain.
            under[\sum_(_ < size L2) _] eq_bigr do rewrite linear_sum.
            under[\sum_(_ < size L2) _] eq_bigr do under eq_bigr do rewrite -!linCompChain.
            rewrite!pair_bigA.
            rewrite (eq_bigr (fun p : 'I_(size L1)*'I_(size L1)
            => if p.2 == p.1
              then inj _ p.1 (proj _ p.1 x)
              else 0 ) _).
            rewrite (eq_bigr (fun p : 'I_(size L2)*'I_(size L2)
              => if p.2 == p.1
              then inj _ (rshift (size L1) p.2) (proj _ (rshift (size L1) p.2) x)
              else 0 ) _).
            by rewrite -!big_mkcond !big_pair_diag_eq {3}(@inj_proj_sum _ x)
            size_cat (@big_split_ord _ _ _ (size L1) (size L2)).
            by move=>p _; case (p.2 == p.1) as []eqn:E;
            [apply (rwP eqP) in E; rewrite E proj_injK_ofsize (isomlK (catifyL2 p.1)) |
            rewrite proj_inj0_ofsize; [rewrite !linear0|
              rewrite eq_sym/eq_op in E; simpl in E; rewrite E]].
            by move=>p _; case (p.2 == p.1) as []eqn:E;
            [ apply (rwP eqP) in E; rewrite E proj_injK_ofsize (isomlK (catifyL1 p.1))|
            rewrite proj_inj0_ofsize; [rewrite !linear0|
              rewrite eq_sym/eq_op in E; simpl in E; rewrite E]].
          Qed.

          Lemma splitK : cancel unsplit split.
          Proof. simpl; rewrite /unsplit_raw/split_raw=>x.
          under eq_bigr do rewrite !raddfD.
          under[\sum_(n < _) ((_ \oLin _ \oLin proj _ (rshift _ n)) _)]
            eq_bigr do rewrite !raddfD.

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

        Fixpoint homify_raw (L : seq S) : DS (I \o T_S) L -> DS I (map T_S L)
          := match L with
          |nil => id
          |a::l => fun x => (x.1 , homify_raw x.2)
          end.
        Fixpoint unhomify_raw (L : seq S) : DS I (map T_S L) -> DS (I \o T_S) L
          := match L with
          |nil => id
          |a::l => fun x => (x.1 , unhomify_raw x.2)
          end.
        
        Variable (L : seq S).
        Lemma homify_lin : linear (@homify_raw L) /\ linear (@unhomify_raw L).
        Proof. split; induction L=>//=r x y;
          by rewrite IHl/homify_raw/unhomify_raw.
        Qed.
        Lemma homifyK : cancel (@homify_raw L) (@unhomify_raw L) /\ cancel (@unhomify_raw L) (@homify_raw L).
        Proof. split; induction L=>//=x; destruct x;
          by rewrite IHl.
        Qed.
        Definition homify := linIsomBuildPack homify_lin homifyK.
      End Hom.

      Section Bijection.
        Variable (S T : eqType) (I : T -> lmodType R)
            (T_S : S -> T) (S_T : T -> S) (Inj : cancel S_T T_S).

        Variable (L : seq T).
        Definition mapify_raw : DS I (map T_S (map S_T L)) -> DS I L.
        by rewrite mapK. Defined.      
        Definition unmapify_raw : DS I L -> DS I (map T_S (map S_T L)).
        by rewrite mapK. Defined.
        Lemma mapify_lin : linear mapify_raw /\ linear unmapify_raw.
        Proof. split; by rewrite/mapify_raw/unmapify_raw; destruct mapK. Qed.
        Lemma mapifyK : cancel mapify_raw unmapify_raw /\ cancel unmapify_raw mapify_raw.
        Proof. split; by rewrite/mapify_raw/unmapify_raw; destruct mapK. Qed.
        Definition mapify := linIsomBuildPack mapify_lin mapifyK.

        Definition bijectify := linIsomConcat (homify I T_S (map S_T L)) mapify.
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
          Proof. by rewrite /Nth/Seq.Nth -codomE nth_codom enum_rankK. Qed.
          Lemma If_Nth_eq : I f = Nth.
          Proof. by rewrite Nth_If_eq. Qed.

          Definition finify_raw : Nth -> I f := (fun fn : Nth
            -> Nth => eq_rect_r (fun M : lmodType R => Nth -> M)
              fn If_Nth_eq) id.
          Definition unfinify_raw : I f -> Nth := (fun fn : Nth
            -> Nth => eq_rect_r (fun M : lmodType R => M -> Nth)
              fn If_Nth_eq) id.
          Lemma finify_lin : linear finify_raw /\ linear unfinify_raw.
          Proof. split; by rewrite /finify_raw/unfinify_raw=>r x y; destruct If_Nth_eq. Qed.
          Lemma finifyK : cancel finify_raw unfinify_raw /\ cancel unfinify_raw finify_raw.
          Proof. split; by rewrite/finify_raw/unfinify_raw; destruct If_Nth_eq. Qed.

          Definition finify := linIsomBuildPack finify_lin finifyK.

        End TypeConversion.
      
        Section Projection.
          Definition proj_raw : DS -> I f
          := finify \oLin (@Seq.proj R F I (enum F) Ord).
          
          Lemma proj_lin : linear proj_raw.
          Proof. rewrite/proj_raw=> r x y; by rewrite !linearPZ. Qed.

          Definition proj : {linear DS -> I f} := Linear proj_lin.
        End Projection.
        
        Section Injection.
          Definition inj_raw : I f -> DS
          := (@Seq.inj R F I (enum F) Ord) \oLin inv(finify).

          Lemma inj_lin : linear inj_raw.
          Proof. rewrite/inj_raw=> r x y; by rewrite !linearPZ. Qed.

          Lemma inj_injective : injective inj_raw.
          Proof. rewrite/inj_raw=>x y; rewrite -!linCompChain=>H.
            apply Seq.inj_injective in H.
            apply (congr1 finify) in H.
            by rewrite !isomKl in H.
          Qed.

          Definition inj : {linear I f -> DS} := Linear inj_lin.
        End Injection.
      End Components.

      Section Results.
        Lemma proj_injK (f : F) x : proj f (inj f x) = x.
        Proof. by rewrite /proj_raw/inj_raw -!linCompChain
          Seq.proj_injK; [rewrite -{2}(isomKf (finify f) x) | apply cardElt].
        Qed.

        Lemma proj_inj0 (f f' : F) x : f != f' -> @proj f (@inj f' x) = 0.
        Proof.
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
          rewrite big_enum_val.
          rewrite {1}(Seq.inj_proj_sum x) -!big_enum  -cardT.
          refine (eq_bigr _ _).
          move=> i _; rewrite /inj_raw/proj_raw/Seq.inj/Seq.proj
          -!linCompChain (isomlK (finify _))/Ord=>/=.
          by rewrite enum_valK.
        Qed.

        Lemma inj_proj_idem x : \sum_(f : F) inj f (proj f (\sum_(f : F) inj f (proj f x))) = \sum_(f : F) inj f (proj f x).
        Proof. by rewrite -inj_proj_sum. Qed.
      End Results.
    End Def.
    Section Hom.
(*      Variable (F G : finType) (I : F -> lmodType R) (J : G -> lmodType R)
      (J = I \o F_G)
      (F_G : G -> F) (enumB : enum F = map F_G (enum G)).

      Definition enumify_raw : Seq.DS I (map F_G (enum G)) -> DS I.
      by rewrite /DS enumB. Defined.
      Definition unenumify_raw : DS I -> Seq.DS I (map F_G (enum G)).
      by rewrite /DS enumB. Defined.
      Lemma enumify_lin : linear enumify_raw /\ linear unenumify_raw.
      Proof. split; rewrite /enumify_raw/unenumify_raw; by destruct enumB. Qed.
      Lemma enumifyK : cancel enumify_raw unenumify_raw /\ cancel unenumify_raw enumify_raw .
      Proof. split; rewrite /enumify_raw/unenumify_raw; by destruct enumB. Qed.
      Definition enumify := linIsomBuildPack enumify_lin enumifyK.

      Definition homify : {linear DS (I \o F_G) -> DS I}
      := enumify \oLin (@Seq.homify _ _ _ I F_G (enum G)).
      Definition unhomify : {linear DS I -> DS (I \o F_G)}
      := inv(@Seq.homify _ _ _ I F_G (enum G)) \oLin inv(enumify).*)
    End Hom.
    Section Bijection.
    (*
      Variable (F G : finType) (I : F -> lmodType R) (J : G -> lmodType R)
        (F_G : G -> F) (G_F : F -> G)
        (I_J : I = J \o G_F) (J_I : J = I \o F_G)
        (Inj : cancel F_G G_F) (Surj : cancel G_F F_G) (enumB : enum F = map F_G (enum G)).


        Definition mapify_raw : DS (I \o S_T \o T_S) -> DS I.
        by rewrite mapK. Defined.      
        Definition unmapify_raw : DS I L -> DS I (map T_S (map S_T L)).
        by rewrite mapK. Defined.
        Lemma mapify_lin : linear mapify_raw /\ linear unmapify_raw.
        Proof. split; by rewrite/mapify_raw/unmapify_raw; destruct mapK. Qed.
        Lemma mapifyK : cancel mapify_raw unmapify_raw /\ cancel unmapify_raw mapify_raw.
        Proof. split; by rewrite/mapify_raw/unmapify_raw; destruct mapK. Qed.
        Definition mapify := linIsomBuildPack mapify_lin mapifyK.

        Definition bijectify := linIsomConcat (homify I T_S (map S_T L)) mapify.*)
    End Bijection.

    Section Operations.
      Variable (F G H : finType) (I : F -> lmodType R)
        (F_GH : G + H -> F)
        (enumB : enum F = map F_GH (enum (sum_finType G H))).

      Definition Jj : G -> F := F_GH \o inl.
      Definition Kk : H -> F := F_GH \o inr.
      Definition J : G -> lmodType R := I \o Jj.
      Definition K : H -> lmodType R := I \o Kk.

      Lemma enumF_cat : enum F = (map Jj (enum G)) ++ (map Kk (enum H)).
      Proof. rewrite enumB (enumT (sum_finType _ _))  (unlock _)=>/=.
      by rewrite /sum_enum/Jj/Kk -!map_comp map_cat -!map_comp.
      Qed.

      Definition catify_raw : DS I -> Seq.DS I ((map Jj (enum G)) ++ (map Kk (enum H))).
        by rewrite -enumF_cat.
      Defined.
	    Definition uncatify_raw : Seq.DS I ((map Jj (enum G)) ++ (map Kk (enum H))) -> DS I.
        by rewrite -enumF_cat.
      Defined.
      
      Lemma catify_lin : linear catify_raw /\ linear uncatify_raw.
        Proof. split; rewrite/catify_raw/uncatify_raw=>r x y;
        by destruct enumF_cat. Qed.
      Lemma catifyK : cancel catify_raw uncatify_raw /\ cancel uncatify_raw catify_raw.
        Proof. split; rewrite/catify_raw/uncatify_raw=>x;
        by destruct enumF_cat. Qed.
      
	    Definition catify := linIsomBuildPack catify_lin catifyK.

      Definition split : {linear DS I -> DS J \oplus DS K}
       := \diagmap(inv(Seq.homify _ Jj _), inv(Seq.homify _ Kk _))
			      \oLin (Seq.split I _ _) \oLin catify.

      Definition unsplit : {linear DS J \oplus DS K -> DS I}
      := inv(catify) \oLin (Seq.unsplit I _ _) \oLin
          \diagmap(Seq.homify _ Jj _, Seq.homify _ Kk _).

      Lemma unsplitK : cancel split unsplit.
      Proof. rewrite /unsplit/split=>x.
        by rewrite -!linCompChain (linCompChain (\diagmap(_,_)) (\diagmap(_,_)))
        Pair.diag_comp !linIsom.concatKl Pair.diag_id -linIDChain
        Seq.unsplitK (isomlK catify).
      Qed.
      
      Lemma splitK : cancel unsplit split.
      Proof. rewrite /unsplit/split=>x.
        by rewrite -!linCompChain isomKl Seq.splitK
        (linCompChain (\diagmap(_,_)) (\diagmap(_,_)))
        Pair.diag_comp !linIsom.concatlK Pair.diag_id -linIDChain.
      Qed.

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