Require Import Program.
From Coq.Logic Require Import ProofIrrelevance FunctionalExtensionality.

From mathcomp Require Import ssreflect ssrfun.
From mathcomp Require Import eqtype path choice seq fintype.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
From mathcomp Require Import ssrbool ssrnat.
Set Warnings "parsing".

Require Import Quiver.

Set Implicit Arguments.
Unset Strict Implicit.

Module NTPath.
  Local Notation EG := Quiver.EdgeGraph.
  Section Def.
    Variable (Q : finQuiverType).

    Definition predicate : pred _ := (fun ty  => path (EG Q) ty.1 ty.2).
    Definition type := { ty | predicate ty}.
    
    Definition type2tail (p : type) := (sval p).1.
    Definition type2deTail (p : type) := (sval p).2.
    Definition type2path (p : type) := (proj2_sig p).
    Definition type2head (p : type) := (seq.last (type2tail p) (type2deTail p)).

    Definition eqType
     := [eqType of type for sig_eqType predicate].
    Definition choiceType
     := [choiceType of type for sig_choiceType predicate].
    Definition countType
       := [countType of type for sig_countType predicate].

    Local Notation "\tail_ p " := (type2tail p) (at level 0).
    Local Notation "\rest_ p " := (type2deTail p) (at level 0).
    Local Notation "\path_ p " := (type2path p) (at level 0).
    Local Notation "\head_ p " := (seq.last \tail_p \rest_p) (at level 0).
    Local Notation "\list_ p " := (cons \tail_p \rest_p) (at level 0).
    Local Notation "\mkPath( a --> r | p ) " := (exist _ (a,r) p) (at level 0).
    Local Notation "a -- Q --> b" := (EG Q a b) (at level 0).

    Section Operations.
      (* the proof of a concatenation *)
      Definition cat_proof {p1 p2 : type} (J : \head_p1 -- Q --> \tail_p2) :
        predicate (\tail_p1, \rest_p1 ++ \list_p2).
      Proof. destruct p1.
        rewrite /predicate cat_path -(rwP andP); split=>//=.
        destruct p2=>/=.
        move: J; rewrite /predicate=>J.
        rewrite -(rwP andP); split=>//=.
      Qed.

      Definition cat
       (p1 p2 : type) (J : \head_p1 -- Q --> \tail_p2) : type :=
        \mkPath(\tail_p1 --> \rest_p1 ++ \list_p2 | cat_proof J).

      (* the proof of a cons *)
      Definition cons_proof {a} {p : type} (J : a -- Q --> \tail_p) :
        predicate(a, \list_p).
      Proof. rewrite -(rwP andP); split=>//=; apply \path_p. Qed.

      Definition cons a (p : type) (J : a -- Q --> \tail_p) : type :=
        \mkPath(a --> \list_p | cons_proof J).

      (* the proof of an rcons *)
      Definition rcons_proof {z} {p : type} (J : \head_p -- Q --> z) :
       predicate (\tail_p, rcons (\rest_p) z).
      Proof. rewrite /predicate rcons_path -(rwP andP); split=>//=; apply \path_p. Qed.

      Definition rcons (p : type) z (J : \head_p -- Q --> z) : type :=
        \mkPath(\tail_p --> rcons (\rest_p) z | rcons_proof J ).
    End Operations.
    Section Functions.
      Definition length (p : type) : nat := size \list_p.
    End Functions.

    Local Notation "\mkPath( a --> r | p ) " := (exist _ (a,r) p) (at level 0).
    Local Notation "\( p ++ q )_ J" := (cat p q J) (at level 0).
    Local Notation "\( a ::> p )_ J" := (cons a p J) (at level 0).
    Local Notation "\( p <:: z )_ J" := (rcons p z J) (at level 0).
    Local Notation "\rev_ p" := (rev p) (at level 0).
    Local Notation "\nth_ p ( n , err ) " := (nth n \list_p err) (at level 0).
    Local Notation "\mkArrow( a ) " := (\mkPath( a --> nil | is_true_true )) (at level 0).
    Section Lemmas.

      Section ConcatAssociativity.
        Lemma join_cat {p1 p2 : type} {t3}  :
             forall (J12 : \head_p1 -- Q --> \tail_p2) (J23 : \head_p2 -- Q --> t3),
                \head_(cat J12) -- Q --> t3.
        Proof. by move=> J12 J23; rewrite last_cat last_cons. Qed.

        Lemma cat_join {h1} {p2 p3 : type}  :
             forall (J12 : h1 -- Q --> \tail_p2) (J23 : \head_p2 -- Q --> \tail_p3),
                h1 -- Q --> \tail_(cat J23).
        Proof. by []. Qed.

        Lemma catA (p1 p2 p3 : type)
          (J12 : \head_p1 -- Q --> \tail_p2) (J23 : \head_p2 -- Q --> \tail_p3) : 
          cat (join_cat J12 J23) = cat (cat_join J12 J23).
        Proof.
          rewrite /cat/type2tail/type2deTail=>/=.
          apply eq_sig_hprop=>//=[x|]; by [apply proof_irrelevance|rewrite -cat_cons catA].
        Qed.
      End ConcatAssociativity.

      Section SizeTwoPlusFacts.
        Lemma path_first_join {a L} (p : type) : 
          (a::L = \rest_p) -> \tail_p -- Q --> a.
        Proof. move=> I.
          destruct p as [[a' p] P]; move: P I.
          rewrite /type2tail/type2deTail=>/=P I.
          destruct I.
          by apply (rwP andP) in P as [P _].
        Qed.

        Definition path_behead_proof {a L} (p : type)
          (I : a::L = \rest_p) : predicate (a,L).
        Proof.
          destruct p as [[a' p] P]; move: P I.
          rewrite /type2tail/type2deTail=>/=P I.
          destruct I.
          by apply (rwP andP) in P as [_ P].
        Qed.

        Lemma path_last_join {a L} (p : type) : 
          (a::L = \rest_p) -> (seq.last \tail_p (belast a L)) -- Q --> \head_p.
        Proof. move: a p;
          induction L=>//=; rewrite /type2deTail/type2tail=>a0 p I/=. {
          rewrite -I /seq.last; move: I.
          destruct p as [p P]=>/=I.
          rewrite/predicate -I in P.
          by apply (rwP andP) in P as [P _].
          } {
          destruct p as [[a' p] P]; move: P I=>/=P I.
          rewrite -I in P; apply (rwP andP) in P as [P P1].
          by rewrite -I=>/=; apply (IHL a \mkPath(a0-->(a::L)|P1)). }
        Qed.
      End SizeTwoPlusFacts.

      Lemma length_cat (p1 p2 : type) (J : \head_p1 -- Q --> \tail_p2) : 
        ((length p1) + (length p2))%nat = length (cat J).
      Proof. by rewrite /cat/length/type2deTail-cat_cons size_cat. Qed.

      Lemma length_arrow (a : \A_Q) : 1 = length \mkArrow(a).
      Proof. by []. Qed.

      Lemma length_cons a (p : type) (J : a -- Q --> \tail_p) : 
        (length p).+1 = length (cons J).
      Proof. by auto. Qed.

      Lemma length_rcons z (p : type)  (J : \head_p -- Q --> z) : 
        (length p).+1 = length (rcons J).
      Proof. rewrite /rcons/length/type2tail/type2deTail=>//=.
      by rewrite size_rcons. Qed.
    End Lemmas.

    Section PathLists.

      Definition getExtendingArrows
        (p : type) := list_rect
        (fun _ => seq.seq ({a : \A_Q | \head_p--Q-->a = true}))
        [::]
        (fun a _
           (IHl : seq.seq ({a : \A_Q | \head_p--Q-->a = true})) =>
         (if \head_p--Q-->a as b0
           return \head_p--Q-->a = b0 ->
              seq.seq ({a : \A_Q | \head_p--Q-->a = true})
          then fun J0 : \head_p--Q-->a = true
             => ((exist _ a J0) :: IHl)%SEQ
          else fun _ : \head_p--Q-->a = false
             => IHl
          ) (erefl (\head_p--Q-->a))
        ) (enum \A_ (Q)).

      Definition extendPath (p : type) : seq (type)
       := map
           (fun s => rcons (proj2_sig s))
           (getExtendingArrows p).

      Definition pathsOfLength1 : seq (type)
       := map (fun a => \mkArrow(a)) (enum \A_Q).

      Definition extendPathsByOne (L : seq (type)) : seq (type)
       := foldr (fun p PL => (extendPath p) ++ PL) nil L.

      Fixpoint pathsOfLengthN (n : nat) := match n with
        |0 => nil
        |1 => pathsOfLength1
        |S n' => extendPathsByOne (pathsOfLengthN n')
        end.

      Fixpoint pathsOfLengthUpToN (n : nat) := match n with
        |0 => nil
        |S n' => (pathsOfLengthN n) ++ (pathsOfLengthUpToN n')
        end.

      Lemma pathsOfLength1_length1 : all (fun p => length p == 1) (pathsOfLength1).
      Proof. rewrite /pathsOfLength1 /(enum _); induction (Finite.enum \A_Q)=>//. Qed.

      Lemma extendPathByOne_extend_length_by_1
       : forall n (p : type),
          length p == n
           -> all (fun p => length p == S n) (extendPath p).
      Proof.
        destruct p as [[a L] p]; simpl in p.
        rewrite /length/type2tail/type2deTail=>//=.
        rewrite -(rwP eqP); move: n.
        induction L=>//=n H.
        rewrite -H /extendPath/length/type2tail/type2deTail=>//=.
        induction(getExtendingArrows \mkPath( a --> [::] | p))=>//=.
        rewrite /extendPath/length/type2tail/type2deTail=>//=.
        clear IHL; move: n H.
        induction(getExtendingArrows \mkPath( a --> (a0::L) | p))=>//= n H.
        by rewrite(IHl n H) size_rcons H eq_refl.
      Qed.

      Lemma extendPathsByOne_extend_length_by_1
       : forall n (L : seq.seq (type)),
          all (fun p => length p == n) L
           -> all (fun p => length p == S n) (extendPathsByOne L).
      Proof. move=> n L.
        induction L=>//=H.
        apply (rwP andP) in H as [H H']=>/=.
        by rewrite seq.all_cat (IHL H') extendPathByOne_extend_length_by_1.
      Qed.

      Lemma pathsOfLengthN_length_N (n : nat) :
        all (fun p => length p == n) (pathsOfLengthN n).
      Proof.
        induction n=>//=; induction n=>//.
        rewrite /pathsOfLength1/(enum _).
        induction(Finite.enum \A_Q)=>//=.
        rewrite extendPathsByOne_extend_length_by_1=>//.
      Qed.

      Lemma length_1_in_pathsOfLength1 : forall p : type, length p = 1 -> p \in (pathsOfLength1).
      Proof.
        destruct p as [[a L] p]; simpl in p.
        induction L.
        rewrite /length/type2tail/type2deTail=>/=_.
        rewrite /pathsOfLength1.
        apply (rwP mapP).
        refine (ex_intro2 _ _ a _ _).
        rewrite -(enum_rankK a) mem_enum.
        by apply (enum_valP (enum_rank a)).
        simpl in p.
        refine (eq_sig_hprop (fun _ => proof_irrelevance _) _ _ _)=>//.
        rewrite /length/type2tail/type2deTail=>//=.
      Qed.


      Lemma length_N_in_pathsOfLengthN :
        forall p : type, p \in (pathsOfLengthN (length p)).
      Proof. move=> p.
        destruct p as [(a,p) H]. move: a H.
        induction p=>/=[a H|a' H].
        rewrite /type2tail/type2deTail.
        apply length_1_in_pathsOfLength1.
        by rewrite /length.
        assert(H' := H).
        apply (rwP andP) in H'.
        destruct H' as [H1 H2].
      Admitted.
    End PathLists.

    Section Cycle.
      Definition cycle_flip {p : type} (J : \head_p--Q-->\tail_p) (N : type)
        (H : \head_N--Q-->\tail_N /\ \head_N--Q-->\tail_p)
       : \head_p--Q-->\tail_N.
      Proof. destruct H as [H1 H2].
        move: H1 H2 J; rewrite -!(rwP eqP)=> H1 H2 J.
        by rewrite J -H2 -H1.
      Qed.

      Definition nCycle_cat_obligation_1
        {p N : type} (J : (\head_ (p)) -- Q --> (\tail_ (p)))
        (H : (\head_N) -- Q --> (\tail_N) /\
             (\head_N) -- Q --> (\tail_p)) := 
      match H as a return
          ((\head_(cat (cycle_flip J a))) -- Q -->
           (\tail_(cat (cycle_flip J a))) /\
           (\head_(cat (cycle_flip J a))) -- Q --> (\tail_ (p)))
      with | conj _ i0 =>
          eq_ind_r
            (fun val : \A_ (Q) =>
             (val) -- Q --> (\tail_p) /\
             (val) -- Q --> ((sval p).1)) (conj i0 i0)
            (last_cat \tail_p \rest_p \list_N)
      end.


      Definition nCycle_cat {p : type} (J : \head_p--Q-->\tail_p) (N : type)
         (H : \head_N--Q-->\tail_N /\ \head_N--Q-->\tail_p)
       : {N : type | \head_N--Q-->\tail_N /\ \head_N--Q-->\tail_p}
       := (exist _ (cat (cycle_flip J H)) (nCycle_cat_obligation_1 J H)).


      Fixpoint nCycle {p : type} (J : \head_p--Q-->\tail_p) (n : nat)
        : {N : type | \head_N--Q-->\tail_N /\ \head_N--Q-->\tail_p}
       := match n with
        |0    => exist _ p (conj J J)
        |S n' => nCycle_cat J (proj2_sig (nCycle J n'))
        end.

      Lemma nCycleLength {p : type} (J : \head_p--Q-->\tail_p) :
          forall n : nat,
        length (sval (nCycle J n)) = ((S n) * (length p))%nat.
      Proof.
      induction n.
      rewrite /nCycle=>//=.
      by rewrite mul1n.
      rewrite /nCycle=>//=.
      rewrite -length_cat IHn.
      by rewrite -{1}(mul1n (length p)) -mulnDl (add1n).
      Qed.
    End Cycle.

    Section LoopFree.
      Definition isLoopFree := ~(exists p : type, \head_p--Q-->\tail_p).
      (*
      Lemma noLoopMaxLength {U} (Q : quiverType U) :
        (exists p : type Q, \head_p--Q-->\tail_p) <-> (exists p : type Q, length p >= #|\A_Q|).
      Proof.
      split. { move=> H.
      destruct H as [p J].
      refine (ex_intro _ (sval (nCycle J #|\A_Q|)) _).
      rewrite nCycleLength.
      destruct p as [[a L] p].
      rewrite /length/type2tail/type2deTail=>//=.
      clear p J.
      induction L=>//=.
      by rewrite muln1.
      refine (leq_trans IHL (_)).
      by rewrite leq_pmul2l. }
      move=> H.
      destruct H as [p H].
      Admitted.

      Lemma noLoopMaxLength2 {U} (Q : quiverType U) :
        isLoopFree Q -> forall p : type Q, length p < #|\A_Q|.
      Proof.
      rewrite /isLoopFree.
      rewrite noLoopMaxLength.
      unfold not.
      move=> E p.
      case (length p < #|\A_ (Q)|) as []eqn:H=>//.
      case (#|\A_ (Q)| <= length p) as []eqn:H2=>//.
      assert (E2 := E (ex_intro _ p H2)).
      contradiction E2.
      rewrite -H in H2.
      Admitted.

      Theorem loopFree_Finite {U} (Q : quiverType U) :
        isLoopFree Q -> forall p : type Q, p \in (pathsOfLengthUpToN Q #|\A_Q|).
      Proof.
      move=>H p.
      assert(G := length_N_in_pathsOfLengthN Q (length p) p (erefl _)).
      case (length p) as []eqn:E.
      destruct p as [[a L] p].
      by rewrite /length/type2tail/type2deTail in E; simpl in E.
      assert(F := noLoopMaxLength2 Q H p).
      rewrite E in F.
      Admitted.
      *)
    End LoopFree.
  End Def.
  Section ExtraTypalOperations.
    Variable (Q : finQuiverType).
    Local Notation "\tail_ p " := (type2tail p) (at level 0).
    Local Notation "\rest_ p " := (type2deTail p) (at level 0).
    Local Notation "\path_ p " := (type2path p) (at level 0).
    Local Notation "\head_ p " := (seq.last \tail_p \rest_p) (at level 0).
    Local Notation "\mkPath( a --> r | p ) " := (exist _ (a,r) p) (at level 0).

    (* the proof of a reverse *)
    Definition rev_proof (p : type Q) :
    path (EG \Op_Q) \head_p (seq.rev (belast \tail_p \rest_p)).
    Proof.
    destruct p as [(a,p) P]=>/=.
    rewrite /type2tail/type2deTail rev_path /EG=>/=.
    rewrite /EG /Quiver.tail /Quiver.head in P.
    simpl in P.
    assert((fun a1 a2 : \A_ (Q) => Qhead Q a1 == Qtail Q a2)
         = (fun a1 a2 : \A_ (Q) => Qtail Q a2 == Qhead Q a1)). {
      apply functional_extensionality=>a1.
      apply functional_extensionality=>a2.
      apply eq_sym. }
    rewrite -H.
    apply P.
    Qed.
    Definition rev (p : type Q) : type \Op_Q :=
      \mkPath(\head_p --> seq.rev (belast \tail_p \rest_p) | rev_proof p).
  End ExtraTypalOperations.

  Module Exports.
      Notation "\tail_ p " := (type2tail p) (at level 0).
      Notation "\rest_ p " := (type2deTail p) (at level 0).
      Notation "\path_ p " := (type2path p) (at level 0).
      Notation "\head_ p " := (seq.last \tail_p \rest_p) (at level 0).
      Notation "\list_ p " := (cons \tail_p \rest_p) (at level 0).
      Notation "\mkPath( a --> r | p ) " := (exist _ (a,r) p) (at level 0).
      Notation "\mkArrow( a ) " := (\mkPath( a --> nil | is_true_true )) (at level 0).
      Notation "\nth_ p ( n , err ) " := (nth n \list_p err) (at level 0).
      Notation nonTrivPathType := type.
      Notation "a -- Q --> b" := (EG Q a b) (at level 0).

      Notation "\( p ++ q )_ J" := (cat p q J) (at level 0).
      Notation "\( a ::> p )_ J" := (cons a p J) (at level 0).
      Notation "\( p <:: z )_ J" := (rcons p z J) (at level 0).
      Notation "\rev_ p" := (rev p) (at level 0).
      Notation "\digraph_ Q " := (path (EG Q)) (at level 0).
    End Exports.

End NTPath.
Export NTPath.Exports.

Canonical NTPath.eqType.
Canonical NTPath.choiceType.
Canonical NTPath.countType.