Require Import Program List.
From Coq.Logic Require Import ProofIrrelevance FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun path seq fintype.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
From mathcomp Require Import ssrbool ssrnat.
Set Warnings "parsing".

Require Import ntPath Quiver.
Set Implicit Arguments.
Unset Strict Implicit.

Module PathPairs.
  Section Def.
    Variable (Q : finQuiverType).
    Inductive type (p : NTPath.type Q) :=
      |Pack :
        forall (np1 : nat) (p1 p2 : NTPath.type Q) (J : \head_p1 -- Q --> \tail_p2),
          (p = NTPath.cat J) -> np1 = NTPath.length p1 -> type p
      |Null : type p.

    Lemma join_eq_cat_join {a} {p p1 p2 : NTPath.type Q} {J : \head_p1--Q-->\tail_p2}
      (C : p = (NTPath.cat J)) : (a--Q-->\tail_p) -> (a--Q-->\tail_(NTPath.cat J)).
    Proof. by rewrite -C. Qed.

    (* \mkPath(a0-->a1::L|_) => \mkArrow(a0) \mkPath(a1-->L|_) *)
    Program Definition first (p : NTPath.type Q)
      := match \rest_p with
      |nil => Null p
      |a::L => @Pack p 1
        \mkArrow(\tail_p)
        \mkPath(a-->L|NTPath.path_behead_proof (p:=p) (erefl (a::L)))
           (NTPath.path_first_join (p:=p) (erefl (a::L))) _ (NTPath.length_arrow a)
      end.
    Next Obligation.
    apply eq_sig_hprop=>//=. { move=> x; apply proof_irrelevance. }
    destruct p as [[a0 p] P]; move: p P Heq_anonymous=>/=p P.
    rewrite /NTPath.type2tail/NTPath.type2deTail=>/=Heq_anonymous.
    by rewrite -Heq_anonymous.
    Qed.

    (* shifts first arrow of p2 to the end of p1,
        n = length p1 *)
    Program Definition next
       {p : NTPath.type Q}
        (pp : type p) : type p :=
    match pp as pp' with Pack n p1 p2 J E N =>
      match \rest_p2 with nil => Null p
        |a::L => @Pack p (n.+1)%nat
              (NTPath.cat (p1:=p1) (p2:=\mkArrow(\tail_p2)) J)
              \mkPath(a-->L|NTPath.path_behead_proof (p:=p2) (erefl (a::L)))
              (NTPath.join_cat _ (NTPath.path_first_join (p:=p2) (erefl (a::L))))
               _ _
        end
      |Null => Null p
    end.
    Next Obligation.
    apply eq_sig_hprop=>//=. { move=> x; apply proof_irrelevance. }
    rewrite Heq_anonymous.
    repeat rewrite /NTPath.type2tail/NTPath.type2deTail=>/=.
    by rewrite -catA cat_cons cat0s.
    Qed. Next Obligation.
    by rewrite -NTPath.length_cat -NTPath.length_arrow -addn1.
    Qed.

    Lemma nth_ltS {n n' m : nat} : n.+1 < m -> n' = n -> n' < m. Proof.
    induction n=>A B//=; rewrite B; by intuition. Qed.

    (* np1_m1 = 0 corresponds to  length p1 = 1  *)
    (* np1_m1 corresponds to      length p1 = np1_m1 + 1  *)
    (* So we need    np1_m1 + 2 < length p  *)
    Fixpoint nth
    (p : NTPath.type Q) (np1_m1 : nat)
    (L : S np1_m1 < NTPath.length p) {struct np1_m1} : type p :=
    (match np1_m1 as np1_m1' return (np1_m1' = np1_m1 -> type p) with
    |0 => fun _ => first p
    |S np1_m1' =>
      fun (Heq_np1_m1 : np1_m1'.+1 = np1_m1)
         => next (nth (nth_ltS L Heq_np1_m1))
    end) (erefl np1_m1).

    Lemma prepend_cons_is_cat (a : \A_Q)
      {p p1 p2 : NTPath.type Q} {J : a--Q-->\tail_p} {J'}
      (C : p = (NTPath.cat J')) :
      (NTPath.cons (a:=a) (p:=p) J) = (NTPath.cat (p1:=NTPath.cons (a:=a) (p:=p1) (join_eq_cat_join C J)) (p2:=p2) J').
    Proof.
    rewrite /NTPath.cons/NTPath.cat/NTPath.type2tail/NTPath.type2deTail=>/=.
    by apply eq_sig_hprop=>//=;[move=> x; apply proof_irrelevance| rewrite C].
    Qed.

    Program Definition prepend (a : \A_Q)
      (p : NTPath.type Q) (J : a--Q-->\tail_p) (pp : type p) :
      type (NTPath.cons J) :=
    match pp with
      |Pack np1_m1 p1 p2 J' C N
         => @Pack _ (S np1_m1)
                 (NTPath.cons (a:=a) (p:=p1) (join_eq_cat_join C J))
                   p2 J'
                 (prepend_cons_is_cat _) _
      |Null => Null _
    end.
    Program Fixpoint Build_rec
      (p : NTPath.type Q) (np1_m1 : nat)
      (L : np1_m1 < size \rest_p) {struct np1_m1} :=
    match np1_m1 with
    |0 => nil
    |S n' => (@nth p (n'.+1) _)::(@Build_rec p n' _)
    end.

    Program Definition Build
      (p : NTPath.type Q) := match size \rest_p with|0 => nil
      |S n' => @Build_rec p n' _ end.

    Record ppType {big_path : NTPath.type Q} := PackPP {
      np1 : nat;
      path1 : NTPath.type Q;
      path2 : NTPath.type Q;
      join : \head_path1 -- Q --> \tail_path2;
      conn : big_path = NTPath.cat join;
      leng : np1 = NTPath.length path1;
      }.


    Fixpoint ExtractPairs {p : NTPath.type Q}
      (L : list (type p)) {struct L} : list (@ppType p)
        := match L with
      |nil => nil
      |a::L' => match a with
        |Null => ExtractPairs L'
        |Pack n p1 p2 J C N => (PackPP C N)::(ExtractPairs L')
        end
      end.

    Fixpoint ExtractTriples1 {p : NTPath.type Q}
      (L : list (type p)) {struct L} : list (exists p' : @ppType p, exists _ : list (@ppType (path2 p')),true)
    := match L with
      |nil => nil
      |a::L' => match a with
        |Null => ExtractTriples1 L'
        |Pack n p1 p2 J C N =>
          (ex_intro _ (PackPP C N) (ex_intro _
            (ExtractPairs (Build p2)) is_true_true)
          )::(ExtractTriples1 L')
        end
      end.
  (*
    Fixpoint ExtractTriples2 {U} {Q : quiverType U} {p : NTPath.type Q}
      (L : list (type p)) {struct L} : list ((list (ppType Q))*(ppType Q))
    := match L with
      |nil => nil
      |a::L' => match a with
        |Null => ExtractTriples2 L'
        |Pack n p1 p2 J C N =>
          (ExtractPairs (Build p1),
            PackPP U Q p n p1 p2 J C N
          )::(ExtractTriples2 L')
        end
      end.
  *)
    Record triple (p : NTPath.type Q) := Triple {
      p1 : NTPath.type Q;
      p2 : NTPath.type Q;
      p3 : NTPath.type Q;
      J12 : \head_p1--Q-->\tail_p2;
      J23 : \head_p2--Q-->\tail_p3;
      C : p = NTPath.cat (NTPath.cat_join J12 J23);
    }.


    Program Definition cons (a : \A_Q) (p : NTPath.type Q) (J : a--Q-->\tail_p)
     := match size \rest_p with
      |0 => nil
      |S n' => (@nth (NTPath.cons J) n' _)::
              (map (prepend J) (Build p))
      end.
    Next Obligation. by rewrite Heq_anonymous -NTPath.length_cons. Qed.

    Definition ExtendList (a : \A_Q) {p} (L : list (type p)) {J : a--Q-->\tail_p} N
    : list (type (NTPath.cons J))
    := (@nth (NTPath.cons J) (NTPath.length p) N )::(map (@prepend a p _) L).

    Section Lemmas.
    (*  Lemma path_pair_cons {U} {Q : quiverType U} (a0 a1 : \A_Q) p P
        (J : a0 -- Q --> a1) N
         : Build (NonTrivPath.cons a0 \mkPath(a1-->p|P) J)
           = ExtendList a0 (Build \mkPath(a1-->p|P)) N.
    Proof.
    rewrite /ExtendList.
    assert(forall J, (size \rest_ (\mkPath( a0 --> \list_ (\mkPath( a1 --> p | P)) | cons_proof J)))
     =
    size (a1::p)).
    by rewrite /type2deTail=>/=.
    rewrite (H J).
    rewrite {1}/Build_rec.
    move: a0 a1 P J N.
    induction p=>//.
    move=> a0 a1 P J N.
    rewrite /Build/NonTrivPath.cons{1}/type2deTail.
    rewrite{1}.
    rewrite /NonTrivPath.cons in IHp.
    rewrite{2}/Build.
    rewrite{1}/type2deTail/sval/Build_rec.

    cons a0 \mkPath(a1-->p|_) J.
    Proof.
    move: a0 a1 P J.
    induction p=>//=.
    move=> a0 a1 P J.
    *)
    End Lemmas.
  End Def.
  Module Exports.
    Notation "\1( p )" := (path1 p) (at level 0).
    Notation "\( p )2" := (path2 p) (at level 0).
  End Exports.
End PathPairs.
Export PathPairs.Exports.
