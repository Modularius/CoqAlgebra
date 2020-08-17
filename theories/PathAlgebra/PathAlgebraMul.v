Require Import Coq.Logic.FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun eqtype bigop.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
    From mathcomp Require Import ssrbool.
Set Warnings "parsing".
Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Require Import Path ntPath Quiver ntPathPairs FormalLC.

Module PAMul.
Open Scope ring_scope.

  Section Def.
  Variables (R : ringType) (Q : finQuiverType).

  Definition Mul (f g : R \LC^(pathType Q))
    := fun p : pathType Q
      => \sum_(i <- Path.BuildPairs p)
            (f i.1)*(g i.2).
(*
  Definition MulEndPairs
    (ntP : nonTrivPathType Q) (x1 x2 : lmod) :=
         (x1 (\e_\t_Q(\tail_ntP))) * (x2 (ntP)) +
         (x1 (ntP)) * (x2 (\e_\h_Q(\head_ntP))).

  Definition Mul (x1 x2 : lmod)
    := fun p : pathType Q
     => match p with
        |\e_v => (x1 \e_v) * (x2 \e_v)
        |inr ntP => (MulEndPairs ntP x1 x2)
        + \sum_(i <- PathPairs.ExtractPairs (PathPairs.Build ntP))
            (x1 (PathPairs.path1 i))*(x2 (PathPairs.path2 i))
        end.
*)
  Definition One : R \LC^(pathType Q) := fun p : pathType Q => match p with
    |\e__ => 1
    |_ => 0 end.

  Lemma eq_bigop_zero_zero {T : Type} (L : list T) :
  \big[+%R/0]_(i <- L)
    (GRing.zero R)
     = (GRing.zero R).
  Proof.
  induction L; [by rewrite big_nil|by rewrite big_cons IHL GRing.addr0].
  Qed.

  Lemma left_id1 : left_id One Mul.
  Proof. rewrite /Mul => x; apply functional_extensionality=>p.
    rewrite/Path.BuildPairs.
    induction p; [by rewrite big_seq1 /One GRing.mul1r |].
    destruct b as [a P]; destruct a as [a p].
    move: a P.
    induction p=>//=[a P|a' P]. {
    rewrite big_cons GRing.mul1r=>/=;
    by rewrite big_seq1 GRing.mul0r GRing.addr0. }
    rewrite big_cons big_cat big_cons =>/=.
    rewrite big_map big_nil
    (eq_bigr (fun _ => 0)).
    by rewrite eq_bigop_zero_zero GRing.mul1r GRing.mul0r GRing.add0r !GRing.addr0.
    by move=>i _; rewrite GRing.mul0r.
  Qed.

  Lemma right_id1 : right_id One Mul.
  Proof. rewrite /Mul => x; apply functional_extensionality=>p.
    rewrite/Path.BuildPairs.
    induction p; [by rewrite big_seq1 /One GRing.mulr1 |].
    destruct b as [a P]; destruct a as [a p].
    move: a P.
    induction p=>//=[a P|a' P]. {
    by rewrite big_cons GRing.mulr0 GRing.add0r
    big_cons /One big_nil GRing.mulr1 GRing.addr0=>/=. }
    rewrite big_cons big_cat big_cons =>/=.
    rewrite big_map big_nil
    (eq_bigr (fun _ => 0)).
    by rewrite eq_bigop_zero_zero GRing.mulr1 GRing.mulr0 !GRing.add0r GRing.addr0.
    by move=>i _; rewrite GRing.mulr0.
  Qed.

  Lemma addXr (x y z : R) :
    y = z -> x + y = x + z. Proof. by move=>H; rewrite H. Qed.

  Lemma addrX (x y z : R) :
    y = z -> y + x = z + x. Proof. by move=>H; rewrite H. Qed.

  Lemma MulA : associative Mul.
  Proof.
  move => x y z.
  rewrite /Mul.
  apply functional_extensionality=>p.
rewrite (eq_bigr (fun i => \big[+%R/0]_(i0 <- Path.BuildPairs (Q:=Q) i.2)
  ( (x i.1) * (y i0.1 * z i0.2) ) )).
Admitted.
(*rewrite pair_big_dep.\
symmetry;
rewrite (eq_bigr (fun i => \big[+%R/0]_(i0 <- Path.BuildPairs (Q:=Q) i.1)
  (x i0.1 * y i0.2 * z i.2))); symmetry.
  rewrite /Mul/MulEndPairs.
  induction p1; [by rewrite -GRing.mulrA|].
  rewrite !GRing.mulrDr !GRing.mulrDl -!GRing.mulrA -!GRing.addrA.
  apply addXr.
  apply addXr.
  rewrite GRing.addrC -!GRing.addrA.
  apply addXr.
  rewrite big_distrl big_distrr=>/=.
  rewrite -!big_split=>/=.
  rewrite (eq_bigr (fun i =>(
       x (PathPairs.path1 i) * y (\e_\t_Q(\tail_(PathPairs.path2 i))) * z (PathPairs.path2 i) +
       x (PathPairs.path1 i) * y (PathPairs.path2 i) * z (\e_\h_Q(\head_(PathPairs.path2 i))) +
       x (\e_\t_Q(\tail_b)) * (y (PathPairs.path1 i) * z (PathPairs.path2 i))) +
       \big[+%R/0]_(i0 <- PathPairs.ExtractPairs (PathPairs.Build (PathPairs.path2 i)))
          (x (PathPairs.path1 i) * y (PathPairs.path1 i0) * z (PathPairs.path2 i0))
  ) _).
  symmetry.
  rewrite (@eq_bigr _ _ _ _ _ _ 
  (fun i =>(
  (x (PathPairs.path1 i) * y (PathPairs.path2 i) * z (\e_\h_Q(\head_b)) +
      (x (\e_\t_Q(\tail_(PathPairs.path1 i))) * y (PathPairs.path1 i) +
       x (PathPairs.path1 i) * y (\e_\h_Q(\head_(PathPairs.path1 i))) +
       \big[+%R/0]_(i0 <- PathPairs.ExtractPairs (PathPairs.Build (PathPairs.path1 i)))
          (x (PathPairs.path1 i0) * y (PathPairs.path2 i0))) * z (PathPairs.path2 i))
  ))
  (fun i =>(
       x (PathPairs.path1 i) * y (\e_\h_Q(\head_(PathPairs.path1 i))) * z (PathPairs.path2 i) +
       x (PathPairs.path1 i) * y (PathPairs.path2 i) * z (\e_\h_Q( \head_b)) +
       x (\e_\t_Q( \tail_(PathPairs.path1 i))) * y (PathPairs.path1 i) * z (PathPairs.path2 i) +
       \big[+%R/0]_(i0 <- PathPairs.ExtractPairs (PathPairs.Build (PathPairs.path1 i)))
          (x (PathPairs.path1 i0) * y (PathPairs.path2 i) * z (PathPairs.path2 i))
  ))).
  rewrite !big_split=>/=.
  assert(\big[+%R/0]_(i <- PathPairs.ExtractPairs (PathPairs.Build b))
     (x (PathPairs.path1 i) * y (\e_\t_Q(\tail_(PathPairs.path2 i))) *
      z (PathPairs.path2 i))
  = \big[+%R/0]_(i <- PathPairs.ExtractPairs (PathPairs.Build b))
     (x (PathPairs.path1 i) * y (\e_\h_Q( \head_(PathPairs.path1 i))) *
      z (PathPairs.path2 i))
  ). {
  apply eq_bigr=>i _.
  pose(J' := PathPairs.join i).
  apply (rwP eqP) in J'.
  by rewrite J'. }
  rewrite H; clear H.
  rewrite -!GRing.addrA.
  apply addXr.
  assert(
  \big[+%R/0]_(i <- PathPairs.ExtractPairs (PathPairs.Build b))
     (x (PathPairs.path1 i) * y (PathPairs.path2 i) *
      z (\e_\h_Q( \head_(PathPairs.path2 i))))
  = \big[+%R/0]_(i <- PathPairs.ExtractPairs (PathPairs.Build b))
     (x (PathPairs.path1 i) * y (PathPairs.path2 i) *
      z (\e_\h_Q(\head_b)))
  ). {
  apply eq_bigr=>i _.
  assert(C := PathPairs.conn i).
  assert(\head_b = \head_(NTPath.cat (PathPairs.path1 i) (PathPairs.path2 i) (PathPairs.join i))).
  by rewrite -C.
  by rewrite H /NTPath.cat/NTPath.type2tail/NTPath.type2deTail last_cat last_cons. }
  rewrite H; clear H.
  apply addXr.

  assert(
  \big[+%R/0]_(i <- PathPairs.ExtractPairs (PathPairs.Build b))
     (x (\e_\t_Q( \tail_(PathPairs.path1 i))) * y (PathPairs.path1 i) *
      z (PathPairs.path2 i))
  = \big[+%R/0]_(i <- PathPairs.ExtractPairs (PathPairs.Build b))
     (x (\e_\t_Q(\tail_b)) * (y (PathPairs.path1 i) *
      z (PathPairs.path2 i)))
  ). {
  apply eq_bigr=>i _.
  assert(C := PathPairs.conn i).
  assert(\tail_b = \tail_(NTPath.cat (PathPairs.path1 i) (PathPairs.path2 i) (PathPairs.join i))).
  by rewrite -C.
  by rewrite GRing.mulrA H /NTPath.cat/NTPath.type2tail/NTPath.type2deTail. }
  rewrite H; clear H.
  apply addXr.
  Abort.
*)

  Definition PathMonoid := @Monoid.Law (R \LC^(pathType Q)) One Mul MulA left_id1 right_id1.
End Def.

End PAMul.
