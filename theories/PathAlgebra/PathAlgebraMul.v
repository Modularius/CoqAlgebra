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

  Definition PathMonoid := @Monoid.Law (R \LC^(pathType Q)) One Mul MulA left_id1 right_id1.
End Def.

End PAMul.
