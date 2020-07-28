Require Import Coq.Logic.ProofIrrelevance.
From mathcomp Require Import ssreflect ssrfun eqtype choice fintype div.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool ssrnat.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Require Import Basis FreeModules Projective.

(* We examine the correctness of the algebra libraries
  By constructing some examples of some ring modules and 
  other objects *)

(* We start with a family of finite rings,
  the positive integers modulo some natural number *)

Section NatMod.
  Variable (n : nat) (n_neq_0 : n != 0).
  Definition type := 'I_(S n).
  Definition nm_zero := @Ordinal (S n) 0 is_true_true.

  Definition modulo (m : nat) : type :=
    @Ordinal _ (modn m (S n)) (ltn_pmod _ (is_true_true : 0 < n.+1)).

  Definition nm_add (i j : type) : type := modulo (i + j).

  Definition nm_neg  (i : type) : type := modulo ((S n) - i).

  Definition nm_mul  (i j : type) : type := modulo (i * j).

  Definition nm_one : type := modulo 1.

  Lemma addA : associative nm_add.
  Proof. rewrite /nm_add=>x y z.
    rewrite /modulo(rwP eqP)/eq_op=>/=.
    by rewrite modnDmr modnDml addnA.
  Qed.
  Lemma addC : commutative nm_add.
  Proof. rewrite /nm_add=>x y.
    by rewrite addnC. Qed.

  Lemma add0 : left_id nm_zero nm_add.
  Proof. rewrite /nm_add=>x; destruct x as [m Hm].
    rewrite /modulo(rwP eqP)/eq_op add0n=>/=.
    by rewrite {2}(divn_eq m (S n)) (divn_small Hm) mul0n add0n.
  Qed.

  Lemma addI : left_inverse nm_zero nm_neg nm_add.
  Proof. rewrite /nm_add=>x; destruct x as [m Hm].
    rewrite /modulo(rwP eqP)/eq_op=>/=.
    case (m == 0) as []eqn:E. {
    apply (rwP eqP) in E.
    by rewrite E subn0 addn0 modnn mod0n.
    } {
    rewrite (@modn_small (n.+1 - m) _).
    rewrite subnK.
    by rewrite modnn.
    by rewrite (ltnW Hm).
    case m as []eqn:M.
    by rewrite eq_refl in E.
    by rewrite ltnS subSS leq_subr.
    }
  Qed. 

  Definition ZmodMixin_mod := ZmodMixin addA addC add0 addI.
  Canonical Zmod_Type := Eval hnf in ZmodType type ZmodMixin_mod.

  Lemma mulA : associative nm_mul.
  Proof. rewrite /nm_mul=>x y z.
    rewrite /modulo(rwP eqP)/eq_op=>/=.
    by rewrite modnMmr modnMml mulnA.
  Qed.

  Lemma mul0l : left_id nm_one nm_mul.
  Proof. rewrite /nm_mul=>x; destruct x as [m Hm].
    rewrite /modulo(rwP eqP)/eq_op=>/=.
    by rewrite modnMml mul1n (modn_small Hm).
  Qed.

  Lemma mul0r : right_id nm_one nm_mul.
  Proof. rewrite /nm_mul=>x; destruct x as [m Hm].
    rewrite /modulo(rwP eqP)/eq_op=>/=.
    by rewrite modnMmr muln1 (modn_small Hm).
  Qed.

  Lemma mulDl : left_distributive nm_mul nm_add.
  Proof. rewrite /nm_mul/nm_add=>x y r.
    rewrite /modulo(rwP eqP)/eq_op=>/=.
  Admitted.

  Lemma mulDr : right_distributive nm_mul nm_add.
  Proof. rewrite /nm_mul/nm_add=>x y r.
    rewrite /modulo(rwP eqP)/eq_op=>/=.
  Admitted.

  Lemma neq01 : is_true (~~ (nm_one == nm_zero)).
  Proof. rewrite /nm_one/nm_zero.
    rewrite /modulo/eq_op.
    apply (rwP negP)=>/=.
    induction n=>//=.
  Qed.

  Definition RingMixin_mod := RingMixin mulA mul0l mul0r mulDl mulDr neq01.
  Canonical RingType_mod := RingType type RingMixin_mod.

  Lemma scale_comp : forall (a b : type) (v : type),
   nm_scale a (nm_scale b v) = nm_scale (a * b)%R v.
  Proof.
    rewrite/nm_scale=>a b v.
    rewrite /modulo(rwP eqP)/eq_op=>/=.
    by rewrite modnMmr -mulnA.
  Qed.
End NatMod.