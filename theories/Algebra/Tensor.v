From mathcomp Require Import ssreflect ssrfun.
From mathcomp Require Import eqtype fintype choice.
From mathcomp Require Import generic_quotient bigop seq.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
From mathcomp Require Import ssrbool.
Set Warnings "parsing".

Set Implicit Arguments.
Unset Strict Implicit.
From mathcomp Require Export ssralg.

Module TensorSubGroupGenerators.
  Section Def.
  Variable (R : ringType) (M N : lmodType R).
    Open Scope ring_scope.
    Inductive PosGen :=
      |gen1 : M -> N -> N -> PosGen
      |gen2 : M -> M -> N -> PosGen
      |gen3 : M -> R -> N -> PosGen.

    Definition PosGenVal
      (gen : PosGen) := match gen with
        |gen1 m n n' => (m,n) + (m,n') - (m, n + n')
        |gen2 m m' n => (m,n) + (m',n) - (m - m', n)
        |gen3 m r n => (r *: m, n) - (m, r *: n)
      end.

    Definition Gen := (PosGen + PosGen)%type.
    Definition GenVal (gen : Gen) :=
      match gen with
        |inl g => PosGenVal g
        |inr g => -PosGenVal g
      end.

  Definition negateGen (gen : Gen) :=
    match gen with inl t => inr t | inr t => inl t end.
  End Def.
End TensorSubGroupGenerators.

Require Import FreeModules Quotient Submodule Algebras FormalLC.
Module Tensor.
  Section Def.
    Variable (R : comRingType) (M N : lmodType R).

    Definition freeModule := formalLCType R (M*N).

    Lemma tensorP : forall m : freeModule, reflect (exists L : seq (R * Gen)%type, (\sum_(t <- L) t.1 *: ?f t.2)%R == m) (?inSub m).
    Definition subModule := subLmodGen 4.

    Axiom getGens : forall (p : M*N), option {L : seq (TensorSubGroupGenerators.Gen M N) | p == \big[+%R/0%R]_(l <- L)(TensorSubGroupGenerators.GenVal l)}.
    Definition isIn (p : M*N) := if getGens p is None then false else true.
    Axiom closedSubMod : submod_closed (subLmod.qualSubElem isIn).
    Definition Subgroup := subLmod.Pack closedSubMod.
    Definition type := quotLmod Subgroup.
  End Def.

  Section AlgDef.
  Open Scope ring_scope.
  Variable (R : ringType) (A : lalgType R) (M : lmodType A) (N : lmodType R).

  Definition Scale (a : A) (x : type (lmods.AtoRmod M) N) : type (lmods.AtoRmod M) N
    := \pi (a *: (repr x).1, (repr x).2).

  Lemma scale_axiom : forall (a b : A) (v : type (lmods.AtoRmod M) N),
    Scale a (Scale b v) = Scale (a * b) v.
  Proof. rewrite/Scale=> a b x=>/=. Admitted.

  Lemma scale_left_id : left_id 1 Scale.
  Proof. rewrite/Scale=> x=>/=; rewrite GRing.scale1r=>/=. destruct x. destruct erepr. Admitted.

  Lemma scale_right_d : right_distributive Scale +%R.
  Proof. rewrite/Scale=> a y z=>/=. Admitted.

  Axiom algMixin : GRing.Lmodule.mixin_of A (type (lmods.AtoRmod M) N). (* := LmodMixin scale_axiom scale_left_id scale_right_d . *)

  Definition algType := LmodType A (type (lmods.AtoRmod M) N) (algMixin).
  End AlgDef.

  Module Exports.
    Infix "\(x)\" := type (at level 80, right associativity).
    Infix "\\(x)\\" := (algType _) (at level 80, right associativity).
  End Exports.
End Tensor.
Export Tensor.Exports.
Close Scope ring_scope.
