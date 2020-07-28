From Coq.Logic Require Import FunctionalExtensionality ProofIrrelevance.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool.
Set Warnings "parsing".
Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

From mathcomp Require Import ssreflect ssrfun bigop.
From mathcomp Require Import eqtype choice fintype generic_quotient.

Require Import PathAlgebra PathAlgebraBasis ChainComplex
          DirectSum FormalLC Basis FreeModules Dimension
          QuiverRep QuiverRepFunctors Quotient fdMorphism.
Set Implicit Arguments.
Unset Strict Implicit.

Module RepStdRes.
  Section Def.
    Variable  (R : comRingType) (U : Quiver.nonEmptyUniverse) (Q : quiverType U)
      (V : fdQuiverRepType R Q).

    Definition TensorSpace (i1 i2 : \V_Q)
    := formalLC.type_lmodType R ( {p : pathType Q | (Path.tail p == i1)} * (basis (fdQuivRep.V_0 _ _ V i2)) ).

    Definition TensorSpaceOfArrow (a : \A_Q) := TensorSpace \h_Q(a) \t_Q(a).
    (*      Tensor.algType (Rmul R \h_Q(a)) \Vec_(V)(\t_Q(a)).*)

    Definition TensorSpaceOfArrows := lmodDS.idx.DS (fun a => TensorSpaceOfArrow a).

    Definition TensorSpaceOfVertex (i : \V_Q) := TensorSpace i i.
    (*    Tensor.algType (Rmul R i) \Vec_(V)(i).*)

    Definition TensorSpaceOfVertices := lmodDS.idx.DS (fun i => TensorSpaceOfVertex i).
    (*
    Definition PairSpaceOfArrow (a : \A_Q) : zmodType := pair_lmodType (lmods.AtoRmod (Rmul R \h_Q(a))) \Vec_(V)(\t_Q(a)).
    Definition PairSpaceOfVertex (i : \V_Q) : zmodType := pair_lmodType (lmods.AtoRmod (Rmul R i)) \Vec_(V)(i).
    Program Definition Map1Tail (a : \A_Q) (i : \V_Q)
      : PairSpaceOfArrow a -> ((lmods.AtoRmod (Rmul R \t_Q(a)))*\Vec_(V)(\t_Q(a)))%type
    := fun x => (@subLmod.subPack _ _ _ ((subLmod.subsort x.1)*(PAlgBasis.elem R (Path.nonTrivPathToPath \mkArrow(a))))%R _,x.2).
    Next Obligation.
    rewrite qualifE unfold_in.
    assert(K:=PAlgBasis.idemR R (Path.nonTrivPathToPath \mkArrow(a))).
    simpl in K; rewrite /NTPath.type2tail in K; simpl in K.
    rewrite -GRing.mulrA.
    by rewrite K.
    Qed.


    Definition Map1Head (a : \A_Q) (i : \V_Q)
      : PairSpaceOfArrow a -> ((lmods.AtoRmod (Rmul R \h_Q(a)))*\Vec_(V)(\h_Q(a)))%type
    := fun x => -(x.1, \Map_( V )( a) x.2).

    Unset Implicit Arguments.
    Definition Map1PairSpace (a : \A_Q) (i : \V_Q)
      : PairSpaceOfArrow a -> PairSpaceOfVertex i.
    Proof. move=>x.
    case (i == \t_Q(a)) as []eqn:Et.
    apply (rwP eqP) in Et.
    rewrite Et.
    apply (Map1Tail i x).
    case (i == \h_Q(a)) as []eqn:Eh.
    apply (rwP eqP) in Eh.
    rewrite Eh.
    apply (Map1Head i x).
    apply (0%R).
    Qed.

    Axiom Map1PairSpace_lin : forall (a : \A_Q) (i : \V_Q) , linear (Map1PairSpace a i).
    Definition Map1PairSpaceLin (a : \A_Q) (i : \V_Q) := Linear (Map1PairSpace_lin a i).


    Definition Map1 (a : \A_Q) (i : \V_Q) : (TensorSpaceOfArrow a : zmodType) -> (TensorSpaceOfVertex i : zmodType)
    := fun x => match x with
    | EquivQuot.EquivQuotient x0 _ =>
        \pi_(EquivQuot.quotType
              (eD:=quotLmod.equiv_equiv
                      (Tensor.Subgroup (lmods.AtoRmod (Rmul R i)) \Vec_( V )( i)))
              (quotLmod.equiv_encModRel
                  (Tensor.Subgroup (lmods.AtoRmod (Rmul R i)) \Vec_( V )( i))))
          ((Map1PairSpaceLin a i) x0)
    end.
    Axiom Map1_lin : forall (a : \A_Q) (i : \V_Q), linear (Map1 a i).
    Canonical Map1Lin (a : \A_Q) (i : \V_Q)
      : {linear (TensorSpaceOfArrow a) -> (TensorSpaceOfVertex i)}
    := Linear (Map1_lin a i).

    *)

    Program Definition Map2 (i : \V_Q)
      : (TensorSpaceOfVertex i) -> (QuivRepFunc.repToMod V).

    Program Definition Map1 (a : \A_Q) (i : \V_Q)
      : (TensorSpaceOfArrow a) -> (TensorSpaceOfVertex i)
    := fun f => _.
    Next Obligation.
    refine (fun p => _).
    destruct p as [p H].
    destruct p as [p Hp].
    case(i == \h_Q(a)) as []eqn:E.
    apply (rwP eqP) in E.
    Check f.
    -\sum_(j : (basis \Vec_(V)(\h_Q(a)))) \sum_(k : (basis \Vec_(V)(\t_Q(a))))
    (finGenCoef j H)*(fdLinear.structureCoef \Map_(V)(a) j k)


    Program Definition Map2PairSpace (i : \V_Q)
      : PairSpaceOfVertex i -> (QuivRepFunc.repToMod V : zmodType)
    := fun x => _.
    Next Obligation.
    destruct s.
    Admitted.

    Axiom Map2PairSpace_lin : forall (i : \V_Q) , linear (Map2PairSpace i).
    Definition Map2PairSpaceLin (i : \V_Q) := Linear (Map2PairSpace_lin i).
    Definition Map2 (i : \V_Q) : (TensorSpaceOfVertex i : zmodType) -> (QuivRepFunc.repToMod V : zmodType)
    := fun x => match x with
    | EquivQuot.EquivQuotient x0 _ => (Map2PairSpaceLin i) x0
    end.
    Axiom Map2_lin : forall (i : \V_Q), linear (Map2 i).

    Canonical Map2Lin (i : \V_Q)
      : {linear (TensorSpaceOfVertex i) -> (QuivRepFunc.repToMod V)}
    := Linear (Map2_lin i).

    Program Definition StandardResolution
    := [ses 0 --> (TensorSpaceOfArrows)    -->
                  (TensorSpaceOfVertices)  -->
                  (QuivRepFunc.repToMod V) --> 0 |
          lmodDS.linExt.ExtendLinearlyLin (fun a i => Map1Lin a i),
          lmodDS.linExt.ExtendLinearlyFromLin (fun i => Map2Lin i)    ] _ _ _.
    Next Obligation.
      split.
      move=>x.
      rewrite /comp.
      by rewrite GRing.linear0.
      move=>y H.
      refine(ex_intro _ 0 _).
      simpl in H; rewrite /lmodDS.linExt.ExtendLinearly in H; simpl in H.
      rewrite /Map1 in H.
    Admitted.
    Next Obligation.
      split. /comp=>x.
    Admitted.
    Next Obligation.
      split. move=>x.
      by rewrite /comp=>/=.
      move=>y H.
      refine(ex_intro _ 0 _).
      simpl.
    Admitted.
  End Def.
End RepStdRes.
Close Scope ring_scope.
