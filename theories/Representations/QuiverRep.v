Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Tactics.
From mathcomp Require Import ssreflect ssrfun eqtype fintype seq.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool.
Set Warnings "parsing".
Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Require Import Quiver Path Morphism ntPath.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope ring_scope.

Module QuivRep.
  Section Def.
    Variable (R : ringType) (Q : finQuiverType).
    Structure type  := Pack {
      V_0 : forall i : \V_Q, lmodType R;
      V_1 : forall a : Q_1 Q, {linear (V_0 \t_Q(a)) -> (V_0 \h_Q(a))};
    }.

    Section Paths.
      Variable (V : type).
      
      Section Pair.
        Variable (a1 a2 : \A_Q) (J : a1--Q-->a2).
        Definition ntPathJoin_fn := (fun x => eq_rect \h_Q(a1) (fun v => (V_0 V v)) x \t_Q(a2) (match rwP eqP with conj _ x1 => x1 end J)).

        Lemma ntPathJoin_lin : linear ntPathJoin_fn.
        Proof. rewrite/ntPathJoin_fn=>r x y;
          case (rwP (@eqP _ \h_Q(a1) \t_Q(a2))).
          move=>H e; by case (e J).
        Qed.

        Definition ntPathJoin : {linear (V_0 V \h_Q(a1)) -> (V_0 V \t_Q(a2))}
        := Linear ntPathJoin_lin.
      End Pair.

      Definition ntPath (p : nonTrivPathType Q)
        : {linear V_0 V (\t_Q(\tail_p)) -> V_0 V (\h_Q(\head_p))}.
        destruct p as [[a L] p]; simpl in p.
        move: a p.
        induction L. { move=> a p; refine(V_1 V a). }
        move=> a' p.
        rewrite /NTPath.type2tail/NTPath.type2deTail=>/=.
        rewrite /NTPath.type2tail/NTPath.type2deTail in IHL; simpl in IHL.
        refine(linConcat.map (V_1 V a') (linConcat.map (ntPathJoin _) (IHL a _))).
        apply (NTPath.path_first_join (erefl \rest_\mkPath(a'-->a::L|p))).
        apply (NTPath.path_behead_proof (erefl \rest_\mkPath(a'-->a::L|p))).
      Qed.
    End Paths.

    Definition Path (V : type) (p : pathType Q)
      : {linear (V_0 V (Path.tail p)) -> (V_0 V (Path.head p))}
      := match p with
        | \e_k => linID.map (V_0 V k)
        | inr k => ntPath V k
        end.
  End Def.

  Module Exports.
    Notation quiverRepType := type.
    Notation "\'Rep' '_' R '(' Q ')'" := (type Q R) (at level 0, format "\'Rep' '_' R '(' Q ')'").
    Notation "\Vec_( V )( i )" := (V_0 V i) (at level 0).
    Notation "\Map_( V )( a )" := (V_1 V a) (at level 0).
    Notation "\PathMap_( V )( p )" := (Path V p) (at level 0).
  End Exports.
End QuivRep.

Require Import FreeModules Dimension.
Open Scope ring_scope.
Module fdQuivRep.
  Section Def.
    Structure type (R : ringIBNType) (Q : finQuiverType) := Pack {
      V_0 : forall i : \V_Q, fdFreeLmodType R;
      V_1 : forall a : Q_1 Q, {linear (V_0 \t_Q(a))->(V_0 \h_Q(a))};
    }.
    Definition fdToType {R : ringIBNType} {Q : finQuiverType} (V : type R Q)
    := @QuivRep.Pack _ _ (V_0 V) (V_1 V).
  End Def.

  Definition DimensionVector {R : ringIBNType} {Q : finQuiverType} (V : type R Q)
  := fun i : \V_Q => \dim(V_0 V i).

  Module Exports.
    Notation "\Vec^fd_( V )( i )" := (V_0 V i) (at level 0).
    Notation "\Map^fd_( V )( a )" := (V_1 V a) (at level 0).
    Notation fdQuiverRepType := type.
    Coercion fdToType : type >-> QuivRep.type.
  End Exports.
End fdQuivRep.
Export QuivRep.Exports.
Export fdQuivRep.Exports.

Close Scope ring_scope.

