Require Import Program.
From Coq.Logic Require Import ProofIrrelevance FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun.
From mathcomp Require Import eqtype path choice seq fintype.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool.
Set Warnings "parsing".


Require Import ntPathPairs ntPath Quiver.
Set Implicit Arguments.
Unset Strict Implicit.

Module Path.

  Section Def.
    Variable (Q : finQuiverType).
    Definition type := (\V_Q + NTPath.type Q)%type.
    Definition Path_eqType
     := [eqType of type for (sum_eqType \V_Q (NTPath.ntPath_eqType Q))].
    Definition Path_choiceType
     := [choiceType of type for (sum_choiceType \V_Q (NTPath.ntPath_choiceType Q))].
    Definition Path_countType
     := [countType of type for (sum_countType \V_Q (NTPath.ntPath_countType Q))].

    Definition nonTrivPathToPath (p : nonTrivPathType Q) : type :=
      inr p.

    Definition head (p : type) : \V_Q :=
      match p with
      |inl i => i
      |inr p => \h_Q(\head_p)
      end.

    Definition tail (p : type) : \V_Q :=
      match p with
      |inl i => i
      |inr p => \t_Q(\tail_p)
      end.

    Definition BuildPairs (p : type) :=
      match p with
        |inl v => (inl v, inl v)::nil
        |inr ntP => (inl (head p),p)::
          (map
            (fun pp => (inr (PathPairs.path1 pp),inr (PathPairs.path2 pp)))
            (PathPairs.ExtractPairs (PathPairs.Build ntP))
          ) ++ (p,@inl \V_Q (NTPath.type Q) (tail p))::nil
            
        end.
    Lemma BuildPairs_nonempty (p : type) : BuildPairs p <> nil.
    Proof. induction p=>//. Qed.
  End Def.

  Module Exports.
    Notation "\e_ v" := (inl v) (at level 0).
    Coercion nonTrivPathToPath : nonTrivPathType >-> type.
    Notation pathType := type.

    Canonical Path_eqType.
    Canonical Path_choiceType.
    Canonical Path_countType.
  End Exports.
End Path.

Export Path.Exports.
(*
Print Finite.Class.
Axiom Path_finiteMixin : forall {U}  (Q : quiverType U), Finite.mixin_of ([eqType of pathType Q]).
Canonical Path_finiteType {U}  (Q : quiverType U) := Finite.Pack (Finite.Class (Path_finiteMixin Q)).
*)