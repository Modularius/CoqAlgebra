Require Import Coq.Logic.ProofIrrelevance.
From mathcomp Require Import ssreflect ssrfun eqtype choice.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Modules.

Module subLmod.
  Section Def.
    Definition qualSubElem {R : ringType} {M : lmodType R} (P : predPredType M)
      := [qualify a x | x \in P].

    Variable (R : ringType) (M : lmodType R) (P : predPredType M)
      (S : submod_closed (qualSubElem P)).

    Fact ST_key : pred_key (qualSubElem P). Proof. by []. Qed.

    Canonical ST_keyed := KeyedQualifier ST_key.

    Canonical ST_opprPred := OpprPred S.
    Canonical ST_addrPred := AddrPred S.
    Canonical ST_zmodPred  := ZmodPred S.
    Canonical ST_submodPred := SubmodPred S.

    Record subtype := subPack {
      subsort : M;
      subsortP : subsort \is a (qualSubElem P);
    }.
    Local Coercion subsort : subtype >-> GRing.Lmodule.sort.
    (* Hint Resolve subsortP. Does this do anything *)
    Canonical type_subType := [subType for subsort].

    Definition ST_eqMixin := [eqMixin of subtype by <:].
    Canonical ST_eqType := EqType subtype (ST_eqMixin).
    Definition ST_choiceMixin := [choiceMixin of subtype by <:].
    Canonical ST_choiceType := ChoiceType subtype (ST_choiceMixin).

    Definition ST_zmodMixin := [zmodMixin of subtype by <:].
    Canonical ST_zmodType := ZmodType subtype (ST_zmodMixin).
    Definition ST_lmodMixin := [lmodMixin of subtype by <:].
    Definition ST_lmodType := LmodType R subtype (ST_lmodMixin).
  End Def.

  Section ClassDef.
  Variable (R : ringType) (M : lmodType R).

    Record type := Pack {
      predP : pred M;
      closedP : submod_closed (qualSubElem predP);
    }.
    Definition Build (S : type) : lmodType R := ST_lmodType (closedP S).
  End ClassDef.

  Module Exports.
    Canonical ST_lmodType.
    Coercion Build : type >-> lmodType.
    Notation subLmodType := type.
    Notation subLmodPack := Pack.
  End Exports.
End subLmod.
Export subLmod.Exports.


Module subLmodRstr.
  Import subLmod.Exports.
  Open Scope ring_scope.

  Section Def.
  Variable (R : ringType) (M : lmodType R).

  Variable SM : subLmodType M.
  Variable N : lmodType R.
  Variable f : {linear M -> N}.

  Definition func : SM -> N := fun x => f (subLmod.subsort x).
  Lemma func_lin : linear func.
  Proof. by move=>a x y;rewrite /func GRing.linearP. Qed.
  Definition dom_restr : {linear SM -> N} := Linear func_lin.
  End Def.
  Module Exports.
    Canonical dom_restr.
    Notation subLmodRestrict := dom_restr.
  End Exports.
End subLmodRstr.
Export subLmodRstr.Exports.

Module subLmodIncl.
  Import subLmod.Exports.
  Open Scope ring_scope.

  Section Def.
    Variable (R : ringType) (M : lmodType R).
    Variable S : subLmodType M.
    Definition incl := subLmodRestrict S (GRing.idfun_linear M).
  End Def.

  Section Theory.
    Variable (R : ringType) (M : lmodType R).
    Variable S : subLmodType M.
    Lemma inj : injective (incl S).
    Proof. move=>x y H=>/=; destruct x, y; simpl in H.
    by destruct H, (proof_irrelevance _ subsortP subsortP0).
    Qed.
  End Theory.

  Module Exports.
    Notation subLmodIncl := incl.
  End Exports.
End subLmodIncl.
Export subLmodIncl.Exports.

Module subLmodMorph.
  (* If one can prove that the image of a linear function lies within a submodule then
     We have a linear function into that submodule *)
  Section Def.
    Open Scope ring_scope.
    Variable (R : ringType) (M : lmodType R).
    Variable N : lmodType R.
    Variable SN : subLmodType N.
    Variable f : {linear M -> N}.
    Definition P := fun m : M => (subLmod.predP SN) (f m).
    Variable S : submod_closed (subLmod.qualSubElem P).
    Definition closedP := forall m, P m.
    Variable H : closedP.
(*
    Definition cofunc : M -> SN := fun x => subLmodPack (H x).
    Lemma cofunc_lin : linear cofunc.
    Proof. move=>r x y.
rewrite /cofunc.
Admitted.

    Definition codom_resrt : {linear M -> SN} := Linear cofunc_lin.

  Module Exports.
    Canonical dom_restr.
    Notation subLmodRestrict := dom_restr.
    Notation subLmodIncl := incl.
  End Exports.
*)
  End Def.
End subLmodMorph.
(* Export subLmodMorph.Exports. *)



Module subLmodSelf.
  Section Def.
    Variable (R : ringType) (U : lmodType R).
    Definition inSelf : predPredType U := fun _ => true.

    Lemma self_subModule : GRing.submod_closed (subLmod.qualSubElem inSelf).
    Proof. by split=> [|a x y Hx Hy]; rewrite qualifE unfold_in. Qed.

    Definition subLmodSelf := subLmod.Pack self_subModule.
  End Def.
  Module Exports.
    Notation subLmodSelf := subLmodSelf.
  End Exports.
End subLmodSelf.
Export subLmodSelf.Exports.

Module subLmodZero.
  Section Def.
    Variable (R : ringType) (U : lmodType R).
    Definition inZero : predPredType U := fun x => x == 0%R.

    Lemma zero_subModule : GRing.submod_closed (subLmod.qualSubElem inZero).
    Proof. split=>[|a x y]; rewrite qualifE unfold_in=>//.
      rewrite !unfold_in -!(rwP eqP)=>Hx Hy;
      by rewrite Hx Hy GRing.addr0 GRing.scaler0.
    Qed.

    Definition zeroSubmod := subLmod.Pack zero_subModule.
  End Def.
  Module Exports.
    Notation subLmodZero := zeroSubmod.
  End Exports.
End subLmodZero.

From mathcomp Require Import bigop seq.
Open Scope ring_scope.
Module genSubLmod.
  Section Def.
    Variable (R : ringType) (M : lmodType R).
    Variable (T : Type) (f : T -> M).
    Variable (inSub : predPredType M).
    Variable (prop : forall m : M,
      reflect (exists L : seq (R*T), \big[+%R/0%R]_(t <- L) *:%R t.1 (f t.2) == m) (inSub m)).

    Lemma gen_subModule : GRing.submod_closed (subLmod.qualSubElem inSub).
    Proof. split=>[|a x y]; rewrite qualifE !unfold_in.
      by apply (rwP (prop 0)); refine (ex_intro _ nil _); rewrite big_nil.
      rewrite -(rwP (prop x)) -(rwP (prop y)) -(rwP (prop (a*:x + y)))=>Hx Hy.
      destruct Hx as [Lx Hx], Hy as [Ly Hy]; move : Hx Hy; rewrite -!(rwP eqP)=> Hx Hy.
      refine (ex_intro _ ((map (fun t => (a*t.1, t.2)) Lx) ++ Ly) _).
      rewrite big_cat big_map (eq_bigr (fun j => a *: (j.1 *: f j.2)))=>[|i _];
      by [rewrite -GRing.scaler_sumr Hx Hy|rewrite GRing.scalerA].
    Qed.

    Definition genSubmod := subLmod.Pack gen_subModule.
  End Def.
  Module Exports.
    Notation subLmodGen := genSubmod.
  End Exports.

End genSubLmod.
Export genSubLmod.Exports.



Module linKernel.
  Section Def.
    Variable (R : ringType) (U V : lmodType R) (f : {linear U -> V}).
    Definition inKer : predPredType U := fun x => f x == 0.

    Definition ker_elem := [qualify x | x \in inKer].

    Lemma ker_subModule : GRing.submod_closed (ker_elem).
    Proof. split=>[|a x y].
      by rewrite qualifE unfold_in GRing.linear0.
      rewrite qualifE !unfold_in !GRing.linearP -!(rwP eqP)=>Hx Hy.
      by rewrite Hx Hy GRing.addr0 GRing.scaler0.
    Qed.

    Definition kernel := subLmodPack ker_subModule.
  End Def.
  Module Exports.
    Notation kernel := kernel.
    Notation "\ker( f )" := (kernel f) (at level 0).
  End Exports.
End linKernel.
Export linKernel.Exports.


Module linImage.
  Section Def.
    Variable (R : ringType) (U V : lmodType R) (f : {linear U -> V}).
    Definition U' := option U.
    Definition V' := option V.
    Definition f' : U' -> V' := fun u' => match u' with Some u => Some (f u)|None => None end.

    Definition preim (v : V) := {u : U | f u == v}.

    Definition inIm : predPredType V :=
    fun v : V => 
      choose (fun u : U' => f' u == Some v) None != None.

    Definition im_elem := [qualify x | x \in inIm].

    Lemma im_subModule : GRing.submod_closed (im_elem).
    Proof. split.
      rewrite qualifE unfold_in.
rewrite /choose/insub.
(*case idP.
case(choose (fun u : U' => f' u == Some 0) None) as []eqn:E.
by rewrite E.
assert(choose (fun u : U' => f' u == Some 0) None = Some 0).
rewrite /choose.
case(insub (@None U)).
move=>x.
simpl.
rewrite xchooseP.*)
Admitted. (*
      by rewrite qualifE unfold_in GRing.linear0.
      move=>a x y Hx Hy.
      rewrite qualifE unfold_in GRing.linearP.
      rewrite unfold_in in Hx; apply (rwP eqP) in Hx.
      rewrite unfold_in in Hy; apply (rwP eqP) in Hy.
      by rewrite Hx Hy GRing.addr0 GRing.scaler0.
    Qed. *)

    Definition image := subLmodPack im_subModule.
  End Def.
  Module Exports.
    Notation image := image.
    Notation "\image( f )" := (image f) (at level 0).
  End Exports.
End linImage.
Export linImage.Exports.


Module sublmodDS.
  Import GRing.
  Section Pair.
    Variable (R : ringType) (m1 m2 : lmodType R).
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
  End Pair.
End sublmodDS.