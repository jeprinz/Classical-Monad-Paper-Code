(* In this file, I'm testing why I needed CProp *)

Require Import Coq.Logic.ProofIrrelevance.
(* Instead of using SProp, for now I'll just use the proof irrelevance axiom.
   I'll see if this causes any issues; probably not. *)
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

(*
In this version, I'm going to try to shorten the definition of Classical and see if everything
still works, and if it makes it nicer or less nice.
 *)

Definition PClassical (P : Prop) : Prop := not (not P).

Definition Preturn {A : Prop} (x : A) : PClassical A.
Proof.
  intro na.
  apply na.
  apply x.
Qed.

Theorem Pbind {A B : Prop} (pa : PClassical A) (f : A -> PClassical B) : PClassical B.
  Proof.
  unfold PClassical in *.
  intros nb.
  apply pa.
  intro a.
  apply f.
  - apply a.
  - apply nb.
Qed.

Ltac pbind H := apply (Pbind H); clear H; intros H.

Theorem sigEq :
  forall A P S1 S2 p1 p2,
    S1 = S2 -> @eq {a : A | P a} (exist _ S1 p1) (exist _ S2 p2).
Proof.
  intros.
  subst S1.
  assert (p1 = p2).
  apply proof_irrelevance.
  subst p1.
  reflexivity.
Qed.

Theorem sigEq2:
  forall A P (x y : {a : A | P a}), proj1_sig x = proj1_sig y -> x = y.
Proof.
  intros.
  destruct x.
  destruct y.
  simpl in H.
  apply sigEq.
  assumption.
Qed.

Theorem Plem (P : Prop) : PClassical (P \/ ~P).
Proof.
  intros n.
  apply n.
  apply or_intror.
  intros p.
  apply n.
  apply or_introl.
  apply p.
Qed.

(*

Question: can I derive one version from the other?

 *)

Theorem canIdoIt : forall A (S : A -> Prop),
    (PClassical (exists a, S a)
    /\ forall x y, S x /\ S y -> x = y)
    <->
      (PClassical (exists! a, S a)).
Proof.
  intros.
  split.
  - intros [n u].
    pbind n.
    apply Preturn.
    specialize n as [a Sa].
    exists a.
    split.
    + assumption.
    + intros.
      specialize (u _ _ (conj Sa H)).
      subst.
      reflexivity.
  - intros.
    split.
    + pbind H.
      specialize H as [a Sa].
      apply Preturn.
      destruct Sa.
      exists a.
      auto.
    + 
Abort.

Theorem maybeICanDoThisThough : forall A (S : A -> Prop),
    (PClassical (exists a, S a)
    /\ forall x y, S x /\ S y -> PClassical (x = y))
    <->
      (PClassical (exists a, S a /\ forall a', S a' -> PClassical (a = a'))).
Proof.
  intros.
  split.
  - intros [n u].
    pbind n.
    apply Preturn.
    specialize n as [a Sa].
    exists a.
    split.
    + assumption.
    + intros.
      specialize (u _ _ (conj Sa H)).
      assumption.
  - intros.
    split.
    + pbind H.
      specialize H as [a Sa].
      apply Preturn.
      destruct Sa.
      exists a.
      auto.
    + intros.
      pbind H.
      destruct H as [a [Sa u]].
      destruct H0.
      assert (u1 := u _ H).
      assert (u2 := u _ H0).
      pbind u1.
      pbind u2.
      apply Preturn.
      subst.
      reflexivity.
Qed.

(* The "Unique" monad, that represents a unique thing that exists non-constructively *)
Definition Classical (A : Type) : Type :=
  (*
  {S : A -> Prop | PClassical (exists a, S a)
                    /\ forall x y, S x /\ S y -> x = y}.*)
  {S : A -> Prop | PClassical (exists! a, S a)}.

Definition Creturn {A : Type} (x : A) : Classical A.
  refine (exist _ (fun y => y = x) _).
  apply Preturn.
  exists x.
  split.
  - reflexivity.
  - intros.
    subst.
    reflexivity.
Defined.

(* In this version, we really get x = y!!! *)
Theorem CreturnInj : forall A (x y : A), Creturn x = Creturn y -> x = y.
Proof.
  intros.
  pose (@f_equal _ _ (@proj1_sig _ _) _ _ H) as fact.
  simpl in fact.
  assert (((fun y => ((y = x))) x)). {
    reflexivity.
  }
  rewrite fact in H0.
  assumption.
Qed.

Definition Cbind {A B : Type} (pa : Classical A) (f : A -> Classical B) : Classical B.
  refine (exist _ (fun b =>  (exists a, (proj1_sig pa a) /\ (proj1_sig (f a) b))) _).
  destruct pa as [Sa nonemptysame].
  simpl.
  pbind nonemptysame.
  specialize nonemptysame as [a [nonempty same]].
  remember (f a) as fa.
  destruct fa as [x0 aBa].
  apply (Pbind aBa).
  intros [a0 [x0a0]].
  apply Preturn.
  exists a0.
  split.
  - exists a.
    split; auto.
    rewrite <- Heqfa.
    simpl.
    assumption.
  - intros b [a1 [Saa1 fa1b]].
    apply H.
    Check (proj2_sig (f a1)).
    
    Check ((proj2_sig (f a1))).
    specialize allx as [ax [Saax fax]].
    specialize ally as [ay [Saay fay]].
    specialize (same _ _ (conj Saax Saay)).
    subst.
    apply ((proj2 (proj2_sig (f ay)) _ _ (conj fax fay))).
Defined.

(* one of the monad laws *)
Theorem bindDef : forall A B (a : A) (f : A -> Classical B),
    Cbind (Creturn a) f = f a.
Proof.
  intros.
  apply sigEq2.
  simpl.
  extensionality b.
  apply propositional_extensionality.
  split.
  - intros.
    simpl in H.
    destruct H.
    destruct H.
    subst.
    assumption.
  - intros.
    simpl.
    exists a.
    split; auto.
Qed.

Theorem monadlaw2 (T : Type) (t : Classical T) : Cbind t Creturn = t.
Proof.
  apply sigEq2.
  extensionality x.
  simpl.
  apply propositional_extensionality.
  split.
  - intros.
    simpl in *.
    destruct H as [a [ta p]].
    subst.
    assumption.
  - intros.
    simpl in *.
    exists x.
    split; auto.
Qed.

(* Can I get this for this version? *)
Theorem ClassicalInd T (t : Classical T)
  : PClassical (exists x, Creturn x = t /\ (proj1_sig t x)).
Proof.
  destruct t as [St [nonempty same]].
  apply (Pbind nonempty); intros [a ta].
  apply Preturn.
  exists a.
  split.
  - 
    apply sigEq2.
    simpl.
    extensionality t.
    apply propositional_extensionality.
    split.
    + simpl.
      intros.
      subst.
      assumption.
    + intros.
      simpl.
      specialize (same _ _ (conj ta H)).
      subst.
      reflexivity.
  - simpl.
    assumption.
Qed.

(* unique choice *)
Definition choose (T : Type) (P : T -> Prop)
           (nonempty : PClassical (exists t, P t))
           (unique : forall x y, P x /\ P y -> x = y)
  : Classical T.
  refine (exist _ P _).
  split.
  - simpl.
    apply (Pbind nonempty); clear nonempty; intros [t Pt].
    apply Preturn.
    exists t.
    assumption.
  - intros x y [Px Py].
    simpl in *.
    specialize (unique _ _ (conj Px Py)).
    assumption.
Defined.

Theorem choiceInd : forall (T : Type) (P : T -> Prop) (Q : Classical T -> Prop)
                            nonempty unique,
    (forall t, P t -> PClassical (Q (Creturn t)))
    -> PClassical (Q (@choose T P nonempty unique)).
Proof.
  intros.
  apply (Pbind (ClassicalInd _ (choose T P nonempty unique))).
  simpl.
  intros [St [eq PSt]].
  rewrite <- eq.
  clear eq.
  apply (Pbind nonempty); clear nonempty; intros [t Pt].
  specialize (H _ Pt).
  apply (Pbind H); clear H; intros H.
  specialize (unique _ _ (conj Pt PSt)).
  subst.
  apply Preturn.
  assumption.
Qed.
  
Theorem classicalInd : forall {T : Type} {Q : Classical T -> Prop} (c : Classical T),
    (forall t, PClassical (Q (Creturn t)))
    -> PClassical (Q c).
Proof.
  intros.
  Check ClassicalInd.
  assert (PClassical (exists x, c = Creturn x)) as fact. {
    destruct c as [c [nonempty unique]].
    apply (Pbind nonempty); intros [t Ct].
    apply Preturn.
    exists t.
    apply sigEq2.
    simpl.
    extensionality t'.
    apply propositional_extensionality.
    split.
    - intros.
      apply unique.
      auto.
    - intros.
      subst.
      assumption.
  }
  
  pbind fact.
  specialize fact as [t p].
  subst.
  apply H.
Qed.

Ltac asreturn H :=
  let H2 := fresh "H2" in
  let eq := fresh "eq" in
  let new := fresh H in
  pose (H2 := ClassicalInd _ H);
  pbind H2;
  specialize H2 as [new [eq _]];
  subst H.

Definition toProp (p : Classical Prop) : Prop :=
  PClassical (p = Creturn True).

(*
Theorem toPropRet (P : Prop) : P -> toProp (Creturn P).
Proof.
  intros.
  unfold toProp.
  apply Preturn.
  apply sigEq2.
  simpl.
  extensionality y.
  apply propositional_extensionality.
  split.
  - intros.
    subst.
    apply propositional_extensionality.
    split; auto.
  - intros.
    subst.
    apply propositional_extensionality.
    split; auto.
Qed.
*)

Theorem toPropRet : forall P, toProp (Creturn P) <-> PClassical P.
Proof.
  intros.
  split.
  - intros.
    pbind H.
    apply Preturn.
    apply (@f_equal _ _ (@proj1_sig _ _)) in H.
    simpl in H.
    apply (@f_equal _ _ (fun f => f True)) in H.
    assert (True = True) by reflexivity.
    rewrite <- H in H0.
    rewrite <- H0.
    constructor.
  - intros.
    unfold toProp.
    pbind H.
    apply Preturn.
    apply sigEq2.
    simpl.
    extensionality y.
    apply propositional_extensionality.
    split.
    + intros.
      subst.
      apply propositional_extensionality.
      split; auto.
    + intros.
      subst.
      apply propositional_extensionality.
      split; auto.
Qed.

Theorem toPropRet1 : forall P, toProp (Creturn P) -> PClassical P.
Proof.
  apply toPropRet.
Qed.

Theorem toPropRet2 : forall P, PClassical P -> toProp (Creturn P).
Proof.
  apply toPropRet.
Qed.


Ltac asreturn2 H :=
  let H2 := fresh "H2" in
  let eq := fresh "eq" in
  let new := fresh "x" in
  let Px := fresh "Px" in
  pose (H2 := ClassicalInd _ H);
  pbind H2;
  specialize H2 as [new [eq _]];
  rewrite <- eq in *;
  clear eq.

Theorem monadlaw3 {A B C : Type} {m : Classical A} {g : A -> Classical B} {h : B -> Classical C}
  : (Cbind (Cbind m g) h) = Cbind m (fun x => Cbind (g x) h).
Proof. 
    intros.
  apply sigEq2.
  simpl.
  extensionality c.
  apply propositional_extensionality.
  split.
    - intros [b [[a [ma gab]] hbc]].
      exists a.
      split.
      + assumption.
      + exists b.
        split; assumption.
    - intros [a [ma [b [gab hbc]]]].
      exists b.
      split.
      + exists a.
        split; assumption.
      + assumption.
Qed.
