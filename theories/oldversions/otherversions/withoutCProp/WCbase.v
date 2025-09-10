(* In this file, I'm testing why I needed CProp *)

Require Import Coq.Logic.ProofIrrelevance.
(* Instead of using SProp, for now I'll just use the proof irrelevance axiom.
   I'll see if this causes any issues; probably not. *)
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Definition PClassical (P : Prop) : Prop := not (not P).
Notation "[ T ]" := (PClassical T).
Definition Preturn {A : Prop} (x : A) : [A].
Proof.
  intro na.
  apply na.
  apply x.
Qed.

Theorem Pbind {A B : Prop} (pa : [A]) (f : A -> [B]) : [B].
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

(* The "Unique" monad, that represents a unique thing that exists non-constructively *)
(*TODO: would there be any reason to put a PClassical around the "x = y"? *)
Definition Classical (A : Type) : Type :=
  {S : A -> Prop | PClassical (exists a, S a)
                    /\ forall x y, S x /\ S y -> x = y}.

Notation "[[| T |]]" := (Classical T).

Definition Creturn {A : Type} (x : A) : [[| A |]].
  refine (exist _ (fun y => y = x) _).
  split.
  - apply Preturn.
    exists x.
    reflexivity.
  - intros.
    destruct H.
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
  destruct pa as [Sa [nonempty same]].
  simpl.
  split.
  - apply (Pbind nonempty).
    intros.
    simpl.
    destruct H.
    remember (f x) as fx.
    destruct fx as [x0 [p sfsdfd]].
    apply (Pbind p).
    intros.
    apply Preturn.
    destruct H0.
    exists x1.
    exists x.
    split; auto.
    rewrite <- Heqfx.
    simpl.
    assumption.
  - intros x y [allx ally].
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

Theorem isReturn {T : Type} (c : Classical T)
  : [exists t, c = Creturn t].
Proof.
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
Qed.

Theorem classicalInd : forall {T : Type} {Q : Classical T -> Prop} (c : Classical T),
    (forall t, PClassical (Q (Creturn t)))
    -> PClassical (Q c).
Proof.
  intros.
  Check ClassicalInd.
  assert (fact := isReturn c).
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

Theorem toPropRetEq : forall P, toProp (Creturn P) = PClassical P.
Proof.
  intros.
  apply propositional_extensionality.
  apply toPropRet.
Qed.

Theorem toPropRet1 : forall P, toProp (Creturn P) -> PClassical P.
Proof.
  apply toPropRet.
Qed.

Theorem toPropRet2 : forall P, PClassical P -> toProp (Creturn P).
Proof.
  apply toPropRet.
Qed.

Theorem toPropRetNot : forall P, ~ (Creturn P = Creturn True) -> ~P.
Proof.
  intros P H p.
  apply H.
  apply f_equal.
  apply propositional_extensionality.
  split; auto.
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


Definition Pif {T : Type} (P : Prop) (b1 b2 : T) : Classical T.
  refine (exist _ (fun b => P /\ b = b1 \/ ~P /\ b = b2) _).
  split.
  - apply (Pbind (Plem P)); intros pornotp.
    apply Preturn.
    destruct pornotp.
    + exists b1.
      auto.
    + exists b2.
      auto.
  - intros.
    destruct H.
    destruct H; destruct H0;
      destruct H; destruct H0;
      subst; auto; contradiction.
Defined.

Theorem PifDef1 {T : Type} (P : Prop) (b1 b2 : T) (p : P) : Pif P b1 b2 = Creturn b1.
Proof.
  intros.
  apply sigEq2.
  simpl.
  extensionality b.
  apply propositional_extensionality.
  split; intros; repeat destruct H; auto.
Qed.

Theorem PifDef2 {T : Type} (P : Prop) (b1 b2 : T) (p : ~ P) : Pif P b1 b2 = Creturn b2.
Proof.
  intros.
  apply sigEq2.
  simpl.
  extensionality b.
  apply propositional_extensionality.
  split; intros.
  - destruct H.
    + destruct H.
      contradiction.
    + destruct H.
      assumption.
  - apply or_intror.
    auto.
Qed.

Ltac classical_auto :=
  repeat first [
      match goal with
      | H : toProp (Creturn ?rest) |- _ => apply toPropRet1 in H
      | H : PClassical ?something |- PClassical ?something_else => pbind H
      | H : Creturn ?something <> Creturn True |- _ => apply toPropRetNot in H
      end
    | apply toPropRet2
    | rewrite bindDef in *
    | rewrite toPropRetEq in *].

Theorem classical_consistent : [False] -> False.
Proof.
  auto.
Qed.

Theorem eqLem (P : Prop) : [P = [P]].
Proof.
  apply (Pbind (Plem P)).
  intros PornotP.
  destruct PornotP.
  - apply Preturn.
    apply propositional_extensionality.
    split.
    + intros _ np.
      auto.
    + auto.
  - apply Preturn.
    apply propositional_extensionality.
    split.
    + intros.
      apply Preturn.
      assumption.
    + intros.
      contradiction.
Qed.

Theorem PFunbind {T : Type} {A : T -> Prop} {B : Prop}
        (pa : forall t, [A t]) (f : (forall t, A t) -> [B]) : [B].
Proof.
Abort. (* I think that this isn't true *)

Theorem classical_not_forall' T P
  : (~ forall (t : T), [P t]) -> [exists t, ~P t].
Proof.
  intros F E.
  apply F.
  intros t Pt .
  apply E.
  exists t.
  assumption.
Qed.

Theorem IdontSupposeThatThisIsTrue (T : Type) (P Q : T -> Prop)
        (H : (forall t, [P t]) = (forall t, [Q t]))
  : (forall t, P t) = (forall t, Q t).
Proof.
  apply propositional_extensionality.
  split.
  - intros.
Abort.

Theorem HowAboutThis (A B : Prop) : [A -> B] = (A -> [B]).
Proof.
  apply propositional_extensionality.
  split.
  - intros.
    pbind H.
    apply H in H0.
    apply Preturn.
    assumption.
  - intros.
    intros f.
    apply f.
    intro a.
    apply H in a.
    exfalso.
    apply classical_consistent.
    pbind a.
    apply Preturn.
    apply f.
    intros.
    assumption.
Qed.
(*
What actually happened in this proof? I feel stupider by the minute.
 *)

Theorem isItTrueWithDependentTypes (A : Prop) B : [forall (a : A), B a] = forall a, [B a].
Proof.
  apply propositional_extensionality.
  split.
 - intros.
    pbind H.
    specialize (H a).
    apply Preturn.
    assumption.
  - intros.
    intros f.
    apply f.
    intro a.
    specialize (H a).
    exfalso.
    apply classical_consistent.
    pbind H.
    apply Preturn.
    apply f.
    intros.
    rewrite (proof_irrelevance A a0 a).
    assumption.
Qed.
(*
Yes, but I need everything to be propositions, or else the sizes of the types would be different!
But if A is a proposition then this is pretty useless.
 *)

(*
Theorem howAboutThisOne (A : Type) (B : A -> Prop) : [forall (a : A), B a] = [forall a, [B a]].
Proof.
  Print inhabited.
  Search inhabited.
  pose (B' := (fun a' => (match a' with inhabits a => B a end) : Prop) : (inhabited A -> Prop)).
  (* The idea is to show that this is equivalent to something where A is a prop, and use the other
   version *)
  (* It seems like the extra [] doesn't really help in the proof. *)
Abort.
*)

(* Its surprising to me that this seems to not be true *)
Theorem classical_not_forall T P
  : (~ forall (t : T), P t) -> [exists t, ~P t].
Proof.
Abort.

Theorem not_exists (T : Type) (P : T -> Prop) (E : ~exists t, P t)
  : forall t, ~(P t).
Proof.
  intros t Pt.
  apply E.
  exists t.
  assumption.
Qed.

Theorem forall_to_exists (T : Type) (P : T -> Prop)
        (F : forall t, ~(P t))
  : ~exists t, P t.
Proof.
  intros [t Pt].
  apply (F t Pt).
Qed.

Theorem not_forall (T : Type) (P : T -> Prop)
        (F : ~forall t, P t)
  : exists t, ~P t.
  pose (P' := fun t => ~P t).
Abort.

Theorem not_forall_2 (T : Type) (P : T -> Prop) (Q : forall t, P t -> Prop)
        (F : ~forall t (p : P t), [Q t p])
  : [exists t, exists (p : P t), ~Q t p].
Proof.
  intros E.
  apply F.
  intros t p nq.
  apply E.
  eauto.
Qed.

Theorem not_and (P Q : Prop)
        (H : ~ (P /\ Q))
  : [~P \/ ~Q].
Proof.
  apply (Pbind (Plem P)); intros PornotP.
  destruct PornotP; apply Preturn.
  - apply or_intror.
    intros q.
    apply H; auto.
  - apply or_introl.
    assumption.
Qed.
