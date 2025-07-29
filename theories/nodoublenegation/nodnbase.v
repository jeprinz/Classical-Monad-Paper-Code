(* In this file, I'm testing why I needed CProp *)

Require Import Coq.Logic.ProofIrrelevance.
(* Instead of using SProp, for now I'll just use the proof irrelevance axiom.
   I'll see if this causes any issues; probably not. *)
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

(*
In this versin of the monad for choice, I'm going to try making a special type of propositions that
are all in the double negation monad.
Following specialprop.agda
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

(* The "Unique" monad, that represents a unique thing that exists non-constructively *)
Definition Classical (A : Type) : Type :=
  {S : A -> Prop | (exists a, S a)
                    /\ (forall x y, S x /\ S y -> x = y)}.

Definition Creturn {A : Type} (x : A) : Classical A.
  refine (exist _ (fun y => y = x) _).
  split.
  - exists x.
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
  - destruct nonempty.
    remember (f x) as fx.
    destruct fx as [x0 [p sfsdfd]].
    destruct p.
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
  : exists x, Creturn x = t /\ (proj1_sig t x).
Proof.
  destruct t as [St [nonempty same]].
  destruct nonempty as [a ta].
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
           (nonempty : (exists t, P t))
           (unique : forall x y, P x /\ P y -> x = y)
  : Classical T.
  refine (exist _ P _).
  split.
  - simpl.
    specialize nonempty as [t Pt].
    exists t.
    assumption.
  - intros x y [Px Py].
    simpl in *.
    specialize (unique _ _ (conj Px Py)).
    assumption.
Defined.

(* This is the exact same thing as ClassicalInd... *)
Theorem choiceInd : forall (T : Type) (P : T -> Prop) (Q : Classical T -> Prop)
                            nonempty unique,
    (forall t, P t -> Q (Creturn t))
    -> Q (@choose T P nonempty unique).
Proof.
  intros.
  assert (x := (ClassicalInd _ (choose T P nonempty unique))).
  simpl.
  specialize x as [St [eq PSt]].
  rewrite <- eq.
  clear eq.
  destruct nonempty as [t Pt].
  specialize (H _ Pt).
  rewrite <- (unique _ _ (conj Pt PSt)).
  assumption.
Qed.
