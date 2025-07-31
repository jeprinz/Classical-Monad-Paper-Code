Require Import base.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import PropExtensionality. (*this line also imports proof irrelevance*)
Require Import FunctionalExtensionality.

Module Type EqRel.
  Parameter A : Type.
  Parameter R : relation A.
  Parameter Rsym : forall a b, R a b -> R b a.
  Parameter Rtrans : forall a b c, R a b -> R b c -> R a c.
  Parameter Rrefl : forall a, R a a.
End EqRel.

Module Quotient (EqRel : EqRel).

  Import EqRel.

  (* The quotient type *)

  Definition t : Type :=
    {S : A -> Prop | (forall x y, S x -> (R x y <-> S y)) /\ (exists a, S a)}.

  Lemma quotientEq :
    forall S1 S2 p1 p2,
      S1 = S2 -> @eq t (exist _ S1 p1) (exist _ S2 p2).
  Proof.
    intros.
    subst S1.
    assert (p1 = p2).
    apply proof_irrelevance.
    subst p1.
    reflexivity.
  Qed.

  Lemma quotientEq2:
    forall (x y : t), proj1_sig x = proj1_sig y -> x = y.
  Proof.
    intros.
    destruct x.
    destruct y.
    simpl in H.
    apply quotientEq.
    assumption.
  Qed.
  
  Definition mk (a : A) : t.
    refine (exist _ (fun a' => R a' a) _).
    subst.
    split.
    - intros.
      split.
      + intros.
        apply Rsym in H0.
        eapply Rtrans.
        apply H0.
        apply H.
      + intros.
        eapply Rtrans.
        apply H.
        apply Rsym in H0.
        apply H0.
    - exists a.
      apply Rrefl.
  Defined.

  Theorem ind : forall (P : t -> Prop), (forall (a : A), P (mk a)) -> forall (q : t), (P q).
  Proof.
    intros.
    remember q as q'.
    destruct q as [S [property [a aInS]]].
    assert (q' = (mk a)). {
      subst.
      apply quotientEq.
      extensionality a'.
      apply propositional_extensionality.
      split.
      - intros.
        apply property; assumption.
      - intros.
        specialize (property a a' aInS).
        apply property.
        apply Rsym.
        apply H0.
    }
    rewrite H0.
    apply H.
  Qed.

  Theorem isMk : forall (x : t), exists a, x = mk a.
  Proof.
    intros.
    Check (ind).
    apply (ind (fun t => exists a, t = mk a)).
    intros.
    exists a.
    auto.
  Qed.

  Theorem sound : forall a b, R a b -> mk a = mk b.
  Proof.
    intros.
    apply quotientEq2.
    simpl.
    extensionality a'.
    apply propositional_extensionality.
    split.
    - intros.
      eapply Rtrans.
      apply H0.
      apply H.
    - intros.
      eapply Rtrans.
      apply H0.
      apply Rsym.
      apply H.
  Qed.

  Theorem complete : forall a b, mk a = mk b -> R a b.
  Proof.
    intros.
    apply (@f_equal _ _ (@proj1_sig _ _)) in H.
    simpl in H.
    apply (@f_equal _ _ (fun f => f a)) in H.
    rewrite <- H.
    apply Rrefl.
  Qed.

  Definition lift {T : Type} (f : A -> Classical T)
             (respects : forall a b, R a b -> f a = f b)
             (x : t) : Classical T.
    refine (exist _ (fun t0 => forall a, proj1_sig x a -> proj1_sig (f a) t0) _).
    destruct x as [S [SR [a Sa]]].
    simpl.
    split.
    -
      remember (f a) as fa.
      destruct fa as [St [tnonempty tunique]].
      simpl in *.
      apply (Pbind tnonempty).
      intros [t Stt].
      apply Preturn.
      exists t.
      intros.
      assert (R a a0) as Raa0. {
        apply SR; assumption.
      }
      specialize (respects _ _ Raa0).
      rewrite <- respects.
      rewrite <- Heqfa.
      simpl.
      assumption.
    - intros x y [fax fay].
      specialize (fax a Sa).
      specialize (fay a Sa).
      Check (proj2_sig (f a)).
      destruct (proj2_sig (f a)) as [_ unique].
      specialize (unique _ _ (conj fax fay)).
      assumption.
  Defined.

  Theorem lift_eq : forall {T : Type} (f : A -> Classical T)
                           (respects : forall a b, R a b -> f a = f b)
                           (a : A), lift f respects (mk a) = f a.
  Proof.
    intros.
    apply sigEq2.
    simpl.
    extensionality t0.
    apply propositional_extensionality.
    split.
    - intros.
      specialize (H a (Rrefl _)).
      assumption.
    - intros.
      specialize (respects _ _ H0).
      rewrite respects.
      assumption.
  Qed.

  (* Just testing stuff here, this isn't going to work. *)
  Definition lift2 {T : Type} (f : A -> T)
             (respects : forall a b, R a b -> f a = f b)
             (x : t) : exists t : T, exists a : A, x = mk a /\ f a = t.
  Proof.
    destruct (isMk x) as [a p].
    subst.
    exists (f a).
    exists a.
    auto.
  Qed.
   
End Quotient.
