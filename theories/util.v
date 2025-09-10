Require Import PropExtensionality. (*this line also imports proof irrelevance*)

Theorem f_equal_dep_prop (A B : Type) (P : A -> Prop)
        (f : forall (a : A), P a -> B)
        (a1 a2 : A)
        (p1 : P a1)
        (p2 : P a2)
        (eqa : a1 = a2)
  : f a1 p1 = f a2 p2.
Proof.
  subst.
  apply f_equal.
  apply proof_irrelevance.
Qed.

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


Theorem not_exists (T : Type) (P : T -> Prop) (E : ~exists t, P t)
  : forall t, ~(P t).
Proof.
  intros t Pt.
  apply E.
  exists t.
  assumption.
Qed.