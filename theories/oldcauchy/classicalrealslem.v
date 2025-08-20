Require Import Stdlib.Reals.Reals.

Theorem excluded_middle_from_classical_reals :
  forall (P : Prop), P \/ ~P.
Proof.
  intros.
  pose (S := (fun r : R => P /\ r = 1   \/   r = 0)%R).
  assert (bound S) as bounded. {
    unfold bound, is_upper_bound.
    exists 1%R.
    intros.
    unfold S in H.
    destruct H.
    - destruct H.
      subst.
      apply Rle_refl.
    - subst.
      apply Rle_0_1.
  }
  
  assert (exists x, S x) as nonempty. {
    exists (0 : R).
    subst S.
    simpl.
    apply or_intror.
    reflexivity.
  }
    
  assert (Slub := completeness S bounded nonempty).

  destruct Slub as [upperbound [upper maximal]].
  unfold is_upper_bound in upper, maximal.

  assert (ub_gt_zero := total_order_T 0%R upperbound).

  destruct ub_gt_zero as [rest |]; [destruct rest|].
  - apply or_introl.

    (* for this to work, we would need to be able to prove that (S 1)*)
    (* or to look at it another way, we need to show that the least upper bound
     of S is in S. 

     Surely this is possible?
     S is a bounded set of integers, and bounded sets of integers have lubs
     that are in the set.*)

    (*
      I think that this doesn't work.
      We still can compute whether or not P is true, and could even prove
      ~~P + ~P
      which to be clear, is not true generally.
     *)
Abort.

Definition set_of (P : Prop) (r : R) : Prop :=
  P /\ r = 1%R \/ r = 0%R.
Check completeness.

Theorem when_true P (p : P) : is_lub (set_of P) 1%R.
Proof.
  unfold is_lub.
  split.
  - unfold is_upper_bound.
    intros.
    unfold set_of in H.
    destruct H.
    + destruct H.
      subst.
      apply Rle_refl.
    + subst.
      apply Rle_0_1.
  - intros.
    unfold is_upper_bound in H.
    assert (set_of P 1). {
      unfold set_of.
      apply or_introl.
      auto.
    }
    specialize (H 1%R H0).
    assumption.
Qed.

Theorem when_false P (np : ~ P) : is_lub (set_of P) 0%R.
Proof.
  unfold is_lub.
  split.
  - unfold is_upper_bound.
    intros.
    unfold set_of in H.
    destruct H.
    + destruct H.
      contradiction.
    + subst.
      apply Rle_refl.
  - intros.
    unfold is_upper_bound in H.
    assert (set_of P 0). {
      unfold set_of.
      apply or_intror.
      auto.
    }
    specialize (H 0%R H0).
    assumption.
Qed.

Check completeness.

Search is_lub.
(* need to know that lubs are unique *)
  
Definition prop_to_bool (P : Prop) : bool.
  pose (S := (fun r : R => P /\ r = 1   \/   r = 0)%R).
  assert (bound S) as bounded. {
    unfold bound, is_upper_bound.
    exists 1%R.
    intros.
    unfold S in H.
    destruct H.
    - destruct H.
      subst.
      apply Rle_refl.
    - subst.
      apply Rle_0_1.
  }
  
  assert (exists x, S x) as nonempty. {
    exists (0 : R).
    subst S.
    simpl.
    apply or_intror.
    reflexivity.
  }
    
  assert (Slub := completeness S bounded nonempty).

  destruct Slub as [upperbound [upper maximal]].
  assert (ub_gt_zero := total_order_T 0%R upperbound).

  destruct ub_gt_zero as [rest |]; [destruct rest|].
  - exact true.
  - exact false.
  - (* we can derive a contradiction in this case but does it matter? *)
    (*specialize (maximal 0%R).
    assert (is_upper_bound S 0%R) as zerobound. {
     *)
    exact false.
Defined.

Theorem of_True : prop_to_bool True = true.
Proof.
  unfold prop_to_bool.
  simpl.
  
Theorem nat_lub_thing
        (S : nat -> Prop)
        (bound : nat)
        (bounded : forall x, S x -> le x bound)
        (optimal : forall y, (forall z, S z -> le z y) -> le bound y)
  : S bound.
Proof.
  
Abort.

(* Yeah I'm pretty sure that that doesn't work. *)
