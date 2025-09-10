Require Import quotient.
Require Import base.
Require Import cauchy.
Require Import Stdlib.Logic.PropExtensionality.


(*
Having formalized cauchy sequences up to equivalence in cauchy.v,
and quotients, here I put them together into a type of real numbers
using equality
 *)

Module CauchyEq <: EqRel. (*NOTE: <: makes the contents transparent from the outside, as oppsed to : *)
  Definition A := cauchy.
  Definition R := Ceq.
  Definition Rsym := Ceq_sym.
  Definition Rtrans := Ceq_trans.
  Definition Rrefl := Ceq_refl.
End CauchyEq.

Module Reals := Quotient CauchyEq.

Definition R := Reals.t.

Definition Rzero := Reals.mk Czero.
Definition Rone := Reals.mk Cone.
Definition Rplus : R -> R -> R := Reals.map2 Cplus plus_respects_cauchy.
Definition Rmult : R -> R -> R := Reals.map2 Cmult mult_respects_cauchy.
Definition Ropp : R -> R := Reals.map Cnegate Cnegate_respects_cauchy.

Definition Rle (x y : R) : Prop.
  refine (toProp (Reals.lift2 (fun x y => Creturn (Cle x y)) _ x y)).
  intros.
  apply f_equal.
  unfold CauchyEq.R in *.
  apply propositional_extensionality.
  split.
  - intros.
    apply Ceq_sym in H.
    apply Ceq_Cle in H, H0.
    apply (Cle_trans _ _ _ H).
    apply (Cle_trans _ _ _ H1).
    assumption.
  - intros.
    apply Ceq_sym in H0.
    apply Ceq_Cle in H, H0.
    apply (Cle_trans _ _ _ H).
    apply (Cle_trans _ _ _ H1).
    assumption.
Defined.

Theorem Rle_refl (x : R) : Rle x x.
Proof.
  Reals.quot_induction x.
  rewrite Reals.lift2_eq.
  apply Preturn.
  apply f_equal.
  Search (_ = True).
  apply PropExtensionalityFacts.PropExt_imp_ProvPropExt.
  apply propositional_extensionality.
  apply Ceq_Cle.
  apply Ceq_refl.
Qed.

Theorem Rle_antisymmetry (x y : R) (H1 : Rle x y) (H2 : Rle y x) : x = y.
Proof.
  apply Reals.unwrap_eq_quot.
  Reals.quot_induction x.
  Reals.quot_induction y.
  Check Reals.complete.
  unfold Rle in H1, H2.
  rewrite Reals.lift2_eq in H1, H2.
  classical_auto.
  apply Preturn.
  apply Reals.sound.
  apply Cle_antisymmetry; auto.
Qed.

Theorem Rle_trans (x y z : R) (H1 : Rle x y) (H2 : Rle y z) : Rle x z.
Proof.
  Reals.quot_induction x.
  Reals.quot_induction y.
  Reals.quot_induction z.
  unfold Rle in *.
  rewrite Reals.lift2_eq in *.
  classical_auto.
  apply Preturn.
  apply (Cle_trans _ x1); assumption.
Qed.

Theorem R_additive_identity_r : forall x, Rplus Rzero x = x.
Proof.
  intros.
  apply Reals.unwrap_eq_quot.
  Reals.quot_induction x.
  apply Preturn.
  unfold Rzero, Rplus.
  rewrite Reals.map2_eq.
  apply Reals.sound.
  apply additive_identity_r.
Qed.

Definition Rinv' (x : R) (*H : x <> Rzero*) : R.
  apply Reals.unwrap_quot.
  refine (Reals.lift (fun x => (Pif' (~ Ceq x Czero)
                                     (fun nonzero => Reals.mk (Cinv x nonzero))
                                     (fun _ => Rzero))) _ x).
  intros.
  apply unwrap_eq.
  apply (Pbind (Plem (~ Ceq a Czero))); intros eqornoteq.
  destruct eqornoteq.
  - rewrite (Pif'Def1 _ _ _ H0).
    assert (~ Ceq b Czero). {
      intros p.
      apply (Ceq_trans _ _ _ H) in p.
      contradiction.
    }
    rewrite (Pif'Def1 _ _ _ H1).
    apply Preturn.
    apply f_equal.
    apply Reals.sound.
    apply Cinv_respects_cauchy.
    assumption.
  - rewrite (Pif'Def2 _ _ _ H0).
    assert (~ ~ Ceq b Czero). {
      intros neq.
      apply classical_consistent.
      pbind H0.
      apply Ceq_sym in H.
      apply (Ceq_trans _ _ _ H) in H0.
      contradiction.
    }
    rewrite (Pif'Def2 _ _ _ H1).
    apply Preturn.
    reflexivity.
Defined.

Definition Rinv (x : R) (H : x <> Rzero) : R := Rinv' x.

Theorem Rinv_def (x : cauchy) (H : ~ Ceq x Czero) : Rinv' (Reals.mk x) = Reals.mk (Cinv x H).
Proof.
  unfold Rinv'.
  rewrite Reals.lift_eq.
  rewrite (Pif'Def1 _ _ _ H).
  Search Reals.unwrap_quot.
  rewrite Reals.unwrapDef.
  apply Reals.sound.
  apply Ceq_refl.
Qed.

Theorem Radditive_identity_l : forall x, (Rplus x Rzero) = x.
Proof.
  intros.
  apply Reals.unwrap_eq_quot.
  Reals.quot_induction x.
  unfold Rzero.
  unfold Rplus.
  rewrite Reals.map2_eq.
  apply Preturn.
  apply Reals.sound.
  apply additive_identity_l.
Qed.

Theorem Radditive_identity_r : forall x, (Rplus Rzero x) = x.
Proof.
  intros.
  apply Reals.unwrap_eq_quot.
  Reals.quot_induction x.
  unfold Rzero.
  unfold Rplus.
  rewrite Reals.map2_eq.
  apply Preturn.
  apply Reals.sound.
  apply additive_identity_r.
Qed.

Theorem Radditive_inverse_l : forall x : R, (Rplus (Ropp x) x) = Rzero.
Proof.
  intros.
  apply Reals.unwrap_eq_quot.
  Reals.quot_induction x.
  apply Preturn.
  unfold Ropp.
  rewrite Reals.map_eq.
  unfold Rplus.
  rewrite Reals.map2_eq.
  apply Reals.sound.
  apply additive_inverse_l.
Qed.

Theorem Radditive_inverse_r : forall x : R, (Rplus x (Ropp x)) = Rzero.
Proof.
  intros.
  apply Reals.unwrap_eq_quot.
  Reals.quot_induction x.
  apply Preturn.
  unfold Ropp.
  rewrite Reals.map_eq.
  unfold Rplus.
  rewrite Reals.map2_eq.
  apply Reals.sound.
  apply additive_inverse_r.
Qed.

Theorem Rplus_comm : forall x y, Rplus x y = Rplus y x.
  intros.
  apply Reals.unwrap_eq_quot.
  Reals.quot_induction x.
  Reals.quot_induction y.
  apply Preturn.
  unfold Rplus.
  repeat rewrite Reals.map2_eq.
  apply Reals.sound.
  apply Cplus_comm.
Qed.

Theorem Rplus_assoc : forall x y z, Rplus x (Rplus y z) = Rplus (Rplus x y) z.
  intros.
  apply Reals.unwrap_eq_quot.
  Reals.quot_induction x.
  Reals.quot_induction y.
  Reals.quot_induction z.
  apply Preturn.
  unfold Rplus.
  repeat rewrite Reals.map2_eq.
  apply Reals.sound.
  apply Cplus_assoc.
Qed.

Theorem Rmultiplicative_identity_l : forall x, (Rmult x Rone) = x.
Proof.
  intros.
  apply Reals.unwrap_eq_quot.
  Reals.quot_induction x.
  apply Preturn.
  unfold Rmult, Rone.
  repeat rewrite Reals.map2_eq.
  apply Reals.sound.
  apply multiplicative_identity_l.
Qed.

Theorem Rmultiplicative_identity_r : forall x, (Rmult Rone x) = x.
Proof.
  intros.
  apply Reals.unwrap_eq_quot.
  Reals.quot_induction x.
  apply Preturn.
  unfold Rmult, Rone.
  repeat rewrite Reals.map2_eq.
  apply Reals.sound.
  apply multiplicative_identity_r.
Qed.

Theorem Rmultiplicative_inverse_l : forall (x : R) (H : x <> Rzero), Rmult (Rinv x H) x = Rone.
Proof.
  intros.
  apply Reals.unwrap_eq_quot.
  unfold Rinv.
  Reals.quot_induction x.
  apply Preturn.
  intros.
  assert (~ Ceq x0 Czero). {
    intros p.
    apply Reals.sound in p.
    contradiction.
  }
  rewrite (Rinv_def _ H0).
  unfold Rmult.
  rewrite Reals.map2_eq.
  apply Reals.sound.
  apply multiplicative_inverse_l.
Qed.

Theorem Rmultiplicative_inverse_r : forall (x : R) (H : x <> Rzero), Rmult x (Rinv x H) = Rone.
Proof.
  intros.
  apply Reals.unwrap_eq_quot.
  unfold Rinv.
  Reals.quot_induction x.
  apply Preturn.
  intros.
  assert (~ Ceq x0 Czero). {
    intros p.
    apply Reals.sound in p.
    contradiction.
  }
  rewrite (Rinv_def _ H0).
  unfold Rmult.
  rewrite Reals.map2_eq.
  apply Reals.sound.
  apply multiplicative_inverse_r.
Qed.

Theorem Rmult_comm : forall x y, Rmult x y = Rmult y x.
  intros.
  apply Reals.unwrap_eq_quot.
  Reals.quot_induction x.
  Reals.quot_induction y.
  apply Preturn.
  unfold Rmult.
  repeat rewrite Reals.map2_eq.
  apply Reals.sound.
  apply Cmult_comm.
Qed.

Theorem Rdistributivity : forall x y z, Rmult x (Rplus y z) = Rplus (Rmult x y) (Rmult x z).
  intros.
  apply Reals.unwrap_eq_quot.
  Reals.quot_induction x.
  Reals.quot_induction y.
  Reals.quot_induction z.
  apply Preturn.
  unfold Rmult, Rplus.
  repeat rewrite Reals.map2_eq.
  apply Reals.sound.
  apply distributivity.
Qed.

Check Cle_add_property.
Theorem Rle_add_property : forall a b, Rle Rzero a -> Rle Rzero b -> Rle Rzero (Rplus a b).
Proof.
  intros.
  Reals.quot_induction a.
  Reals.quot_induction b.
  unfold Rle, Rplus, Rzero in *.
  repeat rewrite ?Reals.lift2_eq, ?Reals.map2_eq in *.
  classical_auto.
  apply Preturn.
  apply Cle_add_property; assumption.
Qed.

Check Cle_mult_property.
Theorem Rle_mult_property : forall a b, Rle Rzero a -> Rle Rzero b -> Rle Rzero (Rmult a b).
Proof.
  intros.
  Reals.quot_induction a.
  Reals.quot_induction b.
  unfold Rle, Rmult, Rzero in *.
  repeat rewrite ?Reals.lift2_eq, ?Reals.map2_eq in *.
  classical_auto.
  apply Preturn.
  apply Cle_mult_property; assumption.
Qed.

Theorem RzeroNotOne : Rzero <> Rone.
Proof.
  intros p.
  unfold Rzero, Rone in *.
  apply Reals.complete in p.
  apply classical_consistent.
  classical_auto.
  apply Preturn.
  apply zeroNotOne.
  assumption.
Qed.
  
Theorem RzeroLeOne : Rle Rzero Rone.
Proof.
  unfold Rle, Rzero, Rone.
  repeat rewrite Reals.lift2_eq.
  classical_auto.
  apply Preturn.
  apply zeroLeOne.
Qed.
  
Check total_ordering.
Theorem Rtotal_ordering : forall x y, [Rle x y \/ Rle y x].
Proof.
  intros.
  Reals.quot_induction x.
  Reals.quot_induction y.
  unfold Rle.
  repeat rewrite Reals.lift2_eq.
  classical_auto.
  assert (couch := total_ordering x0 x1).
  classical_auto.
  apply Preturn.
  destruct couch.
  - apply or_introl.
    apply Preturn.
    assumption.
  - apply or_intror.
    apply Preturn.
    assumption.
Qed.

Check lub_but_its_only_a_prop.

Lemma Cle_is_classical x y : [Cle x y] -> Cle x y.
Proof.
  intros.
  unfold Cle.
  intros.
  classical_auto.
  apply H.
  assumption.
Qed.

Definition Rlub (S : R -> Prop)
           (inhabitant : R) (inhabited : S inhabitant)
           (bound : R) (bounded : forall r, S r -> Rle r bound)
  : R.
  refine (exist _ (fun lub => toCProp (
                  (forall r : R, S r -> [Rle r (Reals.mk lub)]) /\
                  (forall otherbound : R,
                  (forall r : R, S r -> [Rle r otherbound]) -> [Rle (Reals.mk lub) otherbound])
         )) _ ).
  split.
  - intros.
    split.
    + intros.
      classical_auto.
      assert (Reals.mk x = Reals.mk y). {
        apply Reals.sound.
        assumption.
      }
      rewrite <- H1.
      apply Preturn.
      assumption.
    + intros.
      apply Reals.complete.
      remember (Reals.mk x) as x'.
      remember (Reals.mk y) as y'.
      apply Reals.unwrap_eq_quot.
      classical_auto.
      destruct H0, H.
      specialize (H2 _ H0).
      specialize (H1 _ H).
      classical_auto.
      apply Preturn.
      apply Rle_antisymmetry; assumption.
  - Check (lub_but_its_only_a_prop).
    Check (lub_but_its_only_a_prop (fun c => S (Reals.mk c))).
    assert [exists r : cauchy, S (Reals.mk r)]. {
      Reals.quot_induction inhabitant.
      apply Preturn.
      eauto.
    }
    assert [exists b : cauchy, forall r : cauchy, S (Reals.mk r) -> Cle r b]. {
      Reals.quot_induction bound.
      Check extra_monad_exists.
      rewrite extra_monad_exists.
      apply Preturn.
      exists x.
      apply Preturn.
      intros.
      specialize (bounded (Reals.mk r) H0).
      unfold Rle in bounded; rewrite Reals.lift2_eq in bounded.
      classical_auto.
      apply Cle_is_classical.
      assumption.
    }
    assert (lub_property := lub_but_its_only_a_prop _ H H0).
    classical_auto.
    apply Preturn.
    specialize lub_property as [lub [isupper isleast]].
    exists lub.
    apply Preturn.
    split.
    + intros.
      Reals.quot_induction r.
      specialize (isupper x H1).
      apply Preturn.
      unfold Rle.
      rewrite Reals.lift2_eq.
      classical_auto.
      apply Preturn.
      assumption.
    + intros.
      Reals.quot_induction otherbound.
      specialize (isleast x).
      apply Preturn.
      unfold Rle.
      rewrite Reals.lift2_eq.
      classical_auto.
      apply Preturn.
      apply isleast.
      intros.
      specialize (H1 (Reals.mk r) H2).
      apply Cle_is_classical.
      classical_auto.
      unfold Rle in H1; rewrite Reals.lift2_eq in H1.
      classical_auto.
      apply Preturn.
      assumption.
Defined.

Theorem Rlub_is_bound (S : R -> Prop)
        (inhabitant : R) (inhabited : S inhabitant)
        (bound : R) (bounded : forall r, S r -> Rle r bound)
        (r : R) (H : S r) : Rle r (Rlub S inhabitant inhabited bound bounded).
Proof.
  Check Reals.isMk_extended.
  specialize (Reals.isMk_extended (Rlub S inhabitant inhabited bound bounded)) as ismk.
  Reals.quot_induction r.
  classical_auto.
  specialize ismk as [a [ismk prop]].
  rewrite ismk.
  rewrite Reals.lift2_eq.
  simpl in prop.
  classical_auto.
  specialize prop as [isbound isleast].
  specialize (isbound (Reals.mk x) H).
  classical_auto.
  unfold Rle in isbound; rewrite Reals.lift2_eq in isbound.
  classical_auto.
  apply Preturn.
  assumption.
Qed.

Theorem Rlub_is_optimal (S : R -> Prop)
        (inhabitant : R) (inhabited : S inhabitant)
        (bound : R) (bounded : forall r, S r -> Rle r bound)
        (otherbound : R)
        (otherbound_is_bound : forall r, S r -> Rle r otherbound)
        : Rle (Rlub S inhabitant inhabited bound bounded) otherbound.
Proof.
  Check Reals.isMk_extended.
  specialize (Reals.isMk_extended (Rlub S inhabitant inhabited bound bounded)) as ismk.
  Reals.quot_induction otherbound.
  classical_auto.
  specialize ismk as [a [ismk prop]].
  rewrite ismk.
  rewrite Reals.lift2_eq.
  simpl in prop.
  classical_auto.
  specialize prop as [isbound isleast].
  assert (forall r, S r -> [Rle r (Reals.mk x)]). {
    intros.
    apply Preturn.
    apply otherbound_is_bound.
    assumption.
  }
  specialize (isleast (Reals.mk x) H).
  classical_auto.
  unfold Rle in isleast; rewrite Reals.lift2_eq in isleast.
  classical_auto.
  apply Preturn.
  assumption.
Qed.

      
(*
Here is everything in one place to check that I have fully formalized the real numbers.
*)

(* Basic definitions *)
Check R : Type.
Check Rzero : R.
Check Rone : R.
Check Rle : R -> R -> Prop.
Check Rplus : R -> R -> R.
Check Rmult : R -> R -> R.
Check Ropp : R -> R.
Check Rinv : forall x : R, x <> Rzero -> R.

Check Rle_trans : forall x y z : R, Rle x y -> Rle y z -> Rle x z.
Check Rle_antisymmetry : forall x y : R, Rle x y -> Rle y x -> x = y.
Check Rle_refl : forall x : R, Rle x x.

(* Field Axioms *)
Check Rplus_assoc : forall x y z, Rplus x (Rplus y z) = Rplus (Rplus x y) z.
Check Radditive_identity_l : forall x, Rplus x Rzero = x.
Check Radditive_identity_r : forall x, Rplus Rzero x = x.
Check Radditive_inverse_l : forall x, Rplus (Ropp x) x = Rzero.
Check Radditive_inverse_r : forall x, Rplus x (Ropp x) = Rzero.
Check Rplus_comm : forall x y, Rplus x y = Rplus y x.
Check Rplus_assoc : forall x y z, Rplus x (Rplus y z) = Rplus (Rplus x y) z.
Check Rmultiplicative_identity_l : forall x, Rmult x Rone = x.
Check Rmultiplicative_identity_r : forall x : R, Rmult Rone x = x.
Check Rmultiplicative_inverse_l : forall x (H : x <> Rzero), Rmult (Rinv x H) x = Rone.
Check Rmultiplicative_inverse_r : forall x (H : x <> Rzero), Rmult x (Rinv x H) = Rone.
Check Rmult_comm : forall x y, Rmult x y = Rmult y x.
Check Rdistributivity : forall x y z, Rmult x (Rplus y z) = Rplus (Rmult x y) (Rmult x z).

(* Total ordering *)
Check Rtotal_ordering. (* This is the only one of the axioms that needs to be under a monad *)
Check Rle_add_property.
Check Rle_mult_property.
Check RzeroNotOne.
Check RzeroLeOne.

(* least upper bounds *)
Check Rlub.
Check Rlub_is_bound.
Check Rlub_is_optimal.
  
(* The only axioms used are functional and propositional extensionality, as this command shows: *)
Definition all_definitions :=
  (R, Rle, Rplus, Rmult, Ropp, Rinv, Rzero, Rone,
    Rle_trans, Rle_antisymmetry, Rle_refl,
    Rplus_assoc, Radditive_identity_l, Radditive_identity_r, Radditive_inverse_l,
    Radditive_inverse_r, Rplus_comm, Rplus_assoc, Rmultiplicative_identity_r,
    Rmultiplicative_identity_l, Rmultiplicative_inverse_l, Rmultiplicative_inverse_r, Rmult_comm,
    Rdistributivity,
    Rtotal_ordering, Rle_add_property, Rle_mult_property, RzeroNotOne, RzeroLeOne,
    Rlub, Rlub_is_bound, Rlub_is_optimal).

Print Assumptions all_definitions.
