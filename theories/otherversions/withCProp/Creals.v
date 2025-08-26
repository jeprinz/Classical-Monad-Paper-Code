Require Import Cquotient.
Require Import Cbase.
Require Import Ccauchy.


(*
Having formalized cauchy sequences up to equivalence in cauchy.v,
and quotients, here I put them together into a type of real numbers
using equality

In reals2, I'm using quotient2
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
(* The idea is that I can use sigEq2 and sound somehow, without using ind *)

Definition Cinv' (x : cauchy) : [[|cauchy|]] :=
  Pif' (Ceq x Czero) (fun _ => Czero) (fun nonzero => Cinv x nonzero).

Definition Rinv' (x : R) (*H : x <> Rzero*) : R.
  Check Reals.lift.
  apply Reals.unwrap_quot.
  (*refine (Reals.lift (fun x => Creturn (Reals.mk (Cinv x _))) _ x).*)
  Check Cbind.
  Check Reals.lift.
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
(*
TODO: I should probably modify cauchy.v so that Cinv doesn't input the != 0 part,
and that part is just in the field axiom statements.
On second thought, this is not how it works in the Rocq stdlib reals.
 *)

Check ClassicalInd.
Check Reals.isMk.




(* but then how do I prove stuff like: *)
Check multiplicative_inverse_l.
Theorem Cmultipliciative_inverse_l : forall (x : R) (H : x <> Rzero), Rmult (Rinv x H) x = Rone.
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
