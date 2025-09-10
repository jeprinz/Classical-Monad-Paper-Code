Require Import quotient2.
Require Import base.
Require Import cauchy.


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

Check additive_identity_l.
Check Reals.ind.
Theorem R_additive_identity_r : forall x, [Rplus Rzero x = x].
Proof.
  intros.
  apply (Reals.ind (fun x => Rplus Rzero x = x)).
  intros.
  apply Preturn.
  unfold Rzero, Rplus.
  rewrite Reals.map2_eq.
  apply Reals.sound.
  apply additive_identity_r.
Qed.
(* The idea is that I can use sigEq2 and sound somehow, without using ind *)

Check Reals.ind.

Definition Rinv (x : R) (H : x <> Rzero) : [[|R|]].
  Check Reals.lift.
  refine (Reals.lift (fun x => _) _ x).
  Unshelve.
  2: {
    Check Reals.sound.
  
  Check Reals.ind.
  Check (fun x => Cinv x).
  apply (Reals.ind (fun _ => R)).
  refine (Reals.mk 
  shelve.
  Unshelve.
  - intros p.
    apply Reals.sound in p.
    
  intros.
  
  
Import (Quotient CauchyEq).
Definition R := Quo
