Require Import QArith.
Require Import Qabs.
Require Import util.
Require Import base.
Require Import QOrderedType.

(* This file has helper lemmas about rational numbers and integers that are used in cauchy.v *)

Lemma write_frac_as_Qmake : forall {z : Z},
    Z.lt 0 z ->
    1 / (inject_Z z) = Qmake 1 (Z.to_pos z).
Proof.
  intros.
  destruct z.
  - simpl.
    inversion H.
  - simpl.
    unfold Qdiv, Qinv, Qmult.
    simpl.
    reflexivity.
  - inversion H.
Qed.

Lemma Z_lt_le_off_by_one : forall x : Z,
    (0 < x)%Z -> (1 <= x)%Z.
Proof.
  intros.
  apply Zorder.Zlt_0_le_0_pred in H.
  apply (Zorder.Zplus_le_compat_r 0 (Z.pred x) 1) in H.
  rewrite <- Z.sub_1_r in H.
  ring_simplify in H.
  assumption.
Qed.

Lemma QabsPlus1 : forall x, 0 < (Qabs x) + 1.
Proof.
  intros.
  apply (Qle_lt_trans _ (Qabs x)).
  - apply Qabs_nonneg.
  - apply (Qplus_lt_l _ _ (- (Qabs x))).
    field_simplify.
    repeat constructor.
Qed.

Lemma Qabs2Plus1 : forall x y, 0 < (Qabs x) + (Qabs y) + 1.
Proof.
  intros.
  apply (Qle_lt_trans _ (Qabs x)).
  - apply Qabs_nonneg.
  - apply (Qplus_lt_l _ _ (- (Qabs x))).
    field_simplify.
    apply QabsPlus1.
Qed.

Lemma add_a_Qabs : forall x y z, x <= y -> x <= Qabs z + y.
Proof.
  intros.
  apply (Qle_trans _ y).
  - assumption.
  - apply (Qplus_le_l _ _ (-y)).
    field_simplify.
    apply Qabs_nonneg.
Qed.
      
Lemma Qeq_le : forall {x y}, Qeq x y -> Qle x y.
Proof.
  intros.
  apply Qle_lteq.
  apply or_intror.
  assumption.
Qed.

Lemma Qplus_compat : forall {a b c d : Q}, a == c -> b == d -> a + b == c + d.
Proof.
  intros.
  apply (Qeq_trans _ (a + d)).
  - apply Qplus_inj_l.
    assumption.
  - apply Qplus_inj_r.
    assumption.
Qed.

Lemma Qabs_compat : forall {x y : Q}, x == y -> Qabs x == Qabs y.
Proof.
  intros.
  apply Qabs_wd_Proper.
  assumption.
Qed.

Lemma Qmult_compat : forall {a b c d : Q},
    a >= 0 -> b >= 0
    -> c >= a -> d >= b
    -> a * b <= c * d.
Proof.
  intros.

  apply (Qle_trans _ (c * b)).
  -
    apply Qmult_le_compat_r; assumption.
  - apply (Qle_trans _ (b * c)).
    + apply Qeq_le.
      apply Qmult_comm.
    + apply (Qle_trans _ (d * c)).
      * apply Qmult_le_compat_r; auto.
        apply (Qle_trans _ _ _ H H1).
      * apply Qeq_le.
        apply Qmult_comm.
Qed.

Lemma Qinv_def : forall {x : Q}, 1 / x = /x.
Proof.
  intros.
  destruct x.
  destruct Qnum; auto.
Qed.

Lemma Qle_compat : forall {a b c d : Q},
    a == c -> b == d
    -> Qle c d
    -> Qle a b.
Proof.
  intros.
  apply (Qle_trans _ c).
  - apply Qeq_le.
    assumption.
  - apply (Qle_trans _ d).
    + assumption.
    + apply Qeq_le.
      apply Qeq_sym.
      assumption.
Qed.

Lemma pow_nonzero : forall n, ~ inject_Z (2 ^ Z.of_nat n) == 0.
Proof.
  intros n p.
  assert (0 == inject_Z 0) as p' by field.
  apply (Qeq_trans _ _ _ p) in p'.
  clear p.
  apply -> inject_Z_injective in p'.
  refine (Z.pow_nonzero _ _ _ _ p').
  - easy.
  - apply Zorder.Zle_0_nat.
Qed.

Lemma bound_lemma_1 : forall {a b c a' : Q},
    a' >= a
    -> a' - b <= c
    -> a - b <= c.
Proof.
  intros.
  apply (Qplus_le_l _ _ (-b)) in H.
  apply (Qle_trans _ _ _ H) in H0.
  assumption.
Qed.

Lemma bound_lemma_2 : forall {a b c b' : Q},
    b' <= b
    -> a - b' <= c
    -> a - b <= c.
Proof.
  intros.
  apply Qopp_le_compat in H.
  apply (Qplus_le_r _ _ a) in H.
  apply (Qle_trans _ _ _ H) in H0.
  assumption.
Qed.

Lemma Qopp_le_compat2 : forall p q : Q, - p <= - q -> q <= p.
Proof.
  intros.
  apply (Qplus_le_r _ _ p) in H.
  field_simplify in H.
  apply Qle_minus_iff.
  assumption.
Qed.

Theorem Q_not_eq_lemma : forall x y : Q, ~ (x == y) -> [Qabs (x - y) > 0].
Proof.
  intros.
  assert (~ (x - y) == 0). {
    intros p.
    apply H.
    apply (Qplus_inj_r _ _ y) in p.
    field_simplify in p.
    assumption.
  }
  apply (Pbind (Plem (0 < Qabs (x - y)))); intros.
  destruct H1.
  - apply Preturn.
    assumption.
  - apply Qnot_lt_le in H1.
    apply Qabs_Qle_condition in H1.
    destruct H1.
    field_simplify in H1.
    assert (reverse := @QOrder.le_antisym _ _ H1 H2).
    apply Qeq_sym in reverse.
    contradiction.
Qed.

Theorem Q_not_eq_lemma_2 : forall x y : Q, Qabs (x - y) > 0 -> ~ x == y.
Proof.
  intros.
  intros p.
  apply (Qplus_inj_r _ _ (-y)) in p.
  field_simplify in p.
  apply Qabs_wd in p.
  apply (fun x => Qlt_le_trans _ _ _ x (Qeq_le p)) in H.
  inversion H.
Qed.

Theorem Q_not_eq_lemma_3 : forall x : Q, Qabs x > 0 -> ~ x == 0.
Proof.
  intros.
  apply Q_not_eq_lemma_2.
  field_simplify (x - 0).
  assumption.
Qed.

Theorem Qnot_eq_decide : forall x y, ~(x == y) -> [x < y \/ y < x].
Proof.
  intros.
  apply (Pbind (Plem (x < y))); intros.
  destruct H0.
  - apply Preturn.
    apply or_introl.
    assumption.
  - apply QOrder.not_gt_le in H0.
    apply Qnot_eq_sym in H.
    apply Preturn.
    apply or_intror.
    apply (@QOrder.le_neq_lt _ _ H0 H).
Qed.

Theorem Q_pos_neg_cases : forall q, q <= 0 \/ 0 <= q.
Proof.
  intros.
  destruct (QOrder.TO.lt_total q 0).
  - apply or_introl.
    apply Qlt_le_weak.
    assumption.
  - destruct H.
    + apply or_introl.
      apply Qeq_le.
      assumption.
    + apply or_intror.
      apply Qlt_le_weak.
      assumption.
Qed.
