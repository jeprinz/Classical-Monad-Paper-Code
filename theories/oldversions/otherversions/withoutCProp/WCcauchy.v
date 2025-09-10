Require Import base.
Require Import QArith.
Require Import Qabs.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Nat.
Require Import PeanoNat.
Require Import QOrderedType.
Require Import PosDef.
Require Import IntDef.

(* Classical rational number *)
Definition CQ := Classical Q.

Record cauchy : Type :=
  { seq : nat -> CQ
  ; property : forall epsilon : Q, epsilon > 0 -> [exists N : nat,
     forall n m : nat, le N n -> le N m ->
     toProp (
         Cbind (seq n) (fun x => Cbind (seq m) (fun y =>
         Creturn (Qle (Qabs (x - y)) epsilon))))]

  }.

(* Maybe I need an [] around the exists N ??? *)
Definition Ceq (seq1 seq2 : cauchy) : Prop :=
    forall epsilon : Q, epsilon > 0 -> [exists N : nat, forall n : nat, le N n ->
     toProp (
     Cbind (seq seq1 n) (fun x => Cbind (seq seq2 n) (fun y =>
     Creturn (Qle (Qabs (x - y)) epsilon))))].

Definition Cle (seq1 seq2 : cauchy) : Prop :=
    forall epsilon : Q, epsilon > 0 -> [exists N : nat, forall n : nat, le N n ->
     toProp (
     Cbind (seq seq1 n) (fun x => Cbind (seq seq2 n) (fun y =>
     Creturn (Qle (x - y) epsilon))))].

Definition Clt (seq1 seq2 : cauchy) : Prop := Cle seq1 seq2 /\ ~ Ceq seq1 seq2.

Definition Cplus (seq1 seq2 : cauchy) : cauchy.
  refine {| seq := (fun n => Cbind (seq seq1 n) (fun x =>
                            Cbind (seq seq2 n) (fun y =>
                            Creturn (Qplus x y))))|}.
  intros.
  pose (halfe := Qdiv epsilon 2).
  assert (halfe > 0) as Hh. {
    apply Qmult_lt_0_compat.
    - assumption.
    - apply Qinv_lt_0_compat.
      repeat constructor.
  }
  assert (property1 := property seq1 halfe Hh).
  assert (property2 := property seq2 halfe Hh).
  classical_auto.
  specialize property1 as [N1 p1].
  specialize property2 as [N2 p2].
  apply Preturn.
  exists (max N1 N2).
  intros.

  specialize (p1 n m (Nat.max_lub_l _ _ _ H0) (Nat.max_lub_l _ _ _ H1)).
  specialize (p2 n m (Nat.max_lub_r _ _ _ H0) (Nat.max_lub_r _ _ _ H1)).
  asreturn2 (seq seq1 n).
  asreturn2 (seq seq2 n).
  asreturn2 (seq seq1 m).
  asreturn2 (seq seq2 m).

  classical_auto.
  apply Preturn.

  assert (x + x0 - (x1 + x2) == (x - x1) + (x0 - x2)). {
    field.
  }
  rewrite H2.

  assert (epsilon == halfe + halfe). {
    unfold halfe.
    field.
  }
  rewrite H3; clear H3.
  eapply Qle_trans.
  apply Qabs_triangle.
  apply Qplus_le_compat; assumption.
Defined.

Lemma write_frac_as_Qmake : forall {z : Z},
    Z.lt 0 z ->
    1 / (inject_Z z) = Qmake 1 (Z.to_pos z).
Proof.
  intros.
  destruct z.
  - simpl.
    inversion H.
  - simpl.
    Search (inject_Z (Z.pos _)).
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
  - Search Qplus Qlt.
     apply (Qplus_lt_l _ _ (- (Qabs x))).
     field_simplify.
     repeat constructor.
Qed.

Lemma Qabs2Plus1 : forall x y, 0 < (Qabs x) + (Qabs y) + 1.
Proof.
  intros.
  apply (Qle_lt_trans _ (Qabs x)).
  - apply Qabs_nonneg.
  - Search Qplus Qlt.
     apply (Qplus_lt_l _ _ (- (Qabs x))).
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

Lemma Q_le_sqrt : forall q : Q, q > 0 -> [exists r, r * r <= q].
Proof.

  intros.
  apply (Pbind (Plem (Qle q 1))); intros qle1.
  destruct qle1.
  - apply Preturn.
    exists q.
    apply (Qle_trans _ (1 * q)).
    + apply Qlt_le_weak in H.
      apply Qmult_le_compat_r; assumption.
    + field_simplify.
      apply Qle_refl.
  - apply Preturn.
    exists 1.
    field_simplify.
    apply Qnot_le_lt in H0.
    apply Qlt_le_weak.
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
  Search Qabs Qeq.
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
    Search Qmult Qle.
    apply Qmult_le_compat_r; assumption.
  - Search Qmult Qle.
    Check Qmult_comm.
    apply (Qle_trans _ (b * c)).
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
  Search Qplus Qle.
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
  Search Qplus Qle.
  Search Qminus Qle.
  Search Qopp Qle.
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

Theorem Ceq_sym : forall x y, Ceq x y -> Ceq y x.
Proof.
  intros.
  unfold Ceq in *.
  intros.
  specialize (H epsilon H0).
  classical_auto.
  specialize H as [N H].
  apply Preturn.
  exists N.
  intros.
  specialize (H n H1).
  asreturn2 (seq x n).
  asreturn2 (seq y n).
  classical_auto.
  apply Preturn.
  Search Qle Qeq.
  Check Qabs_wd.
  Search Qabs Qminus.
  rewrite Qabs_Qminus.
  assumption.
Qed.

Theorem not_Cle_property_strong : forall x y,
    ~ (Cle x y) ->
    [exists epsilon, epsilon > 0 /\ exists N : nat, forall n, le N n -> toProp (
     Cbind (seq x n) (fun xn =>
     Cbind (seq y n) (fun yn =>
     Creturn (yn + epsilon <= xn))))]. (* I think this could be < *)
Proof.
  intros.
  unfold Cle in H.
  apply not_forall_2 in H.
  pbind H.
  specialize H as [epsilon [epspos H]].
  assert (H' := not_exists _ _ H).
  clear H.
  rename H' into H.
  simpl in H.

  assert (epsilon / 3 > 0) as hepspos. {
    apply (Qmult_lt_r _ _ 3). {
      repeat constructor.
    }
    field_simplify.
    assumption.
  }
  
  assert (propx :=property x (epsilon / 3) hepspos).
  pbind propx.
  assert (propy := property y (epsilon / 3) hepspos).
  pbind propy.
  destruct propx as [N1 propx].
  destruct propy as [N2 propy].
  specialize (H (max N1 N2)).

  apply not_forall_2 in H.
  pbind H.
  specialize H as [N3 [N3le seqN3]].

  apply Preturn.
  exists (epsilon / 3).
  split; auto.
  exists (max N1 N2).
  intros.

  specialize (propx N3 n (Nat.max_lub_l _ _ _ N3le) (Nat.max_lub_l _ _ _ H)).
  specialize (propy N3 n (Nat.max_lub_r _ _ _ N3le) (Nat.max_lub_r _ _ _ H)).

  asreturn2 (seq x n).
  asreturn2 (seq y n).
  asreturn2 (seq y N3).
  asreturn2 (seq x N3).
  classical_auto.
  apply Preturn.

  apply Qnot_le_lt in seqN3.
  apply Qabs_Qle_condition in propy as [propy _].
  apply Qabs_Qle_condition in propx as [_ propx].


  apply (Qplus_le_l _ _ (x1 + (epsilon / 3))) in propy.
  repeat field_simplify in propy.

  apply (Qplus_le_l _ _ (-epsilon / 3)).
  repeat field_simplify.
  apply (Qle_trans _ _ _ propy).

  apply Qlt_le_weak in seqN3.
  apply (Qplus_le_l _ _ (x2 - epsilon )) in seqN3.
  field_simplify in seqN3.
  apply (Qplus_le_l _ _ (- epsilon / 3)).
  repeat field_simplify.

  apply (Qle_trans _ _ _ seqN3).

  apply (Qplus_le_l _ _ epsilon).
  field_simplify.

  apply (Qplus_le_l _ _ x0) in propx.
  repeat field_simplify in propx.
  apply (Qle_trans _ _ _ propx).
  field_simplify.
  apply Qle_refl.
Qed.

(* TODO: prove this in terms of the strong version above instead of just repeating the proof *)
Theorem not_Cle_property : forall x y,
    ~ (Cle x y) ->
    [exists N : nat, forall n, le N n -> toProp (
     Cbind (seq x n) (fun xn =>
     Cbind (seq y n) (fun yn =>
     Creturn (yn <= xn))))]. (* I think this could be < *)
Proof.
  intros.
  unfold Cle in H.
  apply not_forall_2 in H.
  pbind H.
  specialize H as [epsilon [epspos H]].
  assert (H' := not_exists _ _ H).
  clear H.
  rename H' into H.
  simpl in H.

  assert (epsilon / 2 > 0) as hepspos. {
    apply (Qmult_lt_r _ _ 2). {
      repeat constructor.
    }
    field_simplify.
    assumption.
  }
  
  assert (propx :=property x (epsilon / 2) hepspos).
  pbind propx.
  assert (propy := property y (epsilon / 2) hepspos).
  pbind propy.
  destruct propx as [N1 propx].
  destruct propy as [N2 propy].
  specialize (H (max N1 N2)).

  apply not_forall_2 in H.
  pbind H.
  specialize H as [N3 [N3le seqN3]].

  apply Preturn.
  exists (max N1 N2).
  intros.



  specialize (propx N3 n (Nat.max_lub_l _ _ _ N3le) (Nat.max_lub_l _ _ _ H)).
  specialize (propy N3 n (Nat.max_lub_r _ _ _ N3le) (Nat.max_lub_r _ _ _ H)).

  asreturn2 (seq x n).
  asreturn2 (seq y n).
  asreturn2 (seq y N3).
  asreturn2 (seq x N3).
  classical_auto.
  apply Preturn.

  Search Qle Qabs.
  apply Qabs_Qle_condition in propy as [propy _].
  apply Qabs_Qle_condition in propx as [_ propx].

  Search Qle not.
  apply Qnot_le_lt in seqN3.
  apply (Qplus_le_l _ _ (x1 + (epsilon / 2))) in propy.
  repeat field_simplify in propy.

  apply (Qle_trans _ _ _ propy).

  apply Qlt_le_weak in seqN3.
  apply (Qplus_le_l _ _ (x2 - epsilon )) in seqN3.
  field_simplify in seqN3.
  apply (Qplus_le_l _ _ (- epsilon / 2)).
  repeat field_simplify.

  apply (Qle_trans _ _ _ seqN3).

  apply (Qplus_le_l _ _ epsilon).
  field_simplify.

  apply (Qplus_le_l _ _ x0) in propx.
  repeat field_simplify in propx.
  apply (Qle_trans _ _ _ propx).
  field_simplify.
  apply Qle_refl.
Qed.

Theorem not_Cle : forall x y, ~Cle x y -> Cle y x.
Proof.
  intros.
  unfold Cle.
  intros.
  assert (fact := not_Cle_property x y H).
  classical_auto.
  specialize fact as [N fact].
  apply Preturn.
  exists N.
  intros.
  specialize (fact n H1).
  asreturn2 (seq x n).
  asreturn2 (seq y n).
  classical_auto.
  apply Preturn.
  Search Qle Qplus 0%Q.
  Search Qle Qplus.
  apply (Qplus_le_l _ _ (-x0)) in fact.
  field_simplify (x0 - x0) in fact.
  apply Qlt_le_weak in H0.
  apply (Qle_trans _ 0); auto.
Qed.

Definition Cmult (seq1 seq2 : cauchy) : cauchy.
  refine {| seq := (fun n => Cbind (seq seq1 n) (fun x =>
                            Cbind (seq seq2 n) (fun y =>
                            Creturn (Qmult x y))))|}.
  intros.

  assert (Qlt 0 1) as fact by repeat constructor.
  assert (bound1 := property seq1 1 fact).
  assert (bound2 := property seq2 1 fact).
  classical_auto.
  specialize bound1 as [boundN1 bound1fact].
  specialize bound2 as [boundN2 bound2fact].
  specialize (bound1fact boundN1).
  specialize (bound2fact boundN2).
  asreturn2 (seq seq1 boundN1).
  asreturn2 (seq seq2 boundN2).
  rename x0 into y. (* These bounds are within 1 of the value of seq1 and seq2*)
  pose (bound1 := (Qabs x) + 1).
  pose (bound2 := (Qabs y) + 1).

  assert (forall m, le boundN1 m ->
                    toProp (Cbind (seq seq1 m) (fun y => Creturn (Qabs y <= bound1))))
    as bound1fact'. {
    intros.
    specialize (bound1fact m (Nat.le_refl _) H0).
    asreturn2 (seq seq1 m).
    classical_auto.
    apply Preturn.
    unfold bound1.
    apply (Qplus_le_l _ _ (- (Qabs x))).
    field_simplify.
    apply (Qle_trans _ _ _ (Qeq_le (Qabs_opp _))) in bound1fact.
    apply (Qle_trans _ (Qabs (x0 - x))).
    - apply (Qabs_triangle_reverse x0 x).
    - eapply (Qle_trans _ _ _ _ bound1fact).
      Unshelve.
      apply Qeq_le.
      apply Qabs_wd.
      field.
  }
  clear bound1fact.

  assert (forall m, le boundN2 m ->
                    toProp (Cbind (seq seq2 m) (fun y => Creturn (Qabs y <= bound2))))
    as bound2fact'. {
    intros.
    specialize (bound2fact m (Nat.le_refl _) H0).
    asreturn2 (seq seq2 m).
    classical_auto.
    apply Preturn.
    unfold bound2.
    apply (Qplus_le_l _ _ (- (Qabs y))).
    field_simplify.
    apply (Qle_trans _ _ _ (Qeq_le (Qabs_opp _))) in bound2fact.
    apply (Qle_trans _ (Qabs (x0 - y))).
    - apply (Qabs_triangle_reverse x0 y).
    - eapply (Qle_trans _ _ _ _ bound2fact).
      Unshelve.
      apply Qeq_le.
      apply Qabs_wd.
      field.
  }
  clear bound2fact.
  
  pose (epsilon' :=  epsilon / (2 * bound1 * bound2)).
  assert (epsilon' > 0) as Hh. {
    apply Qmult_lt_0_compat.
    - assumption.
    - apply Qinv_lt_0_compat.
      repeat constructor.
      unfold bound1, bound2.
      apply Qmult_lt_0_compat.
      + apply Qmult_lt_0_compat.
        * repeat constructor.
        * apply QabsPlus1.
      + apply QabsPlus1.
  }

  assert (property1 := property seq1 epsilon' Hh).
  assert (property2 := property seq2 epsilon' Hh).
  classical_auto.
  specialize property1 as [N1 p1].
  specialize property2 as [N2 p2].
  apply Preturn.
  exists (max (max boundN1 boundN2) (max N1 N2)).
  intros.
  
  specialize (p1 n m (Nat.max_lub_l _ _ _ (Nat.max_lub_r _ _ _ H0))
                 (Nat.max_lub_l _ _ _ (Nat.max_lub_r _ _ _ H1))).
  specialize (p2 n m (Nat.max_lub_r _ _ _ (Nat.max_lub_r _ _ _ H0))
                 (Nat.max_lub_r _ _ _ (Nat.max_lub_r _ _ _ H1))).
  assert (bound1fact_1 := bound1fact' n (Nat.max_lub_l _ _ _ (Nat.max_lub_l _ _ _ H0))).
  assert (bound1fact_2 := bound1fact' m (Nat.max_lub_l _ _ _ (Nat.max_lub_l _ _ _ H1))).
  assert (bound2fact_1 := bound2fact' n (Nat.max_lub_r _ _ _ (Nat.max_lub_l _ _ _ H0))).
  assert (bound2fact_2 := bound2fact' m (Nat.max_lub_r _ _ _ (Nat.max_lub_l _ _ _ H1))).
  asreturn2 (seq seq1 n).
  asreturn2 (seq seq2 n).
  asreturn2 (seq seq1 m).
  asreturn2 (seq seq2 m).

  classical_auto.
  apply Preturn.

  (* Now the rational number proof part *)
  
  assert (x0*x1 - x2*x3 == (x0*x1 - x0*x3) + (x0*x3 - x2*x3)) as triversion. {
    field.
  }
  apply (Qle_trans _ _ _ (Qeq_le (Qabs_wd _ _ triversion))).
  apply (Qle_trans _ _ _ (Qabs_triangle _ _)).
  assert ((Qabs (x0 * x1 - x0 * x3) + Qabs (x0 * x3 - x2 * x3) ==
             (Qabs x0) * (Qabs (x1 - x3)) + (Qabs (x0 - x2) * (Qabs x3)))). {
    apply (Qeq_trans _ (Qabs (x0 * (x1 - x3)) + Qabs ((x0 - x2) * x3))).
    - apply Qplus_compat; apply Qabs_wd_Proper; field.
    - apply (Qplus_compat (Qabs_Qmult x0 (x1 - x3)) (Qabs_Qmult (x0 - x2) x3)).
  }
  apply (Qle_trans _ _ _ (Qeq_le H2)).
  clear H2 triversion.

  apply (Qle_trans _ _ _ (Qplus_le_compat _ _ _ _
           (Qmult_compat (Qabs_nonneg _) (Qabs_nonneg _) bound1fact_1 p2)
           (Qmult_compat (Qabs_nonneg _) (Qabs_nonneg _) p1 bound2fact_2))).
  unfold epsilon'.

   assert (bound1 >= 1) as bound1gt. {
     unfold bound1.
     apply (Qplus_le_r _ _ ( -1)).
     field_simplify.
     apply Qabs_nonneg.
   }

   assert (bound2 >= 1) as bound2gt. {
     unfold bound2.
     apply (Qplus_le_r _ _ ( -1)).
     field_simplify.
     apply Qabs_nonneg.
  }
  
  assert (bound1 > 0) as bound1pos. {
     apply (Qlt_le_trans _ 1); auto.
   }

  assert (bound2 > 0) as bound2pos. {
     apply (Qlt_le_trans _ 1); auto.
  }
  assert (~ bound2 == 0). {
    intros p.
    apply Qeq_sym in p.
    apply Qlt_not_eq in bound2pos.
    contradiction.
  }
  assert (~ bound1 == 0). {
    intros p.
    apply Qeq_sym in p.
    apply Qlt_not_eq in bound1pos.
    contradiction.
   }

   assert ( bound1 * (epsilon / (2 * bound1 * bound2)) + epsilon / (2 * bound1 * bound2) * bound2
            ==  (epsilon / (2 * bound2)) + (epsilon / (2 * bound1))) as temp. {
     field; auto.
   }
   apply (Qle_trans _ _ _ (Qeq_le temp)).
   clear temp.

   apply (Qle_trans _ (epsilon / 2 + epsilon / 2)).
   2: {
     repeat field_simplify.
     apply Qle_refl.
   }
   
   apply Qplus_le_compat.
  - apply Qmult_compat.
    + apply Qlt_le_weak.
      assumption.
    + apply (Qmult_lt_0_le_reg_r _ _ 2); auto.
      field_simplify; auto.
      rewrite Qinv_def.
      apply Qinv_le_0_compat.
      apply Qlt_le_weak.
      auto.
    + apply Qle_refl.
    + field_simplify; auto.
      repeat rewrite Qinv_def.
      apply (Qmult_lt_0_le_reg_r _ _ 2); auto.
      field_simplify; auto.
      apply (Qmult_lt_0_le_reg_r _ _ bound2); auto.
      field_simplify; auto.
  - apply Qmult_compat.
    + apply Qlt_le_weak.
      assumption.
    + apply (Qmult_lt_0_le_reg_r _ _ 2); auto.
      field_simplify; auto.
      rewrite Qinv_def.
      apply Qinv_le_0_compat.
      apply Qlt_le_weak.
      auto.
    + apply Qle_refl.
    + field_simplify; auto.
      repeat rewrite Qinv_def.
      apply (Qmult_lt_0_le_reg_r _ _ 2); auto.
      field_simplify; auto.
      apply (Qmult_lt_0_le_reg_r _ _ bound1); auto.
      field_simplify; auto.
Defined.

Theorem exact_equality (x y : cauchy)
        (H : forall n, toProp (
                           Cbind (seq x n) (fun qx =>
                           Cbind (seq y n) (fun qy =>
                           Creturn (Qeq qx qy)))))
  : Ceq x y.
Proof.
  unfold Ceq.
  intros.
  
  apply Preturn.
  exists 0%nat.
  intros.
  specialize (H n).
  asreturn2 (seq x n).
  asreturn2 (seq y n).
  classical_auto.
  apply Preturn.
  (* Is this sort of garbage really the easiest way to prove basic rational number stuff in rocq? *)
  assert (x0 - x1 == 0). {
    apply (Qplus_inj_r _ _ x1).
    field_simplify.
    assumption.
  }
  apply Qabs_wd in H2.
  assert (Qabs 0 == 0). {
    reflexivity.
  }
  Check (Qeq_trans _ _ _ H2 H3).
  apply (Qle_trans _ 0).
  - Search Qeq Qle.
    apply Qle_lteq.
    apply or_intror.
    apply (Qeq_trans _ _ _ H2 H3).
  - apply Qlt_le_weak.
    assumption.
Qed.

Theorem Ceq_refl : forall x, Ceq x x.
Proof.
  intros.
  apply exact_equality.
  intros.
  asreturn2 (seq x n).
  classical_auto.
  apply Preturn.
  reflexivity.
Qed.
    
(* I need to set things up so that this can just trivially work out to Qplus_comm *)
Theorem Cplus_comm : forall x y, Ceq (Cplus x y) (Cplus y x).
Proof.
  intros.
  apply exact_equality.
  intros.

  simpl.

  asreturn2 (seq x n).
  asreturn2 (seq y n).

  classical_auto.
  apply Preturn.
  apply Qplus_comm.
Qed.

Theorem Cplus_assoc : forall x y z, Ceq (Cplus x (Cplus y z)) (Cplus (Cplus x y) z).
Proof.
  intros.
  apply exact_equality.
  intros.
  simpl.
  asreturn2 (seq x n).
  asreturn2 (seq y n).
  asreturn2 (seq z n).
  classical_auto.
  apply Preturn.
  apply Qplus_assoc.
Qed.

Theorem Cmult_comm : forall x y, Ceq (Cmult x y) (Cmult y x).
Proof.
  intros.
  apply exact_equality.
  intros.

  simpl.

  asreturn2 (seq x n).
  asreturn2 (seq y n).

  classical_auto.
  apply Preturn.
  apply Qmult_comm.
Qed.


Check Q_as_DT.eq_equiv.
Check Q_as_OT.lt_strorder.
Print StrictOrder.
Check StrictOrder_Transitive.
Check (StrictOrder_Transitive (Q_as_OT.lt_strorder)).

Print Irreflexive.
Print Reflexive.


Theorem Cle_trans : forall x y z, Cle x y -> Cle y z -> Cle x z.
Proof.
  intros x y z H1 H2.
  unfold Cle in *.
  intros.
  pose (halfe := Qdiv epsilon 2).
  assert (halfe > 0) as Hh. {
    apply Qmult_lt_0_compat.
    - assumption.
    - apply Qinv_lt_0_compat.
      repeat constructor.
  }
  specialize (H1 halfe Hh).
  specialize (H2 halfe Hh).
  classical_auto.
  specialize H1 as [N1 H1].
  specialize H2 as [N2 H2].
  apply Preturn.
  exists (max N1 N2).
  intros.
  specialize (H1 n (Nat.le_trans _ _ _ (Nat.le_max_l N1 N2) H0)).
  specialize (H2 n (Nat.le_trans _ _ _ (Nat.le_max_r N1 N2) H0)).

  asreturn2 (seq x n).
  asreturn2 (seq y n).
  asreturn2 (seq z n).
  classical_auto.
  apply Preturn.

  assert (combined := Qplus_le_compat _ _ _ _ H1 H2).
  unfold halfe in combined.
  repeat field_simplify in combined.
  assumption.
Qed.

Theorem Ceq_Cle : forall x y, Ceq x y -> Cle x y.
Proof.
  intros.
  unfold Cle, Ceq in *.
  intros.
  specialize (H epsilon H0).
  classical_auto.
  specialize H as [N H].
  apply Preturn.
  exists N.
  intros.
  specialize (H n H1).
  asreturn2 (seq x n).
  asreturn2 (seq y n).
  classical_auto.
  apply Preturn.
  apply Qabs_Qle_condition in H as [_ H].
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

Theorem total_ordering : forall x y, [Cle x y \/ Cle y x].
Proof.
  intros.
  apply (Pbind (Plem (Cle x y))).
  intros.
  apply Preturn.
  destruct H.
  - auto.
  - apply not_Cle in H.
    auto.
Qed.

Theorem Cle_antisymmetry : forall x y, Cle x y -> Cle y x -> Ceq x y.
Proof.
  intros x y H1 H2.
  unfold Cle, Ceq in *.
  intros.
  specialize (H1 epsilon H).
  specialize (H2 epsilon H).
  classical_auto.
  specialize H1 as [N1 H1].
  specialize H2 as  [N2 H2].
  apply Preturn.
  exists (max N1 N2).
  intros.
  specialize (H1 n (Nat.max_lub_l _ _ _ H0)).
  specialize (H2 n (Nat.max_lub_r _ _ _ H0)).
  asreturn2 (seq x n).
  asreturn2 (seq y n).
  classical_auto.
  apply Preturn.
  apply Qabs_Qle_condition.
  split.
  - apply Qopp_le_compat2.
    apply (Qle_trans _ (x1 - x0)). {
      apply Qeq_le. field.
    }
    field_simplify.
    assumption.
  - assumption.
Qed.

Theorem Ceq_trans : forall x y z, Ceq x y -> Ceq y z -> Ceq x z.
Proof.
  intros.
  assert (Ceq y x) by (apply Ceq_sym; auto). 
  assert (Ceq z y) by (apply Ceq_sym; auto).
  apply Ceq_Cle in H, H0, H1, H2.
  apply Cle_antisymmetry;
  apply (Cle_trans _ y);
  auto.
Qed.

(*
Given a bounded set S, I need to construct a pair of sequences that converge to the lub from
the top and bottom.
*)

(* Output is (top, bottom) *)
Fixpoint converging (startTop startBot: Q) (decide : Q -> Prop) (index :  nat)
  : Classical (Q * Q).
  refine (
      match index with
      | O => Creturn (startTop , startBot)
      | S index' =>
          Cbind (converging startTop startBot decide index') (fun bt =>
          let t := fst bt in
          let b := snd bt in
          let half := (b + t) / 2 in
          Pif (decide half) (t , half) (half , b)
          )
      end
    ).
Defined.

Theorem separate startTop startBot decide (n : nat)
        (H : startBot < startTop)
  :
  toProp (Cbind (converging startTop startBot decide n) (fun tb =>
          let t := fst tb in
          let b := snd tb in
          Creturn (b < t))).
Proof.
  induction n.
  -
    simpl in *.
    classical_auto.
    apply Preturn.
    simpl.
    assumption.
  - simpl in *.
    asreturn2 (converging startTop startBot decide n).
    destruct x as [t b].
    classical_auto.
    simpl in *.
    apply (Pbind (Plem (decide ((b + t) / 2)))).
    intros PornotP.
    destruct PornotP.
    + rewrite PifDef1; try assumption.
      classical_auto.
      apply Preturn.
      simpl.
      apply (Qmult_lt_r ((b + t) / 2) t 2). {
        repeat constructor.
      }
      field_simplify.
      eapply Qlt_le_trans.
      apply Qplus_lt_le_compat.
      * apply IHn.
      * apply Qle_refl.
      * field_simplify.
        apply Qle_refl.
    + rewrite PifDef2; try assumption.
      classical_auto.
      apply Preturn.
      simpl.
      apply (Qmult_lt_r b ((b + t) / 2) 2). {
        repeat constructor.
      }
      field_simplify.
      Check Qlt_le_trans.
      apply (Qle_lt_trans _ (b + b)).
      * field_simplify.
        apply Qle_refl.
      * apply Qplus_lt_r.
        assumption.
Qed.

Theorem monotonic startTop startBot decide (n m : nat) (H : le n m)
        (H2 : startBot < startTop)
  :
  toProp (Cbind (converging startTop startBot decide n) (fun tbn =>
          Cbind (converging startTop startBot decide m) (fun tbm =>
          let tn := fst tbn in
          let bn := snd tbn in
          let tm := fst tbm in
          let bm := snd tbm in
          Creturn (tn >= tm /\ bn <= bm)))).
Proof.
  simpl.
  (* First, we need to show that this is equivalent to n and (n + k) for some k*)
  destruct (Nat.le_exists_sub n m H) as [p [H' _]].
  subst m.
  clear H.

  induction p.
  - simpl in *.
    asreturn2 (converging startTop startBot decide n).
    destruct x as [b t].
    classical_auto.
    apply Preturn.
    split; apply Qle_refl.
  - asreturn2 (converging startTop startBot decide n).
    destruct x as [tn bn].
    simpl in *.
    assert (separation := separate startTop startBot decide (p + n)).
    asreturn2 (converging startTop startBot decide (p + n)).
    destruct x as [tpn bpn].
    classical_auto.
    simpl in *.
    destruct IHp as [le1 le2].

    classical_auto.
    specialize (separation H2).
    clear H2.
    
    apply (Pbind (Plem (decide ((bpn + tpn) / 2)))); intros PornotP.
    destruct PornotP.
    + rewrite (PifDef1 _ _ _ H).
      classical_auto.
      simpl.
      apply Preturn.
      split; auto.
      apply (Qle_trans _ ((bpn + bpn) / 2)).
      * field_simplify.
        field_simplify.
        assumption.
      * 
        Check Qmult_le_r.
        apply (Qmult_le_r _ _ 2). {
          repeat constructor.
        }
        field_simplify.
        apply Qlt_le_weak.
        apply (Qle_lt_trans _ (bpn + bpn) _).
        -- field_simplify.
           apply Qle_refl.
        -- apply (Qplus_lt_r _ _ (- bpn)).
           field_simplify.
           assumption.
    + rewrite (PifDef2 _ _ _ H).
      classical_auto.
      simpl.
      apply Preturn.
      split; auto.
      apply (Qle_trans _ ((tpn + tpn) / 2)).
      * apply (Qmult_le_r _ _ 2). { repeat constructor. }
        field_simplify.
        apply Qlt_le_weak.
        Check Qplus_le_r.
        apply (Qplus_lt_r _ _ (- tpn)).
        field_simplify.
        assumption.
      * field_simplify.
        field_simplify.
        apply (Qle_trans _ tpn).
        -- apply Qle_refl.
        -- assumption.
Qed.

Theorem bound_size_converging_intervals :
  forall startTop startBot decide n,
    toProp (
        Cbind (converging startTop startBot decide n) (fun tb =>
        let t := fst tb in
        let b := snd tb in
        Creturn ((t - b) == (startTop - startBot) / (inject_Z (Z.pow 2 (Z.of_nat n)))))).
Proof.
  intros.
  induction n.
  - simpl.
    classical_auto.
    apply Preturn.
    simpl.
    field.
  - classical_auto.
    simpl in *.
    asreturn2 (converging startTop startBot decide n).
    classical_auto.
    apply (Pbind (Plem (decide ((snd x + fst x) / 2)))); intros yesorno.

    pose (Q1 := inject_Z (2 ^ Z.of_nat n)).
    assert (~ Q1 == 0) as nonneg1. {
      unfold Q1.
      (* TODO: use lemma here *)
      apply pow_nonzero.
    }
    pose (Q2 := inject_Z (Z.pow_pos 2 (Pos.of_succ_nat n))).
    assert (Q2 == 2 * Q1) as double. {
      unfold Q2.
      rewrite Z.pow_pos_fold.
      rewrite Znat.Zpos_P_of_succ_nat.
      rewrite (Z.pow_succ_r).
      2: {
        apply Zorder.Zle_0_nat.
      }
      rewrite inject_Z_mult.
      unfold Q1.
      field_simplify.
      apply Qeq_refl.
    }
    assert (~  Q2 == 0) as nonneg. {
      intros p.
      apply Qeq_sym in double.
      apply (Qeq_trans _ _ _ double) in p.
      Search Qmult Qeq.
      Check Qmult_inj_r.
      apply (Qmult_inj_l _ _ (/2)) in p; try easy.
      field_simplify in p.
      apply (Qeq_trans _ _ 0) in p; try field.
      contradiction.
    }

    (* A lemma that we will need in both cases *)
    assert ((fst x - snd x == (startTop - startBot) / inject_Z (2 ^ Z.of_nat n))
            -> (fst x + -1 * snd x) / 2 ==
                 (startTop + -1 * startBot) / inject_Z (Z.pow_pos 2 (Pos.of_succ_nat n))) as sdfsdf. {
      intros.
      apply (Qmult_inj_r _ _ 2). {
        intros p.
        inversion p.
      }
      field_simplify; auto.
      apply (Qeq_trans _ _ _ IHn).
      fold Q1 Q2.
      apply (Qmult_inj_r _ _ Q1); auto.
      apply (Qmult_inj_r _ _ Q2); auto.
      field_simplify; auto.
      apply (Qeq_trans _ ((startTop - startBot) * Q2)); try field.
      apply (Qeq_trans _ (2 * (startTop - startBot) * Q1)); try field.

      (* by doing this stuff I can make the thing look like the thing *)
      Search Qmult Qeq (_ * _ == _ * _).
      Check Qmult_inj_l.
      Search Qmult Proper.
      apply (Qeq_trans _ _ _ (Qmult_comp _ _ (Qeq_refl _) _ _ double)).
      field.
    }
    
    destruct yesorno.
    + Check PifDef1.
      rewrite (PifDef1 _ _ _ H).
      classical_auto.
      simpl.
      apply Preturn.
      field_simplify; auto.
    + rewrite (PifDef2 _ _ _ H).
      classical_auto.
      simpl.
      apply Preturn.
      field_simplify; auto.
      apply (Qeq_trans _ ((fst x - snd x)/2)); try field.
      apply (sdfsdf IHn).
Qed.

Check bound_size_converging_intervals.

Lemma rational_den_comparison :
  forall q, q > 0 -> (Qmake 1 (Qden q)) <= q.
Proof.
  intros.
  destruct q.
  unfold Qle.
  simpl.
  apply (Z.le_trans _ (1 * (Z.pos Qden)));
    [(ring_simplify; apply Z.le_refl)|].
  apply Z.mul_le_mono_nonneg_r.
  - apply Z.lt_le_incl.
    apply Pos2Z.pos_is_pos.
  - unfold Qlt in H.
    simpl in H.
    ring_simplify in H.
    apply Z_lt_le_off_by_one.
    assumption.
Qed.

Lemma bound_rational_with_power :
  forall q : Q,
    q > 0 ->
    exists n,
      (1 / inject_Z (2 ^ Z.of_nat n)) <= q.
Proof.
  intros.
  pose (den := Qden q).
  (* we want n such that (1 / 2^n) <= (num / den),
   so let n = log2 q.
   2^(log2_up x) >= x, so
   Then, (1 / 2^(log2_up den)) <= (1 / den) *)
  exists (Z.to_nat (Z.log2_up (Zpos den))).
  rewrite Znat.Z2Nat.id.
  2: {
    apply Z.log2_up_nonneg.
  }
  assert (itsastart := Z.log2_log2_up_spec (Z.pos den)).
  specialize (itsastart (Pos2Z.pos_is_pos _)) as [_ itsastart].
 
  assert (Z.lt 0%Z (2 ^ Z.log2_up (Z.pos den))%Z). {
    apply Z.pow_pos_nonneg.
    - easy.
    - apply Z.log2_up_nonneg.
  }
  
  
  apply (Qle_trans _ (Qmake 1 (Qden q))).
  2: {
    apply rational_den_comparison.
    assumption.
  }
  
  rewrite (write_frac_as_Qmake); auto.
  unfold Qle.
  simpl.
  rewrite Z2Pos.id; auto.
Qed.

Theorem epsilon_bound_size_converging_intervals :
  forall epsilon startTop startBot decide,
    epsilon > 0 ->
    startTop > startBot ->
    exists n,
    toProp (
        Cbind (converging startTop startBot decide n) (fun tb =>
        let t := fst tb in
        let b := snd tb in
        Creturn ((t - b) <= epsilon))).
Proof.
  intros.
  assert (startTop - startBot > 0) as intpos. {
    apply (Qplus_lt_l _ _ (-startBot)) in H0.
    field_simplify (startBot - startBot) in H0.
    assumption.
  }
  assert (~ (startTop - startBot == 0)) as intnonzero. {
    apply Qlt_not_eq in intpos.
    intros p.
    apply Qeq_sym in p.
    contradiction.
  }
  specialize (bound_rational_with_power (epsilon / (startTop - startBot))) as [n intervalsize]. {
    apply (Qmult_lt_r _ _ (startTop - startBot)); auto.
    field_simplify; auto.
  }

  exists n.
  assert (lemma := bound_size_converging_intervals startTop startBot decide n).
  asreturn2 (converging startTop startBot decide n).
  classical_auto.
  apply Preturn.
  destruct x as [t b].
  simpl in *.
  apply (@QOrder.eq_le _ _ _ lemma).
  apply Qinv_lt_0_compat in intpos.
  apply (Qmult_le_l _ _ (/(startTop - startBot))); auto.
  field_simplify; auto.
  split; auto.
  apply pow_nonzero.
Qed.

(*
Overall, there are many standard library theorems about powers in Z, but not in Q.
So I need to prove things in terms of power in Z if I want to use the library theorems.
 *)

Definition converging_cauchy (startTop startBot: Q) (decide : Q -> Prop) (separateStart : startBot < startTop)
  : cauchy * cauchy.
  Check converging.

  refine (
      {| seq := fun n => Cbind (converging startTop startBot decide n) (fun tb =>
                         Creturn (fst tb))|}
      ,
      {| seq := fun n => Cbind (converging startTop startBot decide n) (fun tb =>
                         Creturn (snd tb))|}
    ).
  (* Below are the proofs that the upper and lower sequences are cauchy. They are very repetetive with each other. *)
  - intros.
    destruct (epsilon_bound_size_converging_intervals epsilon startTop startBot decide H separateStart) as [N small].

    apply Preturn.
    exists N.
    intros.

    assert (mono1 := monotonic startTop startBot decide N n H0 separateStart).
    assert (mono2 := monotonic startTop startBot decide N m H1 separateStart).
    simpl in mono1, mono2.
    assert (separate_n := separate startTop startBot decide n separateStart).
    assert (separate_m := separate startTop startBot decide m separateStart).

    asreturn2 (converging startTop startBot decide N).
    asreturn2 (converging startTop startBot decide n).
    asreturn2 (converging startTop startBot decide m).

    classical_auto.
    apply Preturn.

    destruct x as [t0 tb0].
    destruct x0 as [tn bn].
    destruct x1 as [tm bm].
    simpl fst in *.
    simpl snd in *.
    destruct mono2 as [tmt0 tb0bm].
    destruct mono1 as [tnt0 tb0bn].
    apply Qlt_le_weak in separate_m, separate_n.

    apply Qabs_Qle_condition.
    split.
    + apply Qopp_le_compat2.
      field_simplify.
      apply (@QOrder.eq_le _ (tm - tn)). {
        field.
      }
      apply (bound_lemma_1 tmt0).
      apply (bound_lemma_2 separate_n).
      apply (bound_lemma_2 tb0bn).
      assumption.
    + apply (bound_lemma_1 tnt0).
      apply (bound_lemma_2 separate_m).
      apply (bound_lemma_2 tb0bm).
      assumption.
  -  intros.
    destruct (epsilon_bound_size_converging_intervals epsilon startTop startBot decide H separateStart) as [N small].

    apply Preturn.
    exists N.
    intros.

    assert (mono1 := monotonic startTop startBot decide N n H0 separateStart).
    assert (mono2 := monotonic startTop startBot decide N m H1 separateStart).
    simpl in mono1, mono2.
    assert (separate_n := separate startTop startBot decide n separateStart).
    assert (separate_m := separate startTop startBot decide m separateStart).

    asreturn2 (converging startTop startBot decide N).
    asreturn2 (converging startTop startBot decide n).
    asreturn2 (converging startTop startBot decide m).

    classical_auto.
    apply Preturn.

    destruct x as [t0 tb0].
    destruct x0 as [tn bn].
    destruct x1 as [tm bm].
    simpl fst in *.
    simpl snd in *.
    destruct mono2 as [tmt0 tb0bm].
    destruct mono1 as [tnt0 tb0bn].
    apply Qlt_le_weak in separate_m, separate_n.

    apply Qabs_Qle_condition.
    split.
    + apply Qopp_le_compat2.
      field_simplify.
      apply (@QOrder.eq_le _ (bm - bn)). {
        field.
      }
      apply (bound_lemma_1 separate_m).
      apply (bound_lemma_1 tmt0).
      apply (bound_lemma_2 tb0bn).
      assumption.
    + apply (bound_lemma_1 separate_n).
      apply (bound_lemma_1 tnt0).
      apply (bound_lemma_2 tb0bm).
      assumption.
Defined.      
    
Theorem two_bounds_equal : forall startTop startBot decide
    (diff : startTop > startBot),
    let u := fst (converging_cauchy startTop startBot decide diff) in
    let b := snd (converging_cauchy startTop startBot decide diff) in
    Ceq u b.
Proof.
  intros.
  unfold Ceq.
  intros.
  apply Preturn.
  Check epsilon_bound_size_converging_intervals.
  destruct (epsilon_bound_size_converging_intervals epsilon startTop startBot decide H diff) as [N close].
  exists N.
  intros.
  assert (apart :=separate startTop startBot decide n diff).
  assert (mono := monotonic startTop startBot decide N n H0 diff).
  simpl seq.

  asreturn2 (converging startTop startBot decide n).
  asreturn2 (converging startTop startBot decide N).
  classical_auto.
  clear u b.
  apply Preturn.

  destruct x as [tn bn].
  destruct x0 as [tN bN].
  simpl fst in *.
  simpl snd in *.
  specialize mono as [tntN bNbn].

  apply Qlt_le_weak in apart.
  Search Qabs Qle.
  apply Qabs_diff_Qle_condition.
  split.
  - apply (Qplus_le_l _ _ (epsilon - bn)).
    field_simplify.
    apply (bound_lemma_1 tntN).
    apply (bound_lemma_2 bNbn).
    assumption.
  - apply (Qplus_le_l _ _ (-tn)).
    field_simplify.
    apply (bound_lemma_1 apart).
    field_simplify.
    apply Qlt_le_weak.
    assumption.
Qed.

(*
TODO:
- If decide is downward-closed, then all elements of upper sequence are not in decide and
  all elements of lower sequence are in decide
 *)

Theorem top_bottom_decide startTop startBot decide (n : nat)
        (H : startBot < startTop)
        (dtop : ~ decide startTop)
        (dbot : decide startBot)
  :
  toProp (Cbind (converging startTop startBot decide n) (fun tb =>
          let t := fst tb in
          let b := snd tb in
          Creturn (decide b /\ ~ decide t))).
Proof.
  Check separate.

  induction n.
  -
    simpl in *.
    classical_auto.
    apply Preturn.
    simpl.
    auto.
  - simpl in *.
    asreturn2 (converging startTop startBot decide n).
    destruct x as [t b].
    classical_auto.
    simpl in *.
    apply (Pbind (Plem (decide ((b + t) / 2)))).
    intros PornotP.
    destruct PornotP.
    + rewrite PifDef1; try assumption.
      classical_auto.
      apply Preturn.
      simpl.
      destruct IHn as [decb dect].
      auto.
    + rewrite PifDef2; try assumption.
      classical_auto.
      apply Preturn.
      simpl.
      destruct IHn.
      auto.
Qed.

Definition QinjR (q : Q) : cauchy.
  refine {| seq := fun _ => Creturn q|}.
  intros.
  apply Preturn.
  exists 0%nat.
  intros.
  classical_auto.
  apply Preturn.
  field_simplify (q - q).
  simpl.
  apply Qlt_le_weak.
  assumption.
Defined.

Theorem Qle_Cle: forall q1 q2, Qle q1 q2 -> Cle (QinjR q1) (QinjR q2).
Proof.
  intros.
  unfold Cle.
  intros.
  apply Preturn.
  exists 0%nat.
  intros.
  simpl.
  classical_auto.
  apply Preturn.
  apply (Qle_trans _ 0).
  + apply (Qplus_le_l _ _ q2).
    field_simplify.
    assumption.
  + apply Qlt_le_weak.
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
  - Search not Qlt.
    apply Qnot_lt_le in H1.
    apply Qabs_Qle_condition in H1.
    Search Qle Qeq.
    destruct H1.
    field_simplify in H1.
    Check QOrder.le_antisym.
    assert (reverse := @QOrder.le_antisym _ _ H1 H2).
    apply Qeq_sym in reverse.
    contradiction.
Qed.

Theorem Q_not_eq_lemma_2 : forall x y : Q, Qabs (x - y) > 0 -> ~ x == y.
Proof.
  intros.
  intros p.
  Search Qeq Qabs 0%Q.
  Search Qeq Qplus.
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

Theorem Ceq_Qeq : forall q1 q2, Ceq (QinjR q1) (QinjR q2) -> [q1 == q2].
Proof.
  intros.
  (* Proof by contradiction *)
  apply (Pbind (Plem (q1 == q2))); intros.
  destruct H0.
  - apply Preturn.
    assumption.
  - 
    unfold Ceq in H.
    simpl seq in H.
    assert (gt0 := Q_not_eq_lemma _ _ H0).
    classical_auto.
    assert ((Qabs (q1 - q2)) / 2 > 0) as pos. {
      apply (Qmult_lt_r _ _ 2). {
        repeat constructor.
      }
      field_simplify.
      assumption.
    }
    assert (~ (Qabs (q1 - q2) == 0)) as nonzero. {
      apply Qnot_eq_sym.
      apply Qlt_not_eq.
      assumption.
    }
    specialize (H ((Qabs (q1 - q2)) / 2) pos).
    classical_auto.
    specialize H as [N H].
    specialize (H N (Nat.le_refl _)).
    classical_auto.
    exfalso.
    apply (Qmult_le_r _ _ (/ (Qabs (q1 - q2)))) in H.
    2: {
      apply Qinv_lt_0_compat.
      assumption.
    }
    field_simplify in H; auto.
Qed.
      


Theorem Cle_Qle : forall q1 q2, Cle (QinjR q1) (QinjR q2) -> [Qle q1 q2].
Proof.
  intros.
  apply (Pbind (Plem (q1 <= q2))); intros.
  destruct H0.
  - apply Preturn.
    assumption.
  - assert (~ (Ceq (QinjR q1) (QinjR q2))). {
      intros eq.
      apply Ceq_Qeq in eq.
      apply classical_consistent.
      classical_auto.
      apply Qeq_le in eq.
      contradiction.
    }
    apply Qnot_le_lt in H0.
    apply Qlt_le_weak in H0.
    apply Qle_Cle in H0.
    assert (fact := Cle_antisymmetry _ _ H H0).
    contradiction.
Qed.

(* Given a set of real numbers, makes a predicate saying that
 a given rational is <= something in that set. *)
Definition make_decider (S : cauchy -> Prop) (q : Q) : Prop :=
  exists r, S r /\ Cle (QinjR q) r.

Theorem is_upper_bound :
  forall (S : cauchy -> Prop) startTop startBot
         (diff : startTop > startBot)
    (sbin : S (QinjR startBot))
    (sbnotin : forall r, S r -> ~ Cle (QinjR startTop) r),
    let u := fst (converging_cauchy startTop startBot (make_decider S) diff) in
    forall r (rInS : S r),
      Cle r u.
Proof.
  intros.
  unfold Cle.
  intros.
  simpl.

  assert ((make_decider S) startBot) as decidebot. {
    unfold make_decider.
    exists (QinjR startBot).
    intros.
    split.
    - assumption.
    - apply Ceq_Cle.
      apply Ceq_refl.
  }
  assert (~ (make_decider S) startTop) as decidetop. {
    unfold make_decider.
    intros [r' [Sr' ler']].
    specialize (sbnotin r' Sr').
    contradiction.
  }

  pose (thirde := Qdiv epsilon 3).
  assert (thirde > 0) as Ht. {
    apply Qmult_lt_0_compat.
    - assumption.
    - apply Qinv_lt_0_compat.
      repeat constructor.
  }

  assert (propertyr := property r thirde Ht).
  assert (propertyseq := property (fst (converging_cauchy startTop startBot (make_decider S) diff))
                                  thirde Ht).
  (*destruct (epsilon_bound_size_converging_intervals epsilon startTop startBot
                                                    (make_decider S) H diff) as [N2 lemma].*)
  classical_auto.
  specialize propertyr as [N1 propertyr].
  specialize propertyseq as [N2 propertyseq].

  assert (ltprop := top_bottom_decide startTop startBot
                                      (make_decider S) (max N1 N2) diff decidetop decidebot).
  (* at this point in the proof, I should be able to know that ui <= r.
     That is what ltprop is supposed to be, but it doesn't seem to work right? *)

  specialize (propertyseq (max N1 N2)).
  (* the issue is that this isn't in same form.  propertyseq has fst converging_cauchy,
   while ltprop has converging, with the fst later. These are really the same thing! *)
  
  simpl in propertyseq. (* this causes the problem of unfolding Qabs. I have to re-fold it later *)
  
  asreturn2 (converging startTop startBot (make_decider S) (max N1 N2)).
  classical_auto.
  unfold make_decider in ltprop.
  specialize ltprop as [_ ltprop].
  assert (forall r, S r -> Cle r (QinjR (fst x))) as temp. {
    intros.
    assert (temp := not_exists _ _ ltprop); clear ltprop; rename temp into ltprop; simpl in ltprop.
    specialize (ltprop r0).
    assert (~ (Cle (QinjR (fst x)) r0)) as temp. {
      intros f.
      apply ltprop.
      auto.
    }
    apply not_Cle.
    assumption.
  }
  clear ltprop; rename temp into ltprop.
  unfold Cle in ltprop.
  specialize (ltprop r rInS thirde Ht).
  classical_auto.
  specialize ltprop as [N3 ltprop].

  apply Preturn.
  exists (max (max N1 N2) N3).
  intros.
  specialize (ltprop (max (max N1 N2) N3) (Nat.max_lub_r _ _ _ (Nat.le_refl _))).
  specialize (propertyseq n (Nat.max_lub_r _ _ _ (Nat.le_refl _))
             (Nat.max_lub_r _ _ _ (Nat.max_lub_l _ _ _ H0))).
  specialize (propertyr (max (max N1 N2) N3) n
                        (Nat.max_lub_l _ _ _ (Nat.max_lub_l _ _ _ (Nat.le_refl _)))
                        (Nat.max_lub_l _ _ _ (Nat.max_lub_l _ _ _ H0))).
  asreturn2 (converging startTop startBot (make_decider S) n).
  asreturn2 (seq r (max (max N1 N2) N3)).
  asreturn2 (seq r n).
  simpl in ltprop.

  destruct x as [uN1N2 bN1N2].
  destruct x0 as [un bn].
  clear u.
  simpl fst in *.
  classical_auto.
  simpl fst in *.

  (* This is to fold Qabs in propertyseq; for some reason the fold tactic doesn't work *)
  assert (Qabs (uN1N2 - un) =
            Z.abs (Qnum uN1N2 * QDen un + - Qnum un * QDen uN1N2) # Qden uN1N2 * Qden un) as temp. {
    simpl.
    reflexivity.
  }
  rewrite <- temp in propertyseq.
  clear temp.

  apply Preturn.

  apply Qabs_diff_Qle_condition in propertyr as [_ propertyr].
  apply Qabs_diff_Qle_condition in propertyseq as [propertyseq _].
  apply (bound_lemma_1 propertyr).
  apply (bound_lemma_2 propertyseq).
  unfold thirde.
  field_simplify.
  apply (Qplus_le_l _ _ (- 2 * epsilon / 3)).
  repeat field_simplify.
  apply (Qle_trans _ (x1 - uN1N2)). {
    apply Qeq_le.
    field.
  }
  unfold thirde in ltprop.
  assumption.
Qed.

Theorem less_than_other_upper_bounds :
  forall (S : cauchy -> Prop) startTop startBot
         (diff : startTop > startBot)
    (sbin : S (QinjR startBot))
    (sbnotin : forall r, S r -> ~ Cle (QinjR startTop) r)
    (otherbound : cauchy)
    (otherboundprop : forall r, S r -> Cle r otherbound),
    let l := snd (converging_cauchy startTop startBot (make_decider S) diff) in
    Cle l otherbound.
Proof.
  intros.
  unfold Cle.
  intros.
  simpl.
  
  assert ((make_decider S) startBot) as decidebot. {
    unfold make_decider.
    exists (QinjR startBot).
    intros.
    split.
    - assumption.
    - apply Ceq_Cle.
      apply Ceq_refl.
  }
  assert (~ (make_decider S) startTop) as decidetop. {
    unfold make_decider.
    intros [r' [Sr' ler']].
    specialize (sbnotin r' Sr').
    contradiction.
  }
  clear sbin sbnotin.
  
  pose (thirde := Qdiv epsilon 3).
  assert (thirde > 0) as Ht. {
    apply Qmult_lt_0_compat.
    - assumption.
    - apply Qinv_lt_0_compat.
      repeat constructor.
  }

  assert (propertyb := property otherbound thirde Ht).
  assert (propertyseq := property (snd (converging_cauchy startTop startBot (make_decider S) diff))
                                  thirde Ht).
  (*destruct (epsilon_bound_size_converging_intervals epsilon startTop startBot
                                                    (make_decider S) H diff) as [N2 lemma].*)
  classical_auto.
  specialize propertyb as [N1 propertyb].
  specialize propertyseq as [N2 propertyseq].

  assert (ltprop := top_bottom_decide startTop startBot
                                      (make_decider S) (max N1 N2) diff decidetop decidebot).
  (* at this point in the proof, I should be able to know that ui <= r.
     That is what ltprop is supposed to be, but it doesn't seem to work right? *)

  specialize (propertyseq (max N1 N2)).
  (* the issue is that this isn't in same form.  propertyseq has fst converging_cauchy,
   while ltprop has converging, with the fst later. These are really the same thing! *)
  
  simpl in propertyseq. (* this causes the problem of unfolding Qabs. I have to re-fold it later *)
  
  asreturn2 (converging startTop startBot (make_decider S) (max N1 N2)).
  classical_auto.
  unfold make_decider in ltprop.
  specialize ltprop as [ltprop _].
  assert (exists r, S r /\ Cle (QinjR (snd x)) r) as temp. {
    intros.
    destruct ltprop as [r [Sr lexr]].
    exists r.
    auto.
  }
  clear ltprop; rename temp into ltprop.
  specialize ltprop as [r [Sr ltprop]].

  specialize (otherboundprop r Sr).
  classical_auto.
  apply (Cle_trans _ _ _ ltprop) in otherboundprop.
  clear ltprop.
  rename otherboundprop into ltprop.

  (***********************)
  
  unfold Cle in ltprop.
  specialize (ltprop thirde Ht).
  classical_auto.
  specialize ltprop as [N3 ltprop].

  apply Preturn.
  exists (max (max N1 N2) N3).
  intros.
  specialize (ltprop (max (max N1 N2) N3) (Nat.max_lub_r _ _ _ (Nat.le_refl _))).
  specialize (propertyseq n (Nat.max_lub_r _ _ _ (Nat.le_refl _))
             (Nat.max_lub_r _ _ _ (Nat.max_lub_l _ _ _ H0))).
  specialize (propertyb (max (max N1 N2) N3) n
                        (Nat.max_lub_l _ _ _ (Nat.max_lub_l _ _ _ (Nat.le_refl _)))
                        (Nat.max_lub_l _ _ _ (Nat.max_lub_l _ _ _ H0))).
  asreturn2 (converging startTop startBot (make_decider S) n).
  asreturn2 (seq otherbound (max (max N1 N2) N3)).
  asreturn2 (seq otherbound n).
  simpl in ltprop.

  destruct x as [uN1N2 bN1N2].
  destruct x0 as [un bn].
  clear l.
  simpl snd in *.
  classical_auto.
  simpl snd in *.
  
  (* This is to fold Qabs in propertyseq; for some reason the fold tactic doesn't work *)
  assert (Qabs (bN1N2 - bn) =
            Z.abs (Qnum bN1N2 * QDen bn + - Qnum bn * QDen bN1N2) # Qden bN1N2 * Qden bn ) as temp. {
    simpl.
    reflexivity.
  }
  rewrite <- temp in propertyseq.
  clear temp.

  apply Preturn.

  apply Qabs_diff_Qle_condition in propertyb as [propertyr _].
  apply Qabs_diff_Qle_condition in propertyseq as [_ propertyseq].
  apply (bound_lemma_1 propertyseq).
  apply (bound_lemma_2 propertyr).
  unfold thirde.
  field_simplify.
  apply (Qplus_le_l _ _ (- 2 * epsilon / 3)).
  repeat field_simplify.
  apply (Qle_trans _ (bN1N2 - x1)). {
    apply Qeq_le.
    field.
  }
  unfold thirde in ltprop.
  assumption.
Qed.

(*Definition real_rational_bounds :
  cauchy -> CQ * CQ.*)

Theorem rational_bounded_by_int :
  forall (q : Q), exists z : Z, inject_Z z >= q.
Proof.
  intros.
  destruct q.
  exists (Z.abs Qnum).
  unfold inject_Z.
  unfold Qle.
  simpl.
  destruct (Z.nonpos_nonneg_cases Qnum).
  - rewrite (Z.abs_neq Qnum H).
    ring_simplify.
    apply (Z.le_trans _ 0).
    + assumption.
    + apply Z.mul_nonneg_nonneg.
      * apply Z.opp_nonneg_nonpos.
        assumption.
      * apply Pos2Z.pos_is_nonneg.
  - rewrite (Z.abs_eq Qnum H).
    apply Z.mul_le_mono_nonneg_l.
    + assumption.
    + assert (this := Pos2Z.pos_is_pos Qden).
      apply Z_lt_le_off_by_one.
      assumption.
Qed.

Definition real_int_bound (r : cauchy) : [[| Z |]].
  refine (exist _ (fun z => Cle r (QinjR (inject_Z z)) /\
                              forall z', (Cle r (QinjR (inject_Z z))) -> Z.le z z') _).
  split.
  (* existence *)
  - Check (property r).
    assert (0 < 1) as lt01 by repeat constructor.
    assert (prop := property r 1 lt01).
    classical_auto.
    specialize prop as [N prop].
    apply Preturn.
    (*Check (Cbind (seq r N) (fun rN => Creturn (rational_bounded_by_int rN))).*)
  (* uniqueness *)
Abort.


(* TODO: I can use this to simplify the definition of Cmult,
 instead in that definition I build in bound1 and bound2 *)
Theorem real_bounded_above_rational :
  forall r, [exists q, Cle r (QinjR q)].
Proof.
  intros.
  assert (0 < 1) as indeed. {
    repeat constructor.
  }
  assert (prop := property r 1 indeed).
  classical_auto.
  specialize prop as [N prop].
  assert (fact := proj2_sig (seq r N)).
  specialize fact as [rNexists rnUnique].
  classical_auto.
  specialize rNexists as [q qIsRn].
  apply Preturn.
  exists (q + 1).
  unfold Cle.
  intros.
  apply Preturn.
  exists N.
  intros.
  specialize (prop N n (Nat.le_refl _) H0).
  asreturn2 (seq r N).
  asreturn2 (seq r n).
  simpl.
  classical_auto.
  simpl in qIsRn.
  subst.
  apply Preturn.
  apply (Qle_trans _ 0).
  2: {
    apply Qlt_le_weak.
    assumption.
  }
  field_simplify.
  apply (Qplus_le_l _ _ 1).
  field_simplify.
  apply Qabs_Qle_condition in prop as [prop _].
  apply Qopp_le_compat in prop.
  apply (fun e => Qle_trans _ _ _ e prop).
  apply Qeq_le.
  field.
Qed.

Theorem real_bounded_below_rational :
  forall r, [exists q, Cle (QinjR q) r].
Proof.
  intros.
  assert (0 < 1) as indeed. {
    repeat constructor.
  }
  assert (prop := property r 1 indeed).
  classical_auto.
  specialize prop as [N prop].
  assert (fact := proj2_sig (seq r N)).
  specialize fact as [rNexists rnUnique].
  classical_auto.
  specialize rNexists as [q qIsRn].
  apply Preturn.
  exists (q - 1).
  unfold Cle.
  intros.
  apply Preturn.
  exists N.
  intros.
  specialize (prop N n (Nat.le_refl _) H0).
  asreturn2 (seq r N).
  asreturn2 (seq r n).
  simpl.
  classical_auto.
  simpl in qIsRn.
  subst.
  apply Preturn.
  apply (Qle_trans _ 0).
  2: {
    apply Qlt_le_weak.
    assumption.
  }
  field_simplify.
  apply (Qplus_le_l _ _ 1).
  field_simplify.
  apply Qabs_Qle_condition in prop as [_ prop].
  apply (Qle_trans _ _ _ prop).
  apply Qle_refl.
Qed.

(*
I want a principle that says that if we have (f : A -> B), and
forall a1 a2, f a1 = f a2, and we have [A], then we get [[B]].
 *)

Theorem lub_but_its_only_a_prop (S : cauchy -> Prop) (nonempty : [exists r, S r])
        (bounded : [exists b, forall r, S r -> Cle r b])
  : [exists lub : cauchy, (forall r, S r -> Cle r lub)
                          /\ forall otherbound, (forall r, S r -> Cle r otherbound)
                                                -> Cle lub otherbound].
Proof.
  classical_auto.
  specialize bounded as [upperboundR upperboundproperty].
  specialize nonempty as [r rInS].
  Check real_bounded_above_rational.
  assert (rationalbound := real_bounded_above_rational upperboundR).
  classical_auto.
  specialize rationalbound as [upperboundQ QgtR].

  assert (lowerboundQ := real_bounded_below_rational r).
  classical_auto.
  specialize lowerboundQ as [lowerboundQ QltR].

  assert ([lowerboundQ <= upperboundQ]) as boundsle. {
    specialize (upperboundproperty r rInS).
    apply Cle_Qle.
    apply (Cle_trans _ _ _ (Cle_trans _ _ _ QltR upperboundproperty) QgtR).
  }
  classical_auto.
  assert (upperboundQ < upperboundQ + 1) as fact1. {
      apply (Qplus_lt_l _ _ (-upperboundQ)).
      field_simplify.
      repeat constructor.
  }
  assert (lowerboundQ < upperboundQ + 1) as boundsapart. {
    apply (Qle_lt_trans _ upperboundQ); assumption.
  }
  pose (ub := converging_cauchy (upperboundQ + 1) lowerboundQ (make_decider S) boundsapart).

  assert (exists r, S r /\ Cle (QinjR lowerboundQ) r) as isGoodLowerBound. {
    exists r.
    split; auto.
  }

  assert ((forall r : cauchy,
     (exists r0 : cauchy, S r0 /\ Cle r r0) ->
     ~ Cle (QinjR (upperboundQ + 1)) r)) as isGoodUpperBound. {
    intros r0 [r1 [Sr1 ler0r1]] bad.
    specialize (upperboundproperty r1 Sr1).
    apply (Cle_trans _ _ _ ler0r1) in upperboundproperty.
    apply (Cle_trans _ _ _ upperboundproperty) in QgtR.
    apply (Cle_trans _ _ _ bad) in QgtR.
    apply Cle_Qle in QgtR.
    apply classical_consistent.
    classical_auto.
    apply (Qplus_le_l _ _ (-upperboundQ)) in QgtR.
    field_simplify in QgtR.
    unfold Qle, BinInt.Z.le in QgtR.
    simpl in QgtR.
    apply Preturn.
    apply QgtR.
    reflexivity.
  }
    
  assert (is_bound := is_upper_bound (fun r' => exists r, S r /\ Cle r' r)
                                 (upperboundQ + 1) lowerboundQ boundsapart
                                 isGoodLowerBound isGoodUpperBound).
  
  assert (is_least := less_than_other_upper_bounds (fun r' => exists r, S r /\ Cle r' r)
                                      (upperboundQ + 1) lowerboundQ boundsapart
                                      isGoodLowerBound isGoodUpperBound).

  assert (bounds_equal := two_bounds_equal (upperboundQ + 1) lowerboundQ
        (make_decider (fun r' => exists r, S r /\ Cle r' r)) boundsapart).

  apply Preturn.

  exists (fst ((converging_cauchy (upperboundQ + 1) lowerboundQ
                                  (make_decider (fun r' : cauchy => exists r : cauchy, S r /\ Cle r' r)) boundsapart))).
  split.
  - intros r0 Sr0.
    assert (exists r : cauchy, S r /\ Cle r0 r) as temp. {
      exists r0.
      split; auto.
      Search (Cle _ _).
      apply Ceq_Cle.
      apply Ceq_refl.
    }
    simpl in is_bound.
          
    specialize (is_bound r0 temp).
    assumption.
  - intros.
    specialize (is_least otherbound).
    assert (forall r : cauchy,
               (exists r0 : cauchy, S r0 /\ Cle r r0) -> Cle r otherbound) as temp. {
      intros r0 [r1 [Sr1 ler0r1]].
      specialize (H r1 Sr1).
      apply (Cle_trans _ r1); auto.
    }
    specialize (is_least temp).
    Check Ceq_Cle.
    apply (Cle_trans _ _ _ (Ceq_Cle _ _ bounds_equal) is_least).
Qed.

(*
Would it be acceptable if our least upper bound property was something like:

[exists r, "r is upper bound" /\ "r is least"]?

rather than
lub : S .... -> cauchy
theorem : ["lub S is least upper bound"]

I think no, otherwise what is the point of the [[]] monad in general?
Thats like saying I could just use [], and
plus : forall x y : R, [exists z, <some property>]



Do I expect to be able to define a function
rat_above_real : R -> [[Q]]
such that
forall r, toProp (Cbind (rat_above_real r) (fun q => Cle r (QinjR q)))
?????

Surely this is possible. For example, "the smallest integer > r" is a uniquely defined thing.
It definitely exists and is unique, so I should be able to use the principle of
definite description.


If I had a quotient for cauchy sequences, then I could also use the fact that least upper bounds
are by definition unique to be able to get a unique value under [[]].
*)

Theorem plus_respects_cauchy_lemma : forall a a' b, Ceq a a' -> Ceq (Cplus a b) (Cplus a' b).
Proof.
  intros.
  unfold Ceq in *.
  intros.
  specialize (H epsilon H0).
  classical_auto.
  specialize H as [N H].
  apply Preturn.
  exists N.
  intros.

  specialize (H n H1).

  simpl (seq (Cplus a b) n).
  simpl (seq (Cplus a' b) n).
  asreturn2 (seq a n).
  asreturn2 (seq a' n).
  asreturn2 (seq b n).

  classical_auto.
  apply Preturn.
  assert (x + x1 - (x0 + x1) == x - x0) by field.
  apply (Qle_trans _ (Qabs (x - x0))).
  - apply Qeq_le.
    apply Qabs_wd.
    assumption.
  - assumption.
Qed.

Theorem plus_respects_cauchy : forall a b a' b',
    Ceq a a' -> Ceq b b' -> Ceq (Cplus a b) (Cplus a' b').
Proof.
  intros.
  apply (Ceq_trans _ (Cplus a' b)).
  - apply plus_respects_cauchy_lemma.
    assumption.
  - apply (Ceq_trans _ (Cplus b' a')).
    + apply (Ceq_trans _ (Cplus b a')).
      * apply Cplus_comm.
      * apply plus_respects_cauchy_lemma.
        assumption.
    + apply Cplus_comm.
Qed.

Theorem mult_respects_cauchy_lemma : forall a a' b, Ceq a a' -> Ceq (Cmult a b) (Cmult a' b).
Proof.
  intros.
  unfold Ceq in *.
  intros.

  assert (0 < 1) as lt01 by repeat constructor.

  Check real_bounded_above_rational.
  assert (boundu := real_bounded_above_rational b).
  assert (boundl := real_bounded_below_rational b).
  classical_auto.
  specialize boundu as [boundu bounduprop].
  specialize boundl as [boundl boundlprop].
  unfold Cle in bounduprop.


  assert (epsilon / 2 > 0) as hepspos. {
    apply (Qmult_lt_r _ _ 2). {
      repeat constructor.
    }
    field_simplify.
    assumption.
  }

  assert (Qabs boundu + Qabs boundl + 1 > 0) as poslemma. {
    apply Qabs2Plus1.
  }
  assert (epsilon / (Qabs boundu + Qabs boundl + 1) > 0) as boundpos. {
    apply (Qmult_lt_l _ _ (Qabs boundu + Qabs boundl + 1)).
    2: {
      field_simplify; auto.
      Search not Qeq Qlt.
      Search Qeq not "sym".
      apply Qnot_eq_sym.
      apply Qlt_not_eq.
      assumption.
    }
    assumption.
  }
  (* TODO: make it whatever it needs to be instead of just epsilon, probably epsilon / bound?  *)  
  specialize (bounduprop 1 lt01).
  specialize (boundlprop 1 lt01).
  specialize (H (epsilon / (Qabs boundu + Qabs boundl + 1)) boundpos).
  classical_auto.
  specialize bounduprop as [N1 bounduprop].
  specialize boundlprop as [N2 boundlprop].
  specialize H as [N3 H].

  apply Preturn.
  exists (max (max N1 N2) N3).

  intros.
  specialize (bounduprop n (Nat.max_lub_l _ _ _ (Nat.max_lub_l _ _ _ H1))).
  specialize (boundlprop n (Nat.max_lub_r _ _ _ (Nat.max_lub_l _ _ _ H1))).
  specialize (H n (Nat.max_lub_r _ _ _ H1)).

  simpl (seq (Cmult a b) n).
  simpl (seq (Cmult a' b) n).
  simpl in bounduprop.
  simpl in boundlprop.
  asreturn2 (seq a n).
  asreturn2 (seq a' n).
  asreturn2 (seq b n).
  
  classical_auto.
  apply Preturn.

  assert (x * x1 - x0 * x1 == (x - x0) * x1) as temp by field.
  apply (Qle_trans _ _ _ (Qeq_le (Qabs_wd _ _ temp))).
  apply (Qle_trans _ _ _ (Qeq_le (Qabs_Qmult _ _))).
  Search Qmult Qle.
  (* At this point, the lhs <= ep / (u + l + 1), and rhs <= (Qabs u + Qabs l + 1)*)
  assert (Qabs x1 <= Qabs boundu + Qabs boundl + 1). {
    apply (Qplus_le_l _ _ boundu) in bounduprop.
    field_simplify in bounduprop.
    apply (fun x => Qle_trans _ _ _ x (Qle_Qabs _)) in bounduprop.
    apply (fun x => Qle_trans _ _ _ x (Qabs_triangle boundu 1)) in bounduprop.
    apply (add_a_Qabs _ _ boundl) in bounduprop.
    (* now bounduprop is good *) 
    apply (Qplus_le_l _ _ (-boundl)) in boundlprop.
    field_simplify in boundlprop.
    apply (fun x => Qle_trans _ _ _ x (Qle_Qabs _)) in boundlprop.
    apply (fun x => Qle_trans _ _ _ x (Qabs_triangle (-boundl) 1)) in boundlprop.
    apply (fun x => Qle_trans _ _ _ x (Qeq_le (Qplus_compat (Qabs_opp _) (Qeq_refl _))))
      in boundlprop.
    apply (add_a_Qabs _ _ boundu) in boundlprop.
    field_simplify in bounduprop.
    field_simplify in boundlprop.
    assert (Qabs 1 == 1) by repeat constructor.
    apply (fun x => Qle_trans _ _ _ x (Qeq_le (Qplus_compat (Qplus_comm _ _) H2)))
      in bounduprop.
    apply (fun x => Qle_trans _ _ _ x (Qeq_le (Qplus_compat (Qeq_refl _) H2)))
      in boundlprop.

    apply Qopp_le_compat in boundlprop.
    field_simplify (- (-1 * x1)) in boundlprop.
    apply Qabs_Qle_condition; auto.
  }

  Search Qle Qmult.
  apply (Qle_trans _ (((epsilon / (Qabs boundu + Qabs boundl + 1)))
                      * (Qabs boundu + Qabs boundl + 1))).
  - apply Qmult_compat; auto; apply Qabs_nonneg.
  - field_simplify.
    + apply Qle_refl.
    + apply Qnot_eq_sym.
      apply Qlt_not_eq.
      assumption.
Qed.

Theorem mult_respects_cauchy : forall a b a' b',
    Ceq a a' -> Ceq b b' -> Ceq (Cmult a b) (Cmult a' b').
Proof.
  intros.
  apply (Ceq_trans _ (Cmult a' b)).
  - apply mult_respects_cauchy_lemma.
    assumption.
  - apply (Ceq_trans _ (Cmult b' a')).
    + apply (Ceq_trans _ (Cmult b a')).
      * apply Cmult_comm.
      * apply mult_respects_cauchy_lemma.
        assumption.
    + apply Cmult_comm.
Qed.

Definition Cnegate (x : cauchy) : cauchy := Cmult x (QinjR (-1)).

Theorem Cnegate_respects_cauchy : forall x y, Ceq x y -> Ceq (Cnegate x) (Cnegate y).
Proof.
  intros.
  unfold Cnegate.
  apply mult_respects_cauchy_lemma.
  assumption.
Qed.

Definition Czero : cauchy := QinjR 0.
Definition Cone : cauchy := QinjR 1.

Theorem additive_identity_l : forall x, Ceq (Cplus x Czero) x.
Proof.
  intros.
  apply exact_equality.
  intros.
  simpl.
  asreturn2 (seq x n).
  classical_auto.
  apply Preturn.
  field.
Qed.

Theorem additive_identity_r : forall x, Ceq (Cplus Czero x) x.
Proof.
  intros.
  apply exact_equality.
  intros.
  simpl.
  asreturn2 (seq x n).
  classical_auto.
  apply Preturn.
  field.
Qed.

Theorem multiplicative_identity_l : forall x, Ceq (Cmult x Cone) x.
Proof.
  intros.
  apply exact_equality.
  intros.
  simpl.
  asreturn2 (seq x n).
  classical_auto.
  apply Preturn.
  field.
Qed.

Theorem multiplicative_identity_r : forall x, Ceq (Cmult Cone x) x.
Proof.
  intros.
  apply exact_equality.
  intros.
  simpl.
  asreturn2 (seq x n).
  classical_auto.
  apply Preturn.
  field.
Qed.

(*
Lemma: if x != y, then exists N epsilon, Qabs (xn - yn) >= epsilon for n >= N
 *)
Theorem apart_property : forall x y,
    ~ (Ceq x y) ->
    [exists epsilon, epsilon > 0 /\ exists N : nat, forall n, le N n -> toProp (
     Cbind (seq x n) (fun xn =>
     Cbind (seq y n) (fun yn =>
                        Creturn (Qabs (yn - xn) >= epsilon))))].
Proof.
  intros.
  Check not_Cle_property_strong.
  apply (Pbind(Plem (Cle x y))); intros.
  destruct H0.
  - assert (~ Cle y x). {
      intros le.
      Search "antis" Ceq.
      apply H.
      apply Cle_antisymmetry; assumption.
    }
    assert (prop := not_Cle_property_strong y x H1).
    classical_auto.
    specialize prop as [epsilon [epspos [N prop]]].
    apply Preturn.
    exists epsilon.
    split; auto.
    exists N.
    intros.
    specialize (prop n H2).
    asreturn2 (seq x n).
    asreturn2 (seq y n).
    classical_auto.
    apply Preturn.
    Search Qabs Qle.
    apply (fun x => Qle_trans _ _ _ x (Qle_Qabs _)).
    apply (Qplus_le_r _ _ x0).
    field_simplify.
    assumption.
  - assert (prop := not_Cle_property_strong x y H0).
    classical_auto.
    specialize prop as [epsilon [epspos [N prop]]].
    apply Preturn.
    exists epsilon.
    split; auto.
    exists N.
    intros.
    specialize (prop n H1).
    asreturn2 (seq x n).
    asreturn2 (seq y n).
    classical_auto.
    apply Preturn.
    Search Qabs Qeq Qopp.
    apply (fun x => Qle_trans _ _ _ x (Qeq_le (Qabs_opp _))).
    apply (fun x => Qle_trans _ _ _ x (Qle_Qabs _)).
    apply (Qplus_le_r _ _ x1).
    field_simplify.
    assumption.
Qed.

(*Theorem not_equal_property  x y (ne : ~(Ceq x y))
  : [exists epsilon, exists N, forall n : nat, le N n ->
                                toProp (Cbind (seq x n) (fun xn =>
                                        Cbind (seq y n) (fun yn =>
                                        Creturn (Qabs (yn - xn) >= epsilon))))].
Proof.
  unfold Ceq in ne.
  apply not_forall_2 in ne.
  classical_auto.
  specialize ne as [epsilon [epspos prop]].
  assert (temp := not_exists _ _ prop); clear prop; rename temp into prop.
  
  assert ([exists N le N n -> toProp (Cbind (seq x n) (fun xn =>
                                                Cbind (seq y n) (fun yn =>
                                                Creturn (Qabs (xn - yn) <= epsilon))))]) as temp. {
    intros.
    specialize (prop N).
    simpl in prop.
    apply not_forall_2 in prop.
    classical_auto.
    specialize prop as [n [H prop]].
    apply Preturn.
    exists n.
    intros.*)
    
Lemma property_needed_for_Cinv epsilon bound1 bound2 x0 x1
      (bound1pos : 0 < bound1)
      (bound2pos : 0 < bound2)
      (prop : Qabs (x0 - x1) <= epsilon * bound1 * bound2)
      (apart1 : bound1 <= Qabs (0 - x0))
      (apart2 : bound2 <= Qabs (0 - x1))
  : Qabs (1 / x0 - 1 / x1) <= epsilon.
Proof.
  
  apply (fun x => Qle_trans _ _ _ x (Qeq_le (Qeq_sym _ _ (Qabs_opp _)))) in apart2, apart1.
  field_simplify (- (0 - x1)) in apart2.
  field_simplify (- (0 - x0)) in apart1.

  assert (0 < Qabs x0) as x0pos by apply (Qlt_le_trans _ _ _ bound1pos apart1).
  assert (~ x0 == 0) as x0nonzero
      by (apply Q_not_eq_lemma_3; auto).
  assert (0 < Qabs x1) as x1pos by apply (Qlt_le_trans _ _ _ bound2pos apart2).
  assert (~ x1 == 0) as x1nonzero by apply (Q_not_eq_lemma_3 _ x1pos).
  assert (1 / x0 - 1 / x1 == (x1 - x0) / (x0 * x1)) by (field; auto).
  assert (~ bound1 == 0) as bound1nonzero. {
    apply Qnot_eq_sym.
    apply Qlt_not_eq.
    assumption.
  }
  assert (~ bound2 == 0) as bound2nonzero. {
    apply Qnot_eq_sym.
    apply Qlt_not_eq.
    assumption.
  }

  apply (Qle_trans _ _ _ (Qeq_le (Qabs_wd _ _ H))).
  unfold Qdiv.
  apply (Qle_trans _ _ _ (Qeq_le (Qabs_Qmult _ _))).
  
  apply (Qle_trans _ _ _ (Qeq_le (Qabs_opp _))) in prop.
  field_simplify (- (x0 - x1)) in prop.
  apply (Qle_trans _ _ _ (Qeq_le (Qabs_wd _ _(Qplus_comm _ _)))) in prop.
  
  apply (Qle_trans _ ((epsilon * bound1 * bound2) * (/ (bound1 * bound2)))).
  - apply Qmult_compat.
    + apply Qabs_nonneg.
    + apply Qabs_nonneg.
    + assumption.
    + apply (Qle_compat (Qabs_Qinv _) (Qeq_refl _)).
      apply (Qle_trans _ _ _ (Qeq_le (Qinv_comp _ _(Qabs_Qmult _ _)))).
      assert (Qabs x0 * Qabs x1 > 0). {
        apply Qmult_lt_0_compat; auto.
      }
      assert (bound1 * bound2 > 0) by (apply Qmult_lt_0_compat; auto).
      apply (Qmult_le_l _ _ (Qabs x0 * Qabs x1)); auto.
      apply (Qmult_le_l _ _ (bound1 * bound2)); auto.
      field_simplify; auto.
      2: {
        split;
        apply Qnot_eq_sym;
        apply Qlt_not_eq;
        assumption.
      }
      assert (bound1nonneg := Qlt_le_weak _ _ bound1pos).
      assert (bound2nonneg := Qlt_le_weak _ _ bound2pos).
      apply Qmult_compat; auto.
  - field_simplify.
    + apply Qle_refl.
    + split; assumption.
Qed.

Definition Cinv (x : cauchy) (nonzero : ~ (Ceq x Czero)) : cauchy.
  refine {| seq := (fun n => Cbind (seq x n) (fun xn =>
                                                Creturn (1 / xn)))|}.
  intros.
  
  assert (apart := apart_property _ _ nonzero).
  classical_auto.
  specialize apart as [bound [boundpos [N1 apart]]].
  assert (epsilon * bound * bound > 0) as thingpos. {
    apply Qmult_lt_0_compat; auto.
    apply Qmult_lt_0_compat; auto.
  }
  assert (xprop := property x (epsilon * bound * bound) thingpos).
  classical_auto.
  specialize xprop as [N2 xprop].

  apply Preturn.
  exists (max N1 N2).
  intros.

  unfold Czero in apart.

  assert (apart1 := apart n (Nat.max_lub_l _ _ _ H0)).
  assert (apart2 := apart m (Nat.max_lub_l _ _ _ H1)).
  simpl (seq (QinjR 0) n) in apart1.
  simpl (seq (QinjR 0) m) in apart2.
  clear apart.
  specialize (xprop n m (Nat.max_lub_r _ _ _ H0) (Nat.max_lub_r _ _ _ H1)).

  asreturn2 (seq x n).
  asreturn2 (seq x m).
  classical_auto.
  apply Preturn.

  apply (property_needed_for_Cinv epsilon bound bound x0 x1 boundpos boundpos xprop apart1 apart2).
Defined.

Theorem Cinv_respects_cauchy : forall x y H1 H2,
    Ceq x y -> Ceq (Cinv x H1) (Cinv y H2).
Proof.
  intros.
  unfold Ceq.
  intros.
  unfold Ceq in H.
  simpl (seq (Cinv _ _) _).
  assert (apartx := apart_property _ _ H1).
  assert (aparty := apart_property _ _ H2).


  classical_auto.
  specialize apartx as [epsilon1 [eps1pos [N1 apartx]]].
  specialize aparty as [epsilon2 [eps2pos [N2 aparty]]].
    assert (epsilon * epsilon1 * epsilon2 > 0) as thingpos. {
    apply Qmult_lt_0_compat; auto.
    apply Qmult_lt_0_compat; auto.
  }
  specialize (H (epsilon * epsilon1 * epsilon2) thingpos).
  classical_auto.
  specialize H as [N3 H].

  apply Preturn.
  exists (max (max N1 N2) N3).
  intros.

  specialize (H n (Nat.max_lub_r _ _ _ H3)).
  specialize (apartx n (Nat.max_lub_l _ _ _ (Nat.max_lub_l _ _ _ H3))).
  specialize (aparty n (Nat.max_lub_r _ _ _ (Nat.max_lub_l _ _ _ H3))).
  
  simpl (seq Czero _) in apartx, aparty.
  asreturn2 (seq x n).
  asreturn2 (seq y n).
  classical_auto.
  apply Preturn.

  apply (property_needed_for_Cinv epsilon epsilon1 epsilon2
                                  x0 x1 eps1pos eps2pos H apartx aparty).
Defined.

(* I think this was the wrong property *)
Theorem Cle_add_property_wrong a b c
        (leab : Cle a b)
  : Cle (Cplus a c) (Cplus b c).
Proof.
  unfold Cle in *.
  intros.

  (*assert (propc := property c (epsilon / 2) hepspos).*)
  specialize (leab epsilon H).
  classical_auto.
  (*specialize propc as [N1 propc].*)
  specialize leab as [N leab].

  apply Preturn.
  exists N.
  intros.

  specialize (leab n H0).

  simpl (seq (Cplus _ _) _).
  asreturn2 (seq a n).
  asreturn2 (seq b n).
  asreturn2 (seq c n).

  classical_auto.
  apply Preturn.
  field_simplify.

  assumption.
Qed.

Theorem Cle_add_property a b
        (anonneg : Cle Czero a)
        (bnonneg : Cle Czero b)
  : Cle Czero (Cplus a b).
Proof.

  unfold Cle in *.
  intros.
  assert (epsilon / 2 > 0) as hepspos. {
    apply (Qmult_lt_r _ _ 2). {
      repeat constructor.
    }
    field_simplify.
    assumption.
  }
  specialize (anonneg (epsilon / 2) hepspos).
  specialize (bnonneg (epsilon / 2) hepspos).
  classical_auto.
  specialize anonneg as [N1 anonneg].
  specialize bnonneg as [N2 bnonneg].

  apply Preturn.
  exists (max N1 N2).
  intros.

  specialize (anonneg n (Nat.max_lub_l _ _ _ H0)).
  specialize (bnonneg n (Nat.max_lub_r _ _ _ H0)).

  simpl (seq (Cplus _ _) _).
  simpl (seq Czero _) in *.
  asreturn2 (seq a n).
  asreturn2 (seq b n).

  classical_auto.
  apply Preturn.

  Search Qle Qplus.
  assert (added := Qplus_le_compat _ _ _ _ anonneg bnonneg).
  field_simplify.
  repeat field_simplify in added.
  assumption.
Qed.  

(*Theorem Cle_mult_property a b c
        (leab : Cle a b)
  : Cle (Cmult a c) (Cmult b c).
Proof.*)
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
  

Lemma Cle_mult_property_lemma
      a b c d x y neg
      (propa : a <= x)
      (propb : x <= b)
      (propc : c <= y)
      (propd : y <= d)
      (isneg : neg <= 0)
      (H1 : a * d >= neg)
      (H2 : b * c >= neg)
  : neg <= x * y.
Proof.
  (* case on whether x and y are positive or negative *)
  Search Qlt or.
  assert (xcases := Q_pos_neg_cases x).
  assert (ycases := Q_pos_neg_cases y).
  destruct xcases, ycases.
  - 
    apply Qopp_le_compat in H, H0.
    field_simplify in H.
    field_simplify in H0.
    apply (Qle_trans _ ((-x) * (-y))).
    + Search 0%Q Qle Qmult.
      apply (Qle_trans _ _ _ isneg).
      apply Qmult_le_0_compat; auto.
    + field_simplify.
      apply Qle_refl.
  - apply Qopp_le_compat in H.
    field_simplify in H.
    apply (Qle_trans _ (-((-x) * y))).
    + remember ((-x) * y) as donttouchthis.
      apply Qopp_le_compat2.
      field_simplify.
      subst donttouchthis.
      apply (Qle_trans _ ((- a) * d)).
      * apply Qmult_compat; auto.
        apply Qopp_le_compat2.
        field_simplify.
        auto.
      * apply Qopp_le_compat in H1.
        field_simplify in H1.
        assumption.
    + field_simplify.
      apply Qle_refl.
  - apply Qopp_le_compat in H0.
    field_simplify in H0.
    apply (Qle_trans _ (-(x * (-y)))).
    + remember (x * (-y)) as donttouchthis.
      apply Qopp_le_compat2.
      field_simplify.
      subst donttouchthis.
      apply (Qle_trans _ (b * (-c))).
      * apply Qmult_compat; auto.
        apply Qopp_le_compat2.
        field_simplify.
        auto.
      * apply Qopp_le_compat in H2.
        field_simplify in H2.
        field_simplify.
        assumption.
    + field_simplify.
      apply Qle_refl.
  - apply (Qle_trans _ _ _ isneg).
    apply Qmult_le_0_compat; auto.
Qed.

Theorem Cle_mult_property a b
        (anonneg : Cle Czero a)
        (bnonneg : Cle Czero b)
  : Cle Czero (Cmult a b).
Proof.

  unfold Cle in *.
  intros.
  assert (epsilon / 2 > 0) as hepspos. {
    apply (Qmult_lt_r _ _ 2). {
      repeat constructor.
    }
    field_simplify.
    assumption.
  }
  assert (1 > 0) as le01 by repeat constructor.
  Check real_bounded_above_rational.
  assert (bounda := real_bounded_above_rational a).
  assert (boundb := real_bounded_above_rational b).
  classical_auto.
  specialize bounda as [bounda boundaprop].
  specialize boundb as [boundb boundbprop].
  unfold Cle in boundaprop, boundbprop.
  specialize (boundaprop 1 le01).
  specialize (boundbprop 1 le01).
  classical_auto.
  specialize boundaprop as [N3 boundaprop].
  specialize boundbprop as [N4 boundbprop].

  assert (forall x, Qabs x + 1 > 0) as formpos. {
    intros.
    apply (Qle_lt_trans _ (Qabs x)).
    + apply Qabs_nonneg.
    + apply (Qplus_lt_l _ _ (- (Qabs x))).
      field_simplify.
      repeat constructor.
  }

  assert (forall x, ~ Qabs x + 1 == 0) as formnonneg. {
    intros.
    apply Qnot_eq_sym.
    apply Qlt_not_eq.
    apply formpos.
  }
  
  (* I need bounda and boundb to be non-negative. Or maybe I can just
   throw an absolute value in there somewhere? *)
  assert (epsilon / (Qabs bounda + 1) > 0) as thingapos. {
    unfold Qdiv.
    apply Qmult_lt_0_compat.
    - assumption.
    - apply Qinv_lt_0_compat.
      apply formpos.
  }
  assert (epsilon / (Qabs boundb + 1) > 0) as thingbpos. {
    unfold Qdiv.
    apply Qmult_lt_0_compat.
    - assumption.
    - apply Qinv_lt_0_compat.
      apply formpos.
  }
    
  specialize (anonneg (epsilon / (Qabs boundb + 1)) thingbpos).
  specialize (bnonneg (epsilon / (Qabs bounda + 1)) thingapos).
  classical_auto.
  specialize anonneg as [N1 anonneg].
  specialize bnonneg as [N2 bnonneg].

  apply Preturn.
  exists (max (max N1 N2) (max N3 N4)).
  intros.

  specialize (anonneg n (Nat.max_lub_l _ _ _ (Nat.max_lub_l _ _ _ H0))).
  specialize (bnonneg n (Nat.max_lub_r _ _ _ (Nat.max_lub_l _ _ _ H0))).
  specialize (boundaprop n (Nat.max_lub_l _ _ _ (Nat.max_lub_r _ _ _ H0))).
  specialize (boundbprop n (Nat.max_lub_r _ _ _ (Nat.max_lub_r _ _ _ H0))).

  simpl (seq (QinjR _) _) in *.
  simpl (seq (Cmult _ _) _).
  simpl (seq Czero _) in *.
  asreturn2 (seq a n).
  asreturn2 (seq b n).

  classical_auto.
  apply Preturn.

  apply Qopp_le_compat in anonneg, bnonneg.
  field_simplify in anonneg; auto.
  field_simplify in bnonneg; auto.
  apply (Qplus_le_l _ _ bounda) in boundaprop.
  field_simplify in boundaprop.
  apply (Qplus_le_l _ _ boundb) in boundbprop.
  field_simplify in boundbprop.
  apply (fun x => Qle_trans _ _ _ x (Qplus_le_compat _ _ _ _ (Qle_Qabs _) (Qle_refl _)))
    in boundaprop, boundbprop.

  apply Qopp_le_compat2.
  field_simplify.

  Check Cle_mult_property_lemma.
  Check (Cle_mult_property_lemma
           (-1 * epsilon / (Qabs bounda + 1))
           (Qabs bounda + 1)
           (-1 * epsilon / (Qabs boundb + 1))
           (Qabs boundb + 1)).
  Check (Cle_mult_property_lemma
           (-1 * epsilon / (Qabs bounda + 1))
           (Qabs bounda + 1)
           (-1 * epsilon / (Qabs boundb + 1))
           (Qabs boundb + 1)
           x x0 (- epsilon)).
  apply Qopp_lt_compat in H.
  field_simplify in H.
  apply Qlt_le_weak in H.
  Check (Cle_mult_property_lemma
           (-1 * epsilon / (Qabs boundb + 1))
           (Qabs bounda + 1)
           (-1 * epsilon / (Qabs bounda + 1))
           (Qabs boundb + 1)
           x x0 (- epsilon)
           anonneg
           boundaprop
           bnonneg
           boundbprop
           H).

  assert (- epsilon <= (-1 * epsilon / (Qabs boundb + 1)) * (Qabs boundb + 1)). {
    apply Qeq_le.
    field.
    auto.
  }
  assert (- epsilon <= (Qabs bounda + 1) * (-1 * epsilon / (Qabs bounda + 1))). {
    apply Qeq_le.
    field.
    auto.
  }

  apply (Cle_mult_property_lemma
           (-1 * epsilon / (Qabs boundb + 1))
           (Qabs bounda + 1)
           (-1 * epsilon / (Qabs bounda + 1))
           (Qabs boundb + 1)
           x x0 (- epsilon)
           anonneg
           boundaprop
           bnonneg
           boundbprop
           H
           H1
           H2).
Qed.

Theorem additive_inverse_r : forall x, Ceq (Cplus x (Cnegate x)) Czero.
Proof.
  intros.
  apply exact_equality.
  intros.
  simpl.
  asreturn2 (seq x n).
  classical_auto.
  apply Preturn.
  field.
Qed.

Theorem additive_inverse_l : forall x, Ceq (Cplus (Cnegate x) x) Czero.
Proof.
  intros.
  apply exact_equality.
  intros.
  simpl.
  asreturn2 (seq x n).
  classical_auto.
  apply Preturn.
  field.
Qed.

Theorem multiplicative_inverse_r : forall x (H : ~ (Ceq x Czero)),
    Ceq (Cmult x (Cinv x H)) Cone.
Proof.
  intros.
  unfold Ceq.
  intros.
  assert (prop := apart_property _ _ H).
  classical_auto.
  specialize prop as [epsilon2 [eps2pos [N prop]]].
  
  apply Preturn.
  exists N.
  intros.
  specialize (prop n H1).
  simpl (seq Czero _) in prop.
  simpl (seq (Cmult x (Cinv x H)) n).
  simpl (seq Cone n).
  asreturn2 (seq x n).
  classical_auto.
  apply Preturn.

  apply (Qlt_le_trans _ _ _ eps2pos) in prop.
  Search (0 < Qabs _)%Q.
  apply Q_not_eq_lemma_2 in prop.
  apply Qnot_eq_sym in prop.
  field_simplify (x0 * (1 / x0) - 1); auto.
  simpl.
  apply Qlt_le_weak.
  assumption.
Qed.

Theorem multiplicative_inverse_l : forall x (H : ~ (Ceq x Czero)),
    Ceq (Cmult (Cinv x H) x) Cone.
Proof.
  intros.
  unfold Ceq.
  intros.
  assert (prop := apart_property _ _ H).
  classical_auto.
  specialize prop as [epsilon2 [eps2pos [N prop]]].
  
  apply Preturn.
  exists N.
  intros.
  specialize (prop n H1).
  simpl (seq Czero _) in prop.
  simpl (seq (Cmult (Cinv x H) x) n).
  simpl (seq Cone n).
  asreturn2 (seq x n).
  classical_auto.
  apply Preturn.

  apply (Qlt_le_trans _ _ _ eps2pos) in prop.
  Search (0 < Qabs _)%Q.
  apply Q_not_eq_lemma_2 in prop.
  apply Qnot_eq_sym in prop.
  field_simplify ((1 / x0) * x0 - 1); auto.
  simpl.
  apply Qlt_le_weak.
  assumption.
Qed.

Theorem distributivity : forall x y z,
    Ceq (Cmult x (Cplus y z)) (Cplus (Cmult x y) (Cmult x z)).
Proof.
  intros.
  apply exact_equality.
  intros.
  simpl.
  asreturn2 (seq x n).
  asreturn2 (seq y n).
  asreturn2 (seq z n).
  classical_auto.
  apply Preturn.
  Search Q "dist".
  apply Qmult_plus_distr_r.
Qed.

(*
Here is everything in one place to check that I have fully formalized the real numbers.
*)

(* Basic definitions *)
Check cauchy.
Check Ceq.
Check Cle.
Check Cplus.
Check Cmult.
Check Cnegate.
Check Cinv.
Check Czero.
Check Cone.

(* Basic order and equivalence axioms  *)
Check Ceq_trans.
Check Ceq_refl.
Check Ceq_sym.

Check Cle_trans.
Check Cle_antisymmetry.
Check Ceq_Cle.

(* Basic definitions respect equivalence *)
Check plus_respects_cauchy.
Check mult_respects_cauchy.
Check Cnegate_respects_cauchy.
Check Cinv_respects_cauchy.

(* Field Axioms *)
Check Cplus_assoc.
Check additive_identity_l.
Check additive_identity_r.
Check additive_inverse_l.
Check additive_inverse_r.
Check Cplus_comm.
Check Cplus_assoc.
Check multiplicative_identity_l.
Check multiplicative_identity_r.
Check multiplicative_inverse_l.
Check multiplicative_inverse_r.
Check Cmult_comm.
Check distributivity.

(* Total ordering *)
Check total_ordering.
Check Cle_add_property.
Check Cle_mult_property.

(* Existence of least upper bounds *)
Check lub_but_its_only_a_prop.
  
(* The only axioms used are functional and propositional extensionality, as this command shows: *)
Definition all_definitions :=
  (cauchy, Ceq, Cle, Cplus, Cmult, Cnegate, Cinv, Czero, Cone,
    Ceq_trans, Ceq_refl, Ceq_sym, Cle_trans, Cle_antisymmetry, Ceq_Cle,
    plus_respects_cauchy, mult_respects_cauchy, Cnegate_respects_cauchy, Cinv_respects_cauchy,
    Cplus_assoc, additive_identity_l, additive_identity_r, additive_inverse_l,
    additive_inverse_r, Cplus_comm, Cplus_assoc, multiplicative_identity_r,
    multiplicative_identity_l, multiplicative_inverse_l, multiplicative_inverse_r, Cmult_comm,
    distributivity,
    total_ordering, Cle_add_property, Cle_mult_property, lub_but_its_only_a_prop).

Print Assumptions all_definitions.
