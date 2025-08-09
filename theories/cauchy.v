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
    apply (Qmult_lt_r _ _ 2). {repeat constructor.}
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
    apply (Qle_trans _ (x1 - x0)). {apply Qeq_le. field.}
    field_simplify.
    assumption.
  - assumption.
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
          (*match bt with (b , t) =>*)
          let t := fst bt in
          let b := snd bt in
          let half := (b + t) / 2 in
          Pif (decide half) (t , half) (half , b)
          (*end*) )
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
      apply (@QOrder.eq_le _ (tm - tn)). {field.}
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
      apply (@QOrder.eq_le _ (bm - bn)). {field.}
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
