
Require Import QArith.Qcanon.
Require Import QArith.Qcabs.
Require Import Qabs.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import base.

(*
I'm going to try QCanon to see if that makes things better or worse
*)

(* Classical rational number *)

Definition CQ := Classical Qc.

(* TODO: Do I need the [] around the exists? *)
Record cauchy : Type :=
  { seq : nat -> CQ
  ; property : forall epsilon : Qc, (Qclt 0 epsilon) -> [exists N : nat,
     forall n m : nat, le N n -> le N m ->
     toProp (
         Cbind (seq n) (fun x => Cbind (seq m) (fun y =>
         Creturn (Qcle (Qcabs (x - y)) epsilon))))]

  }.

(* Maybe I need an [] around the exists N ??? *)
Definition Ceq (seq1 seq2 : cauchy) : Prop :=
    forall epsilon : Qc, epsilon > 0 -> [exists N : nat, forall n : nat, le N n ->
     toProp (
     Cbind (seq seq1 n) (fun x => Cbind (seq seq2 n) (fun y =>
     Creturn (Qcle (Qcabs (x - y)) epsilon))))].

(* TODO: I don't think that this definition is correct.
 There can be two sequences both converging to the same number but one is always greater
 than the other.
 There are a few ways to fix this:
 1) postulate that there exists epsilon > 0, and x is < y by at least epsilon
 2) add a disjunction saying "or Ceq seq1 seq2" and replace < with <=,
    and make this a definintion of <=. Then, the definition < would be this, but not equal.
 3) add a conjunction saying they are not equal, and this is a definition of <.
*)
Definition Clt (seq1 seq2 : cauchy) : Prop :=
  [exists N : nat, forall n : nat, le N n ->
     toProp (
       Cbind (seq seq1 n) (fun x => Cbind (seq seq2 n) (fun y =>
       Creturn (Qlt x y))))]
  /\ (~ Ceq seq1 seq2).

Require Import PeanoNat.
Require Import Nat.


Definition Cplus (seq1 seq2 : cauchy) : cauchy.
  refine {| seq := (fun n => Cbind (seq seq1 n) (fun x =>
                            Cbind (seq seq2 n) (fun y =>
                            Creturn (Qcplus x y))))|}.
  intros.
  pose (halfe := Qcdiv epsilon (Q2Qc 2)).
  assert (halfe > 0) as Hh. {
    Check Qmult_lt_0_compat.
    Search Qc (Qclt 0 _) Qcmult.
    apply Qcmult_lt_0_compat.
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
  Check ClassicalInd.

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

(*
Fixpoint max_up_to (f : nat -> CQ) (n : nat) : CQ.
  refine (match n with
          | O => Creturn 0
          | S n' => Cbind (f n) (fun fn =>
                    Cbind (max_up_to f n') (fun rec =>
                    Creturn (Qmax fn rec)))
          end).
Abort.

Theorem cauchy_upper_bound (c : cauchy) :
  [ exists bound : Q,
    forall n,
      toProp (
          Cbind (seq c n) (fun x => Creturn (Qlt x bound)))].
Proof.
  assert (Qlt 0 1) as fact by repeat constructor.
  assert (prop := property c 1 fact).
  classical_auto.
  specialize prop as [N prop].
  specialize (prop N).
  asreturn2 (seq c N).
  (* why can't I rewrite under the forall? *)
  Fail rewrite bindDef in prop.
  assert (forall m, (N <= m)%nat ->
                    toProp (Cbind (seq c m) (fun y => Creturn (Qabs (x - y) <= 1)))) as prop'. {
    intros.
    specialize (prop m (Nat.le_refl N) H).
    asreturn2 (seq c m).
    classical_auto.
    apply Preturn.
    assumption.
  }
  clear prop.
  (* I need to take the maximum of all elements less than N *)
  
  
Abort.
*)

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

Require Import QOrderedType.
Check Q_as_DT.eq_equiv.
Check Q_as_OT.lt_strorder.
Print StrictOrder.
Check StrictOrder_Transitive.
Check (StrictOrder_Transitive (Q_as_OT.lt_strorder)).

Print Irreflexive.
Print Reflexive.

Theorem Clt_antireflexive : forall x y, Ceq x y -> ~ (Clt x y).
Proof.
  intros x y Heq Hlt.
  unfold Ceq, Clt in *.
Abort.

Theorem not_exists (T : Type) (P : T -> Prop) (E : ~exists t, P t)
  : forall t, ~(P t).
Proof.
  intros t Pt.
  apply E.
  exists t.
  assumption.
Qed.

(* (Ceq x y) \/ (Clt x y) = ~ (Clt y x) *)

Theorem anti_sym : forall x y, Clt x y -> Clt y x -> False.
Proof.
  intros x y H1 H2.
  unfold Clt in H1, H2.
  apply classical_consistent.
  specialize H1 as [H1 Neq1].
  specialize H2 as [H2 Neq2].
  classical_auto.
  specialize H1 as [N1 H1].
  specialize H2 as [N2 H2].

  specialize (H1 (max N1 N2) (Nat.max_lub_l _ _ _ (Nat.le_refl _))).
  specialize (H2 (max N1 N2) (Nat.max_lub_r _ _ _ (Nat.le_refl _))).
  asreturn2 (seq x (max N1 N2)).
  asreturn2 (seq y (max N1 N2)).
  classical_auto.
  apply Preturn.
  Search Qlt not.
  apply (Qlt_trans _ _ _ H1) in H2.
  apply (QOrder.lt_irrefl H2).
Qed.

Theorem anti_refl_2 : forall x y, Clt x y -> Ceq x y -> False.
Proof.
  intros x y H1 H2.
  unfold Clt, Ceq in *.
Abort.
  
Theorem anti_refl : forall x y, ~ Clt x y -> ~Clt y x -> Ceq x y.
Proof.
  intros x y H H0.
  (*
        There are three parts of this proof: dealing with monad stuff, dealing with cauchy sequence
        stuff, and finally some proofs about rational numbers.
        Because of the nature of the Classical monad, we need to make some choices about how to
        instantiate some values before completing the monad stuff. Therefore, there are things like
        (epsilon / 3) that are interspersed in the monad stuff, even though the details of that
        value don't become relevant until later in the proof.
   *)
  unfold Clt in H, H0.
  unfold Ceq.
  intros.

  apply not_and in H, H0.
  classical_auto.

  (* deal with the easy cases, where we just get a proof that (Ceq x y) *)
  destruct H0.
  2: {
    pbind H0.
    apply Ceq_sym in H0.
    exact (H0 epsilon H1).
  }
  destruct H.
  2: {
    pbind H.
    exact (H epsilon H1).
  }
  
  assert (epsilon / 2 > 0) as epspos. {
    apply (Qmult_lt_r _ _ 2). {repeat constructor.}
    field_simplify.
    assumption.
  }

  assert (propx :=property x (epsilon / 2) epspos).
  pbind propx.
  assert (propy := property y (epsilon / 2) epspos).
  pbind propy.
  destruct propx as [N3 propx].
  destruct propy as [N4 propy].
  pbind H.
  pbind H0.
  
  assert (H' := not_exists _ _ H); simpl in H'; clear H.
  assert (H0' := not_exists _ _ H0); simpl in H0'; clear H0.
  specialize (H' (max N3 N4)).
  specialize (H0' (max N3 N4)).
  apply not_forall_2 in H', H0'.
  classical_auto.
  
  specialize H0' as [N1 [N1le seqN1]].
  specialize H' as [N2 [N2le seqN2]].

  apply Preturn.
  exists (max N3 N4).
  intros.

  assert (propx_n_N2 := propx n N2 (Nat.max_lub_l _ _ _ H) (Nat.max_lub_l _ _ _ N2le)).
  assert (propx_N1_n := propx N1 n (Nat.max_lub_l _ _ _ N1le) (Nat.max_lub_l _ _ _ H)).
  assert (propy_n_N2 := propy n N1 (Nat.max_lub_r _ _ _ H) (Nat.max_lub_r _ _ _ N1le)).
  assert (propy_N1_n := propy N2 n (Nat.max_lub_r _ _ _ N2le) (Nat.max_lub_r _ _ _ H)).
  clear propx propy.

  asreturn2 (seq x N1).
  asreturn2 (seq y N1).
  asreturn2 (seq x N2).
  asreturn2 (seq y N2).
  asreturn2 (seq x n).
  asreturn2 (seq y n).
  classical_auto.
  apply Preturn.

  (* At this point, the proof has been reduced to statements about rationals.
       Does the length of the remaining proof reflect on the Rocq stdlib lacking
       more useful theorems and tactics, or my own lack of knowledge of it? *)

  assert (2 * (epsilon / 2) == epsilon) as Heps3 by field.
  apply (Qle_trans _ (2 * (epsilon / 2)) _).
  2: {
    apply Qle_lteq.
    apply or_intror.
    assumption.
  }


  apply QOrder.not_gt_le in seqN1.
  apply QOrder.not_gt_le in seqN2.

  remember (epsilon / 2) as halfeps.

  
  apply Qabs_diff_Qle_condition.      
  apply Qabs_diff_Qle_condition in propy_N1_n as [x3x5 x5x3].
  apply Qabs_diff_Qle_condition in propy_n_N2 as [x5x1 x1x5].
  apply Qabs_diff_Qle_condition in propx_N1_n as [x0x4 x4x0].
  apply Qabs_diff_Qle_condition in propx_n_N2 as [x4x2 x2x4].

  apply (Qplus_le_l _ _ halfeps) in x5x1, x0x4, x4x2.

  
  
  repeat field_simplify in x5x1.
  field_simplify in x5x1.
  field_simplify in x0x4.
  field_simplify in x4x2.
  

  split.
  * apply (Qplus_le_l _ _ (2 * halfeps)).
    field_simplify.
    apply (Qle_trans _ _ _ x4x0).
    apply (Qplus_le_l _ _ (- halfeps)).
    field_simplify.
    apply (Qle_trans _ _ _ seqN1).
    apply (Qle_trans _ _ _ x1x5).
    field_simplify.
    apply Qle_refl.
  * apply (Qle_trans _ _ _ x5x3).
    apply (Qplus_le_l _ _ (- halfeps)).
    field_simplify.
    apply (Qle_trans _ _ _ seqN2).
    apply (Qle_trans _ _ _ x2x4).
    field_simplify.
    apply Qle_refl.
Qed.

Theorem C_total_order : forall x y, [Clt x y \/ Ceq x y \/ Clt y x].
Proof.
  intros.
  apply (Pbind (Plem (Clt x y))); intros.
  destruct H.
  - apply Preturn.
    apply or_introl.
    assumption.
  - apply (Pbind (Plem (Clt y x))); intros.
    destruct H0.
    + apply Preturn.
      apply or_intror.
      apply or_intror.
      assumption.
    + apply Preturn.
      apply or_intror.
      apply or_introl.
      apply anti_refl; auto.
Qed.

(*
The hard part will be the completeness property.
See the proof in wikipedia https://en.wikipedia.org/wiki/Construction_of_the_real_numbers#Construction_from_Cauchy_sequences.
It should be possible, it only requires LEM and I have that.
Still, the construction creates two new cauchy sequences where each next element needs a new
invocation of LEM. Will that be possible?

I think it will work.
Something that will be useful will be to define the propositional if thing.
I can define the sequence by recursion over the nat input, and at each step I can use a propositional if
on the statement that the midpoint is an upper bound of the set to determine what happens at the next step.
*)

(*
Given a bounded set S, I need to construct a pair of sequences that converge to the lub from
the top and bottom.
*)

(* Output is (top, bottom) *)
Fixpoint converging (startTop startBot: CQ) (decide : Q -> Prop) (index :  nat)
  : Classical (Q * Q).
  refine (
      match index with
      | O => Cbind startTop (fun t =>
             Cbind startBot (fun b =>
             Creturn (t , b)))
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
        (H : toProp (
               Cbind startTop (fun t =>
               Cbind startBot (fun b =>
               Creturn (b < t)))))
  :
  toProp (Cbind (converging startTop startBot decide n) (fun tb =>
          let t := fst tb in
          let b := snd tb in
          Creturn (b < t))).
Proof.
  induction n.
  -
    simpl in *.
    asreturn2 startTop.
    asreturn2 startBot.
    classical_auto.
    apply Preturn.
    simpl.
    assumption.
  - asreturn2 startTop.
    asreturn2 startBot.
    simpl in *.
    asreturn2 (converging (Creturn x) (Creturn x0) decide n).
    destruct x1 as [t b].
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
        (H2 : toProp (
                 Cbind startTop (fun t =>
                 Cbind startBot (fun b =>
                 Creturn (b < t)))))
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

    asreturn2 startTop.
    asreturn2 startBot.
    classical_auto.
    specialize (separation (Preturn H2)).
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

(*
To prove that the sequence is cauchy, I need to show
- for any epsilon>0, (startTop - startBot) halved some number of times is < epsilon
- all subsequent elements of the sequence after that point are within epsilon
 *)
Search Q Z.
Print Qpower.
Check Qpower_positive.
Print positive.
Search Qpower_positive.
Check pow.
Search pow.
Search (Z -> Q).
Search "pow" Z.
Search Z.pow ex Z.le.
Check Z.log2_spec_alt.


(*
Maybe I can do something like:
- assume w.l.o.g. that numerator is 1
- halving doubles the denomenator - this at least adds 1 to the denominator each time
- so denominator after n doubles is >= n
 *)

Require Import PosDef.

(*
Fixpoint double_n_times (n : nat) (z : positive) : positive :=
  match n with
  | O => z
  | S n' => (double_n_times n' z) * 2
  end.

Lemma half_double_relation (n : nat) (q : Q) :
  Qmake (Qnum (half_n_times n q))(Qden (half_n_times n q))
  = Qmake (Qnum q) (double_n_times n (Qden q)).
Proof.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    inversion IHn; clear IHn.
    destruct (half_n_times n q).
    simpl in *.
    apply f_equal2.
    + ring_simplify.
      reflexivity.
    + reflexivity.
Qed.

Lemma some_n_big_enough (z1 z2 : positive) :
  Pos.gt (double_n_times (Pos.to_nat (z2 - z1)) z1) z2.
Proof.
  Search positive nat.

  remember (Pos.to_nat (z2 - z1)) as x.
  induction x.
  - simpl.
    apply (f_equal Pos.of_nat) in Heqx.
    simpl in Heqx.
    Search Pos.of_nat Pos.to_nat.
    rewrite Pos2Nat.id in Heqx.
    Search Pos.sub Pos.add.
    Check Pos2Nat.id.
    Search Pos.sub Pos.gt.
Abort.
    
Theorem test_something_like_this (q : Q) (eps : Q) :
  exists n, half_n_times n q < eps.
Proof.
  Search Q Z.
Abort.

Theorem test_something_like_this_2 (q : Q) (eps : Q) :
  ~ forall n, half_n_times n q > eps.
Proof.
  intros H.
  Print Q.
  Check Qnum.
Abort.
 *)

Fixpoint half_n_times (n : nat) (q : Q) : Q :=
  match n with
  | O => q
  | S n' => (half_n_times n' q) / 2
  end.

Fixpoint double_n_times (n : nat) (q : Q) : Q :=
  match n with
  | O => q
  | S n' => (double_n_times n' q) * 2
  end.

Search Z Q.
Search Z.pow Z.lt Z.log2_up.
Search Q "pow".
Search Qpower.
Print power_theory.
Search Q nat.

Fixpoint double_Z_n_times (n : nat) (z : Z) : Z :=
  match n with
  | O => z
  | S n' => (double_Z_n_times n' z) * 2
  end.

Require Import IntDef.
Search (Z -> nat).

Theorem doubling_makes_it_bigger :
  forall (x y : Z),
    Z.le 0 x
    -> Z.le 0 y
  -> Z.lt y (double_Z_n_times (Z.to_nat (x - y)) (x + 1)).
Proof.
  intros.

  remember (x - y)%Z as diff.
  induction diff.
  - simpl in *.
    apply (f_equal (fun z => z + y)%Z) in Heqdiff.
    ring_simplify in Heqdiff.
    subst.
    apply (Zorder.Zplus_lt_reg_r _ _ (- x)).
    ring_simplify.
    repeat constructor.
  - Print positive.
Abort.

Fixpoint double_pos_n_times (n : nat) (z : positive) : positive :=
  match n with
  | O => z
  | S n' => (double_pos_n_times n' z) * 2
  end.

Require Import IntDef.
Search (Z -> nat).

Theorem doubling_pos_makes_it_bigger :
  forall (x y : positive),
  Pos.lt y (double_pos_n_times (Pos.to_nat (x - y)) (x + 1)).
Proof.
  intros.
  remember (x - y)%positive as diff.
  Search positive "ind".
  Check Pos.peano_ind.
  generalize dependent Heqdiff.
  refine (Pos.peano_ind (fun diff => (diff = (x - y) ->
                                      y < double_pos_n_times (Pos.to_nat diff) (x + 1))%positive)
        _ _ diff).
  - intros.
    simpl in *.

Definition convergingTop (startTop startBot : CQ) (decide : Q -> Prop) : cauchy.
  refine {|seq := fun n => Cbind (converging startTop startBot decide n) (fun pair =>
                           match pair with (t , b) =>
                           Creturn t end )|}.
  intros.
  simpl.
  assert ((fun x : Q * Q => let (t, _) := x in Creturn t) = (fun x => Creturn (fst x))). {
    extensionality x.
    intros.
    destruct x.
    reflexivity.
  }
  repeat rewrite H0.
  repeat rewrite bindDef.
  Check monadlaw2.
Abort.
 
