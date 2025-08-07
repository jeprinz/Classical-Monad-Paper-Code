Require Import base.
Require Import QArith.
Require Import Qabs.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

(* TODO: Maybe I should first implement reals using LEM and choice? Or look at lean's implementation? *)

(* Something to consider: represent cauchy as Q -> Q, which means given epsilon, 
 rest of outputs should be within epsilon *)

(* Classical rational number *)

Definition CQ := Classical Q.

(* TODO: Do I need the [] around the exists? *)
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

Definition Clt (seq1 seq2 : cauchy) : Prop :=
  [exists N : nat, forall n : nat, le N n ->
     toProp (
       Cbind (seq seq1 n) (fun x => Cbind (seq seq2 n) (fun y =>
       Creturn (Qlt x y))))].

Require Import PeanoNat.
Require Import Nat.

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

Theorem anti_refl_2 : forall x y, Clt x y -> Clt y x -> False.
Proof.
  intros x y H1 H2.
  unfold Clt in H1, H2.
  apply classical_consistent.
  classical_auto.
  specialize H1 as [N1 H1].
  specialize H2 as [N2 H2].
  Check Nat.max_lub_l.
  specialize (H1 (max N1 N2) (Nat.max_lub_l _ _ _ (Nat.le_refl _))).
  specialize (H2 (max N1 N2) (Nat.max_lub_r _ _ _ (Nat.le_refl _))).
  asreturn2 (seq x (max N1 N2)).
  asreturn2 (seq y (max N1 N2)).
  classical_auto.
  apply Preturn.
Abort.
  
  

Theorem anti_refl : forall x y, ~ Clt x y -> ~Clt y x -> Ceq x y.
Proof.
  intros.
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
Fixpoint half_n_times (n : nat) (q : Q) : Q :=
  match n with
  | O => q
  | S n' => (half_n_times n' q) / 2
  end.

(*
Maybe I can do something like:
- assume w.l.o.g. that numerator is 1
- halving doubles the denomenator - this at least adds 1 to the denominator each time
- so denominator after n doubles is >= n
 *)

Require Import PosDef.


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
  exists n, Pos.gt (double_n_times n z1) z2.
Proof.
  Search positive nat.

  remember (Pos.to_nat (z2 - z1)) as times.
  exists times.
  generalize dependent z1.
  generalize dependent z2.
  induction times.
  - intros.
    simpl.
    assert (is_pos := Pos2Nat.is_pos (z2 - z1)).
    rewrite Heqtimes in is_pos.
    apply Nat.lt_irrefl in is_pos.
    contradiction.
  - intros.
    Search Pos.of_nat S.
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
 
