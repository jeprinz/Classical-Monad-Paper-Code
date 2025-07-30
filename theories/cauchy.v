Require Import base.
Require Import QArith.
Require Import Qabs.

Check Q.

(* Classical rational number *)

Definition CQ := Classical Q.

(* Just as an example, define addition and prove its commutative on CQ *)

Search Qplus.
Locate "==".

Definition CQplus (a b : CQ) : CQ :=
  Cbind a (fun x =>
  Cbind b (fun y =>
  Creturn (x + y))).

(*Definition PCclassicalInj : Classical Prop -> Classical *)

Definition CQeq (a b : CQ) : Prop :=
  toProp (
      Cbind a (fun x =>
      Cbind b (fun y =>
      Creturn (Qeq x y)))).

(*TODO: There must be a nicer way to put classical in the definition of CQeq or something *)
Theorem CQplus_comm : forall a b, CQeq (CQplus a b) (CQplus b a).
Proof.
  intros.
  unfold CQeq.
  asreturn a.
  asreturn b.
  unfold CQplus, CQeq.
  repeat rewrite bindDef.
  apply toPropRet.
  apply Preturn.
  apply Qplus_comm.
Qed.
(*goal: define CQeq properly so that the proof of this theorem is just applying some induction
or something and then just calling Qplus_comm. *)

(*********************************************************************)

Definition cauchy' : Type :=
  {seq : nat -> Q |
    forall epsilon : Q, epsilon > 0 -> exists N : nat, forall n : nat, le N n ->
     Qle (Qabs (seq N - seq n)) epsilon}.

Definition cauchy : Type :=
  {seq : nat -> CQ |
    forall epsilon : Q, epsilon > 0 -> exists N : nat, forall n m : nat, le N n -> le N m ->
     toProp (
         Cbind (seq n) (fun x => Cbind (seq m) (fun y =>
         Creturn (Qle (Qabs (x - y)) epsilon))))
  }.


Definition Ceq (seq1 seq2 : cauchy) : Prop :=
    forall epsilon : Q, epsilon > 0 -> exists N : nat, forall n m : nat, le N n -> le N m ->
     toProp (
     Cbind (proj1_sig seq1 n) (fun x => Cbind (proj1_sig seq2 m) (fun y =>
     Creturn (Qle (Qabs (x - y)) epsilon)))).

Definition Clt (seq1 seq2 : cauchy) : Prop :=
  exists N : nat, forall n m : nat, le N n -> le N m ->
     Cbind (proj1_sig seq1 n) (fun x => Cbind (proj1_sig seq2 m) (fun y =>
     Creturn (Qle x  y)))
     = Creturn True.

Require Import PeanoNat.
Require Import Nat.

Definition Cplus1 (seq1 seq2 : cauchy) : cauchy.
  refine (exist _ (fun n => CQplus (proj1_sig seq1 n) (proj1_sig seq2 n)) _).
  intros.
Abort.


Definition Cplus (seq1 seq2 : cauchy) : cauchy.
  refine (exist _ (fun n => Cbind (proj1_sig seq1 n) (fun x =>
                            Cbind (proj1_sig seq2 n) (fun y =>
                            Creturn (Qplus x y)))) _).
  intros.
  pose (halfe := Qdiv epsilon 2).
  assert (halfe > 0) as Hh. {
    apply Qmult_lt_0_compat.
    - assumption.
    - apply Qinv_lt_0_compat.
      repeat constructor.
  }
  Check (proj2_sig seq2).
  Check (proj2_sig seq2 halfe Hh).
  destruct (proj2_sig seq1 halfe Hh) as [N1 p1].
  destruct (proj2_sig seq2 halfe Hh) as [N2 p2].
  exists (max N1 N2).
  intros.
  Check ClassicalInd.



  (*Check (proj2_sig seq1 epsilon H).
  destruct (proj2_sig seq1 epsilon H) as [N cauchyfact1].
  specialize (cauchyfact1 n m).*)
  specialize (p1 n m (Nat.max_lub_l _ _ _ H0) (Nat.max_lub_l _ _ _ H1)).
  specialize (p2 n m (Nat.max_lub_r _ _ _ H0) (Nat.max_lub_r _ _ _ H1)).
  asreturn2 (proj1_sig seq1 n).
  asreturn2 (proj1_sig seq2 n).
  asreturn2 (proj1_sig seq1 m).
  asreturn2 (proj1_sig seq2 m).
  repeat rewrite bindDef in *.
  apply toPropRet1 in p2, p1.
  pbind p1.
  pbind p2.
  apply toPropRet.
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
                           Cbind (proj1_sig x n) (fun qx =>
                           Cbind (proj1_sig y n) (fun qy =>
                           Creturn (Qeq qx qy)))))
  : Ceq x y.
Proof.
  unfold Ceq.
  intros.

  destruct (proj2_sig x epsilon H0) as [N1 p1].
  destruct (proj2_sig y epsilon H0) as [N2 p2].
  exists (max N1 N2).
  
  intros.
  specialize (p1 n m (Nat.max_lub_l _ _ _ H1) (Nat.max_lub_l _ _ _ H2)).
  specialize (p2 n m (Nat.max_lub_r _ _ _ H1) (Nat.max_lub_r _ _ _ H2)).

  assert (premise1 := H n).
  assert (premise2 := H m).
  clear H.
  
  asreturn2 (proj1_sig x n).
  asreturn2 (proj1_sig y m).
  asreturn2 (proj1_sig x m).
  asreturn2 (proj1_sig y n).
  repeat rewrite bindDef in *.
  apply toPropRet1 in premise1, premise2, p1, p2.
  pbind premise1.
  pbind premise2.
  pbind p1.
  pbind p2.
  apply toPropRet.
  apply Preturn.

  assert ((x0 - x1) == (x0 - x2)). {
    field_simplify.
    apply Qplus_inj_l.
    apply Qmult_inj_l.
    - intros p.
      inversion p.
    - apply Qeq_sym.
      assumption.
  }
  rewrite H.
  assumption.
Qed.
  
(* I need to set things up so that this can just trivially work out to Qplus_comm *)
Theorem Cplus_comm : forall x y, Ceq (Cplus x y) (Cplus y x).
Proof.
  intros.
  unfold Ceq.
  intros.

  destruct (proj2_sig (Cplus x y) epsilon H) as [N1 p1].
  destruct (proj2_sig (Cplus y x) epsilon H) as [N2 p2].
  exists (max N1 N2).
  
  intros.
  specialize (p1 n m (Nat.max_lub_l _ _ _ H0) (Nat.max_lub_l _ _ _ H1)).
  specialize (p2 n m (Nat.max_lub_r _ _ _ H0) (Nat.max_lub_r _ _ _ H1)).

  asreturn2 (proj1_sig (Cplus x y) n).
  asreturn2 (proj1_sig (Cplus y x) n).
  asreturn2 (proj1_sig (Cplus x y) m).
  asreturn2 (proj1_sig (Cplus y x) m).
  repeat rewrite bindDef in *.
  apply toPropRet.
  apply toPropRet1 in p1, p2.
  pbind p1.
  pbind p2.
  apply Preturn.
  Search Qabs Qle.
  apply Qabs_Qle_condition.
  apply Qabs_Qle_condition in p1, p2.
  destruct p1, p2.
  split.
  - eapply Qle_trans.
    apply H2.
    apply p2.
(*
Definition Cmap2 (T : Type) (f : Q -> Q -> Q) (seq1 seq2 : cauchy) : cauchy.
  refine (exist _ (fun n => Cbind (proj1_sig seq1 n) (fun x =>
                            Cbind (proj1_sig seq2 n) (fun y =>
                            Creturn (f x y)))) _).
  intros.
*)
