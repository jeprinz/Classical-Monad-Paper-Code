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
     Cbind (seq n) (fun x => Cbind (seq m) (fun y =>
     Creturn (Qle (Qabs (x - y)) epsilon)))
     = Creturn True
  }.


Definition Ceq (seq1 seq2 : cauchy) : Prop :=
    forall epsilon : Q, epsilon > 0 -> exists N : nat, forall n m : nat, le N n -> le N m ->
     Cbind (proj1_sig seq1 n) (fun x => Cbind (proj1_sig seq2 m) (fun y =>
     Creturn (Qle (Qabs (x - y)) epsilon)))
     = Creturn True.

Definition Clt (seq1 seq2 : cauchy) : Prop :=
  exists N : nat, forall n m : nat, le N n -> le N m ->
     Cbind (proj1_sig seq1 n) (fun x => Cbind (proj1_sig seq2 m) (fun y =>
     Creturn (Qle x  y)))
     = Creturn True.

Require Import PeanoNat.
Require Import Nat.

Definition Cplus1 (T : Type) (seq1 seq2 : cauchy) : cauchy.
  refine (exist _ (fun n => CQplus (proj1_sig seq1 n) (proj1_sig seq2 n)) _).
  intros.
Abort.


Definition Cplus (T : Type) (seq1 seq2 : cauchy) : cauchy.
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

  Ltac asreturn2 H :=
  let H2 := fresh "H2" in
  let eq := fresh "eq" in
  let new := fresh "x" in
  pose (H2 := ClassicalInd _ H)(*;
  pbind H2;
  specialize H2 as [new [eq _]];
  subst H*).

  
  asreturn2 (proj1_sig seq1 n).
  pbind H2.
  
(*
Definition Cmap2 (T : Type) (f : Q -> Q -> Q) (seq1 seq2 : cauchy) : cauchy.
  refine (exist _ (fun n => Cbind (proj1_sig seq1 n) (fun x =>
                            Cbind (proj1_sig seq2 n) (fun y =>
                            Creturn (f x y)))) _).
  intros.
*)
