Require Import base.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Inductive Prog (A B : Type) : Type :=
| Ret : B -> Prog A B
| Rec : A -> (B -> Prog A B) -> Prog A B.

Inductive runProgR {A B : Type} (def : A -> Prog A B) : Prog A B -> B -> Prop :=
| retR : forall b, runProgR def (Ret _ _ b) b
| recR : forall a b1 b2 rest,
    runProgR def (def a) b1
    -> runProgR def (rest b1) b2
    -> runProgR def (Rec _ _ a rest) b2.

Theorem runProgFunction {A B : Type} {def : A -> Prog A B} {p : Prog A B} {b1 b2 : B}
        (rp1 : runProgR def p b1) (rp2 : runProgR def p b2) : b1 = b2.
Proof.
  intros.
  generalize dependent b2.
  induction rp1.
  - intros.
    inversion rp2.
    reflexivity.
  - intros.
    inversion rp2.
    subst.
    specialize (IHrp1_1 _ H1).
    subst.
    specialize (IHrp1_2 _ H3).
    subst.
    reflexivity.
Qed.

Definition runProgImpl {A B : Type} (def : A -> Prog A B) (p : Prog A B) : Classical (option B).
  refine (exist _ (fun ob => toCProp ((exists b, ob = Some b /\ runProgR def p b)
                              \/
                                (ob = None /\ ~ exists b, runProgR def p b))) _).
  split.
  - apply (Pbind (Plem (exists b, runProgR def p b))).
    intros H.
    apply Preturn.
    destruct H as [[b r] | nr].
    + exists (Some b).
      classical_auto.
      apply Preturn.
      apply or_introl.
      exists b.
      auto.
    + exists None.
      classical_auto.
      apply Preturn.
      apply or_intror.
      auto.
  - intros x y [H1 H2].
    classical_auto.
    destruct H1, H2.
    + destruct H as [b1 [p1 r1]].
      destruct H0 as [b2 [p2 r2]].
      subst.
      apply Preturn.
      apply f_equal.
      apply (runProgFunction r1 r2).
    + destruct H as [b1 [p1 r1]].
      destruct H0 as [p2 r2].
      destruct r2.
      exists b1.
      assumption.
    + destruct H0 as [b1 [p1 r1]].
      destruct H as [p2 r2].
      destruct r2.
      exists b1.
      assumption.
    + destruct H, H0.
      subst.
      apply Preturn.
      reflexivity.
Defined.

Definition runProg {A B : Type} (def : A -> Prog A B) (a : A) : Classical (option B) :=
  runProgImpl def (def a).

Theorem runProgDefinitionRet {A B : Type} (def : A -> Prog A B) (b : B)
  : runProgImpl def (Ret _ _ b) = Creturn (Some b).
Proof.
  apply unwrap_eq.
  classical_induction_full (runProgImpl def (Ret A B b)).
  simpl in defining_pred.
  classical_auto.
  apply Preturn.
  destruct x.
  - destruct defining_pred.
    + destruct H.
      destruct H.
      inversion H.
      subst.
      inversion H0.
      subst.
      reflexivity.
    + destruct H.
      inversion H.
  - destruct defining_pred.
    + destruct H.
      destruct H.
      inversion H.
    + destruct H.
      destruct H0.
      exists b.
      constructor.
Qed.

Theorem runProgDefinitionRec {A B : Type} (def : A -> Prog A B) (a : A)
        (rest : B -> Prog A B)
  : (runProgImpl def (Rec _ _ a rest)
    =
    Cbind (runProgImpl def (def a)) (fun ob =>
    match ob with
    | Some b => runProgImpl def (rest b)
    | None => Creturn None
    end)).
Proof.
  apply unwrap_eq.
  classical_induction_full (runProgImpl def (Rec A B a rest)).
  classical_induction_full (runProgImpl def (def a)).
  classical_auto.
  simpl in defining_pred, defining_pred0.
  classical_auto.

  destruct defining_pred0.
  - destruct H as [b [eq rundefab]].
    subst.
    classical_induction_full (runProgImpl def (rest b)).
    simpl in *.
    classical_auto.
    destruct defining_pred, defining_pred0.
    + destruct H as [b1 [eq1 runb]].
      destruct H0 as [b2 [eq2 runb0]].
      subst.
      apply Preturn.
      apply f_equal.
      apply f_equal.
      Print runProgR.
      apply (recR _ _ _ _ _ rundefab) in runb0.
      apply (runProgFunction runb runb0).
    + destruct H as [b1 [eq1 runb]].
      inversion runb.
      destruct H0.
      destruct H5.
      exists b1.
      rewrite (runProgFunction rundefab H2) in *.
      assumption.
    + destruct H as [eq bad].
      destruct H0 as [b0 [eq2 runb0]].
      destruct bad.
      exists b0.
      eapply recR.
      * apply rundefab.
      * assumption.
    + destruct H, H0.
      subst.
      apply Preturn.
      reflexivity.
  - destruct defining_pred.
    + destruct H0.
      destruct H0.
      destruct H.
      subst.
      inversion H1.
      destruct H2.
      eexists.
      apply H3.
    + destruct H, H0.
      subst.
      apply Preturn.
      reflexivity.
Qed.

Require Import Nat.

(*
This is the function

Fixpoint collatz (n : nat) : nat :=
  if eqb n 1 then 0 else
    1 + collatz (if eqb (modulo n 2) 0
                 then (n / 2)
                 else (n * 3) + 1).
*)

Definition collatz_prog (n : nat) : Prog nat nat :=
  if eqb n 1 then Ret _ _ 0 else
    Rec _ _ (if (eqb (modulo n 2) 0)
             then n / 2
             else (3 * n) + 1)
        (fun res => Ret _ _ (1 + res)).

Definition collatz : nat -> [[|option nat|]] :=
  runProg collatz_prog.

Goal collatz 6 = Creturn (Some 8).
Proof.
  unfold collatz, runProg, collatz_prog.
  simpl.
  repeat (simpl; rewrite ?runProgDefinitionRec, ?runProgDefinitionRet, ?monadlaw1).
  reflexivity.
Qed.
