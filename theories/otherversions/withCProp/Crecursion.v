Require Import Cbase.
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
  refine (choose _ (fun ob => (exists b, ob = Some b /\ runProgR def p b)
                              \/
                                (ob = None /\ ~ exists b, runProgR def p b)) _ _).
  - apply (Pbind (Plem (exists b, runProgR def p b))).
    intros H.
    apply Preturn.
    destruct H as [[b r] | nr].
    + exists (Some b).
      apply or_introl.
      exists b.
      auto.
    + exists None.
      apply or_intror.
      auto.
  - intros x y [H1 H2].
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
  Check choiceInd.
  apply unwrap_eq.
  apply (choiceInd _ _ (fun x => x = Creturn (Some b))).
  intros ob H.
  apply Preturn.
  destruct ob.
  - destruct H.
    + destruct H.
      destruct H.
      inversion H.
      subst.
      inversion H0.
      subst.
      reflexivity.
    + destruct H.
      inversion H.
  - destruct H.
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
  asreturn3 (runProgImpl def (Rec A B a rest)).
  asreturn3 (runProgImpl def (def a)).
  classical_auto.
  simpl in defining_pred, defining_pred0.
  classical_auto.

  destruct defining_pred0.
  - destruct H as [b [eq rundefab]].
    subst.
    asreturn3 (runProgImpl def (rest b)).
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
