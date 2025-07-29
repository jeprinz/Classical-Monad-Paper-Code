Require Import base.

Inductive whileR {A B : Type} (step : A -> A + B) : A -> B -> Prop :=
| while_base : forall a b, step a = inr b -> whileR step a b
| while_step : forall a a' b, step a = inl a'
                              -> whileR step a' b
                              -> whileR step a b
.

Theorem whileRFunction : forall A B step a b1 b2,
    @whileR A B step a b1 
    -> @whileR A B step a b2
    -> b1 = b2.
Proof.
  intros.
  induction H; inversion H0.
  - rewrite H in H1.
    inversion H1.
    subst.
    reflexivity.
  - rewrite H in H1.
    inversion H1.
  - rewrite H in H2.
    inversion H2.
  - rewrite H in H2.
    inversion H2.
    subst.
    specialize (IHwhileR H3).
    subst.
    reflexivity.
Qed.

Definition Partial (T : Type) : Type := Classical (option T).

Definition while {A B : Type} (a : A) (step : A -> A + B) : Partial B.
  refine (choose _ (fun ob => match ob with
                              | None => ~ exists b, whileR step a b
                              | Some b => whileR step a b
                              end) _ _).
  - apply (Pbind (Plem (exists b, whileR step a b))); intros.
    destruct H.
    + destruct H.
      apply Preturn.
      exists (Some x).
      assumption.
    + apply Preturn.
      exists None.
      assumption.
  - intros x y [whilex whiley].
    destruct x, y.
    + rewrite (whileRFunction _ _ _ _ _ _ whilex whiley).
      reflexivity.
    + destruct whiley.
      exists b.
      assumption.
    + destruct whilex.
      exists b.
      assumption.
    + reflexivity.
Defined.

Theorem whileBase (A B : Type) step (a : A) (b : B)
        (H : step a = inr b)
  : PClassical (while a step = Creturn (Some b)).
Proof.
  apply (choiceInd (option B) _ (fun c => c = Creturn (Some b))).
  intros.
  apply while_base in H.
  destruct t.
  - rewrite (whileRFunction _ _ _ _ _ _ H H0).
    apply Preturn.
    reflexivity.
  - destruct H0.
    exists b.
    assumption.
Qed.

Theorem whileStep (A B : Type) step (a a' : A)
        (H : step a = inl a')
  : PClassical (@while A B a step = while a' step).
Proof.
  apply choiceInd.
  intros.
  apply (choiceInd _ _ (fun c => c = Creturn t)).
  intros.
  destruct t, t0.
  - rewrite (whileRFunction _ _ _ _ _ _ (while_step _ _ _ _ H H0) H1).
    apply Preturn.
    reflexivity.
  - destruct H1.
    exists b.
    apply (while_step _ _ _ _ H H0).
  - destruct H0.
    exists b.
    destruct H1.
    + rewrite H in H0.
      inversion H0.
    + rewrite H in H0.
      inversion H0.
      subst.
      assumption.
  - apply Preturn.
    reflexivity.
Qed.

(************************************************************************************)

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
      reflexivity.
Defined.

Definition runProg {A B : Type} (def : A -> Prog A B) (a : A) : Classical (option B) :=
  runProgImpl def (def a).

Theorem runProgDefinitionRet {A B : Type} (def : A -> Prog A B) (b : B)
  : PClassical (runProgImpl def (Ret _ _ b) = Creturn (Some b)).
Proof.
  Check choiceInd.
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

Definition bind {A B : Type} (a : option A) (f : A -> option B) : option B.
Admitted.

(* I probably need a monad transormer? *)

Theorem runProgDefinitionRec {A B : Type} (def : A -> Prog A B) (a : A)
        (rest : B -> Prog A B)
  : PClassical (runProgImpl def (Rec _ _ a rest) =
                  Cbind (runProgImpl def (def a)) (fun ob =>
                  bind ob (fun b =>
                  Cbind 
               (*runProgImpl def (rest b))).*)
