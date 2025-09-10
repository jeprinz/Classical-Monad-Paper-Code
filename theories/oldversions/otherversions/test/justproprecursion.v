Require Import justprop.

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
