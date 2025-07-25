Require Import Coq.Logic.ProofIrrelevance.
(* Instead of using SProp, for now I'll just use the proof irrelevance axiom.
   I'll see if this causes any issues; probably not. *)
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

(*
In this versin of the monad for choice, I'm going to try making a special type of propositions that
are all in the double negation monad.
Following specialprop.agda
 *)

Definition PClassical (P : Prop) : Prop := not (not P).

Definition Preturn {A : Prop} (x : A) : PClassical A.
Proof.
  intro na.
  apply na.
  apply x.
Qed.

Theorem Pbind {A B : Prop} (pa : PClassical A) (f : A -> PClassical B) : PClassical B.
  Proof.
  unfold PClassical in *.
  intros nb.
  apply pa.
  intro a.
  apply f.
  - apply a.
  - apply nb.
Qed.

Ltac pbind H := apply (Pbind H); clear H; intros H.

Definition CProp : Type := {P : Prop | exists P', P = PClassical P'}. 

Definition isTrue (P : CProp) : Prop := proj1_sig P.

Definition toCProp (P : Prop) : CProp.
  refine (exist _ (PClassical P) _).
  exists P.
  reflexivity.
Defined.

Theorem sigEq :
  forall A P S1 S2 p1 p2,
    S1 = S2 -> @eq {a : A | P a} (exist _ S1 p1) (exist _ S2 p2).
Proof.
  intros.
  subst S1.
  assert (p1 = p2).
  apply proof_irrelevance.
  subst p1.
  reflexivity.
Qed.

Theorem sigEq2:
  forall A P (x y : {a : A | P a}), proj1_sig x = proj1_sig y -> x = y.
Proof.
  intros.
  destruct x.
  destruct y.
  simpl in H.
  apply sigEq.
  assumption.
Qed.

Theorem CProp_Ext {P Q : CProp} (f : isTrue P -> isTrue Q) (g : isTrue Q -> isTrue P)
  : P = Q.
Proof.
  destruct P, Q.
  simpl in *.
  apply sigEq2.
  simpl.
  apply propositional_extensionality.
  split; assumption.
Qed.

Theorem unwrap {T : CProp} (H : PClassical (isTrue T)) : isTrue T.
Proof.
  destruct T.
  simpl in *.
  destruct e.
  subst.
  intros p.
  apply H.
  intros q.
  apply q in p.
  assumption.
Qed.

Theorem Plem (P : Prop) : PClassical (P \/ ~P).
Proof.
  intros n.
  apply n.
  apply or_intror.
  intros p.
  apply n.
  apply or_introl.
  apply p.
Qed.

(* The "Unique" monad, that represents a unique thing that exists non-constructively *)
Definition Classical (A : Type) : Type :=
  {S : A -> CProp | PClassical (exists a, isTrue (S a))
                    /\ forall x y, isTrue (S x) /\ isTrue (S y) -> PClassical (x = y)}.

Definition Creturn {A : Type} (x : A) : Classical A.
  refine (exist _ (fun y => toCProp (y = x)) _).
  split.
  - apply Preturn.
    exists x.
    simpl.
    apply Preturn.
    reflexivity.
  - intros.
    destruct H.
    simpl in *.
    apply (Pbind H); clear H; intros H.
    apply (Pbind H0); clear H0; intros H0.
    apply Preturn.
    subst.
    reflexivity.
Defined.

(* TODO: Confirm that the output really has to be in PClassical. *)
Theorem CreturnInj : forall A (x y : A), Creturn x = Creturn y -> PClassical (x = y).
Proof.
  intros.
  pose (@f_equal _ _ (@proj1_sig _ _) _ _ H) as fact.
  simpl in fact.
  assert (isTrue ((fun y => (toCProp (y = x))) x)). {
    apply Preturn.
    reflexivity.
  }
  rewrite fact in H0.
  assumption.
Qed.

Definition Cbind {A B : Type} (pa : Classical A) (f : A -> Classical B) : Classical B.
  refine (exist _ (fun b => toCProp
                              (exists a, isTrue (proj1_sig pa a) /\ isTrue (proj1_sig (f a) b))) _).
  destruct pa as [Sa [nonempty same]].
  simpl.
  split.
  - apply (Pbind nonempty).
    intros.
    simpl.
    destruct H.
    remember (f x) as fx.
    destruct fx as [x0 [p sfsdfd]].
    apply (Pbind p).
    intros.
    apply Preturn.
    destruct H0.
    exists x1.
    apply Preturn.
    exists x.
    split; auto.
    rewrite <- Heqfx.
    simpl.
    assumption.
  - intros x y [allx ally].
    apply (Pbind allx); clear allx; intros [ax [Saax fax]].
    apply (Pbind ally); clear ally; intros [ay [Saay fay]].
    specialize (same _ _ (conj Saax Saay)).
    apply (Pbind same); clear same; intro same.
    subst.
    apply (Pbind (proj2 (proj2_sig (f ay)) _ _ (conj fax fay))).
    intros.
    subst.
    apply Preturn.
    reflexivity.
Defined.

(* one of the monad laws *)
Theorem bindDef : forall A B (a : A) (f : A -> Classical B),
    Cbind (Creturn a) f = f a.
Proof.
  intros.
  apply sigEq2.
  simpl.
  extensionality b.
  apply CProp_Ext.
  - intros.
    simpl in H.
    apply unwrap.
    Check Pbind.
    apply (Pbind H); clear H; intros H.
    destruct H.
    destruct H.
    apply (Pbind H); clear H; intros H.
    subst.
    apply Preturn.
    assumption.
  - intros.
    simpl.
    apply Preturn.
    exists a.
    split.
    + apply Preturn.
      reflexivity.
    + assumption.
Qed.

Theorem monadlaw2 (T : Type) (t : Classical T) : Cbind t Creturn = t.
Proof.
  apply sigEq2.
  extensionality x.
  simpl.
  apply CProp_Ext.
  - intros.
    simpl in *.
    apply unwrap.
    apply (Pbind H); clear H; intros H.
    destruct H as [a [ta p]].
    apply (Pbind p); clear p; intros p.
    subst.
    apply Preturn.
    assumption.
  - intros.
    simpl in *.
    apply Preturn.
    exists x.
    split; auto.
    apply Preturn.
    reflexivity.
Qed.

(* Can I get this for this version? *)
Theorem ClassicalInd T (t : Classical T)
  : PClassical (exists x, Creturn x = t /\ (isTrue (proj1_sig t x))).
Proof.
  destruct t as [St [nonempty same]].
  apply (Pbind nonempty); intros [a ta].
  apply Preturn.
  exists a.
  split.
  - 
    apply sigEq2.
    simpl.
    extensionality t.
    apply CProp_Ext.
    + simpl.
      intros.
      apply unwrap.
      apply (Pbind H); clear H; intros H.
      subst.
      apply Preturn.
      assumption.
    + intros.
      simpl.
      specialize (same _ _ (conj ta H)).
      apply (Pbind same); clear same; intros same.
      subst.
      apply Preturn.
      reflexivity.
  - simpl.
    assumption.
Qed.

(* unique choice *)
Definition choose (T : Type) (P : T -> Prop)
           (nonempty : PClassical (exists t, P t))
           (unique : forall x y, P x /\ P y -> PClassical (x = y))
  : Classical T.
  refine (exist _ (fun t => toCProp (P t)) _).
  split.
  - simpl.
    apply (Pbind nonempty); clear nonempty; intros [t Pt].
    apply Preturn.
    exists t.
    apply Preturn.
    assumption.
  - intros x y [Px Py].
    simpl in *.
    apply (Pbind Px); clear Px; intros Px.
    apply (Pbind Py); clear Py; intros Py.
    specialize (unique _ _ (conj Px Py)).
    assumption.
Defined.

Theorem choiceInd : forall (T : Type) (P : T -> Prop) (Q : Classical T -> Prop)
                            nonempty unique,
    (forall t, P t -> PClassical (Q (Creturn t)))
    -> PClassical (Q (@choose T P nonempty unique)).
Proof.
  intros.
  apply (Pbind (ClassicalInd _ (choose T P nonempty unique))).
  simpl.
  intros [St [eq PSt]].
  rewrite <- eq.
  clear eq.
  apply (Pbind nonempty); clear nonempty; intros [t Pt].
  specialize (H _ Pt).
  apply (Pbind H); clear H; intros H.
  pbind PSt.
  specialize (unique _ _ (conj Pt PSt)).
  pbind unique.
  subst.
  apply Preturn.
  assumption.
Qed.


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
      apply Preturn.
      reflexivity.
    + destruct whiley.
      exists b.
      assumption.
    + destruct whilex.
      exists b.
      assumption.
    + apply Preturn.
      reflexivity.
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
