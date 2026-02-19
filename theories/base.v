Require Import Coq.Logic.ProofIrrelevance.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Require Import util.

(* Double Negation Monad *)
Definition PClassical (P : Prop) : Prop := not (not P).
Notation "[ T ]" := (PClassical T).

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

(* this is equivalent to the usual definition of stable propositions, under the assumption
 of propositional extentionality, which we are using in this development. *)
Definition CProp : Type := {P : Prop | exists P', P = PClassical P'}.

Definition isTrue (P : CProp) : Prop := proj1_sig P.

Definition toCProp (P : Prop) : CProp.
  refine (exist _ (PClassical P) _).
  exists P.
  reflexivity.
Defined.

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

(* The nonconstructivity monad, that represents a unique thing that exists non-constructively *)
Definition Classical (A : Type) : Type :=
  {S : A -> CProp | PClassical (exists a, isTrue (S a))
                    /\ forall x y, isTrue (S x) /\ isTrue (S y) -> PClassical (x = y)}.
Notation "[[| T |]]" := (Classical T).

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
    destruct fx as [SB [existenceB uniqueB]].
    apply (Pbind existenceB).
    intros [b SBb].
    apply Preturn.
    exists b.
    apply Preturn.
    exists x.
    split; auto.
    rewrite <- Heqfx.
    simpl.
    apply SBb.
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

Theorem monadlaw1 : forall A B (a : A) (f : A -> Classical B),
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

Theorem all_classical_return T (t : Classical T)
  : PClassical (exists x, Creturn x = t /\ (isTrue (proj1_sig t x))).
Proof.
  destruct t as [St [nonempty same]].
  apply (Pbind nonempty); intros [a ta].
  apply Preturn.
  exists a.
  split.
  - apply sigEq2.
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

Theorem ind : forall (A : Type)
                     (Q : Classical A -> Prop)
                     (S : A -> CProp) nonempty unique,
    (forall t, isTrue (S t) -> [Q (Creturn t)])
    -> PClassical (Q (exist _ S (conj nonempty unique))).
Proof.
  intros.
  apply (Pbind (all_classical_return _ (exist _ S (conj nonempty unique)))).
  simpl.
  intros [St [eq PSt]].
  rewrite <- eq.
  clear eq.
  apply (Pbind nonempty); clear nonempty; intros [t Pt].
  specialize (H _ Pt).
  apply (Pbind H); clear H; intros H.
  specialize (unique _ _ (conj Pt PSt)).
  pbind unique.
  subst.
  apply Preturn.
  assumption.
Qed.

(* This theorem is false if we used Prop instead of CProp *)
Theorem removedneq (T : Type) (t1 t2 : Classical T) (eq : PClassical (t1 = t2)) : t1 = t2.
Proof.
  apply sigEq2.
  destruct t1, t2.
  simpl.
  assert (PClassical (x = x0)). {
    pbind eq.
    apply (@f_equal _ _ (@proj1_sig _ _)) in eq.
    simpl in eq.
    apply Preturn.
    assumption.
  }
  clear a a0 eq.
  extensionality t.
  apply CProp_Ext.
  - intros.
    apply unwrap.
    pbind H.
    subst.
    apply Preturn.
    assumption.
  - intros.
    apply unwrap.
    pbind H.
    subst.
    apply Preturn.
    assumption.
Qed.

Definition toProp (p : Classical Prop) : Prop :=
  PClassical (p = Creturn True).

Theorem toPropRet : forall P, toProp (Creturn P) <-> PClassical P.
Proof.
  intros.
  split.
  - intros.
    pbind H.
    apply (@f_equal _ _ (@proj1_sig _ _)) in H.
    simpl in H.
    apply (@f_equal _ _ (fun f => f True)) in H.
    assert (isTrue (toCProp (True = True))). {
      simpl.
      apply Preturn.
      reflexivity.
    }
    rewrite <- H in H0.
    simpl in H0.
    pbind H0.
    subst.
    apply Preturn.
    constructor.
  - intros.
    unfold toProp.
    pbind H.
    apply Preturn.
    apply sigEq2.
    simpl.
    extensionality y.
    apply CProp_Ext.
    + intros.
      simpl in *.
      pbind H0.
      subst.
      apply Preturn.
      apply propositional_extensionality.
      split; auto.
    + intros.
      simpl in *.
      pbind H0.
      apply Preturn.
      subst.
      apply propositional_extensionality.
      split; auto.
Qed.

Theorem toPropRetEq : forall P, toProp (Creturn P) = PClassical P.
Proof.
  intros.
  apply propositional_extensionality.
  apply toPropRet.
Qed.

Theorem toPropRet1 : forall P, toProp (Creturn P) -> PClassical P.
Proof.
  apply toPropRet.
Qed.

Theorem toPropRet2 : forall P, PClassical P -> toProp (Creturn P).
Proof.
  apply toPropRet.
Qed.

Theorem toPropRetNot : forall P, ~ (Creturn P = Creturn True) -> ~P.
Proof.
  intros P H p.
  apply H.
  apply f_equal.
  apply propositional_extensionality.
  split; auto.
Qed.

(* a tactic to make applying the induction principle more convenient *)
Ltac classical_induction H :=
  let H2 := fresh "H2" in
  let eq := fresh "eq" in
  let new := fresh "x" in
  let Px := fresh "Px" in
  pose (H2 := all_classical_return _ H);
  pbind H2;
  specialize H2 as [new [eq _]];
  rewrite <- eq in *;
  clear eq.

Theorem monadlaw3 {A B C : Type} {m : Classical A} {g : A -> Classical B} {h : B -> Classical C}
  : (Cbind (Cbind m g) h) = Cbind m (fun x => Cbind (g x) h).
Proof. 
    intros.
  apply sigEq2.
  simpl.
  extensionality c.
  apply CProp_Ext.
    - intros.
      simpl in *.
      pbind H.
      specialize H as [b [athing hbc]].
      pbind athing.
      specialize athing as [a [ma gab]].
      apply Preturn.
      exists a.
      split.
      + assumption.
      + apply Preturn.
        exists b.
        split; assumption.
    - intros.
      simpl in *.
      pbind H.
      specialize H as [a [mb hbc]].
      pbind hbc.
      specialize hbc as [b [gba hac]].
      apply Preturn.
      exists b.
      split.
      + apply Preturn.
        exists a.
        split; assumption.
      + assumption.
Qed.

Definition Pif {T : Type} (P : Prop) (b1 b2 : T) : Classical T.
  refine (exist _ (fun b => toCProp (P /\ b = b1 \/ ~P /\ b = b2)) _).
  split.
  - apply (Pbind (Plem P)); intros pornotp.
    apply Preturn.
    destruct pornotp.
    + exists b1.
      simpl.
      apply Preturn.
      auto.
    + exists b2.
      simpl.
      apply Preturn.
      auto.
  - intros.
    destruct H.
    simpl in *.
    pbind H.
    pbind H0.
    apply Preturn.
    destruct H; destruct H0;
      destruct H; destruct H0;
      subst; auto; contradiction.
Defined.

Theorem PifDef1 {T : Type} (P : Prop) (b1 b2 : T) (p : P) : Pif P b1 b2 = Creturn b1.
Proof.
  intros.
  apply sigEq2.
  simpl.
  extensionality b.
  apply CProp_Ext;
    intros;
    simpl in *;
    pbind H;
    repeat destruct H; auto;
    subst;
    apply Preturn;
    auto.
Qed.

Theorem PifDef2 {T : Type} (P : Prop) (b1 b2 : T) (p : ~ P) : Pif P b1 b2 = Creturn b2.
Proof.
  intros.
  apply sigEq2.
  simpl.
  extensionality b.
  apply CProp_Ext.
  - intros.
    simpl in *.
    pbind H.
    destruct H.
    + destruct H.
      contradiction.
    + destruct H.
      apply Preturn.
      assumption.
  - intros.
    simpl in *.
    pbind H.
    apply Preturn.
    apply or_intror.
    auto.
Qed.

(* the tactic described in section 6 of the paper *)
Ltac classical_auto :=
  repeat first [
      match goal with
      | H : toProp (Creturn ?rest) |- _ => apply toPropRet1 in H
      | H : PClassical ?something |- PClassical ?something_else => pbind H
      | H : Creturn ?something <> Creturn True |- _ => apply toPropRetNot in H
      end
    | apply toPropRet2
    | rewrite monadlaw1 in *
    | rewrite toPropRetEq in *
    | simpl (isTrue (toCProp _)) in *].

Theorem classical_consistent : [False] -> False.
Proof.
  auto.
Qed.

Theorem eqLem (P : Prop) : [P = [P]].
Proof.
  apply (Pbind (Plem P)).
  intros PornotP.
  destruct PornotP.
  - apply Preturn.
    apply propositional_extensionality.
    split.
    + intros _ np.
      auto.
    + auto.
  - apply Preturn.
    apply propositional_extensionality.
    split.
    + intros.
      apply Preturn.
      assumption.
    + intros.
      contradiction.
Qed.

Theorem extra_monad_exists (A : Type) (B : A -> Prop)
  : [exists (a : A), B a] = [exists (a : A), [B a]].
Proof.
  apply propositional_extensionality.
  split.
  - intros.
    classical_auto.
    apply Preturn.
    destruct H.
    exists x.
    apply Preturn.
    assumption.
  - intros.
    classical_auto.
    destruct H.
    classical_auto.
    apply Preturn.
    exists x.
    assumption.
Qed.

Theorem not_forall_2 (T : Type) (P : T -> Prop) (Q : forall t, P t -> Prop)
        (F : ~forall t (p : P t), [Q t p])
  : [exists t, exists (p : P t), ~Q t p].
Proof.
  intros E.
  apply F.
  intros t p nq.
  apply E.
  eauto.
Qed.

(* The whole point of using CProp instead of Prop is to get this theorem *)
Theorem unwrap_eq (T : Type) (x y : [[|T|]]) (eq : [x = y]) : x = y.
Proof.
  apply sigEq2.
  destruct x, y.
  simpl.
  assert [x = x0]. {
    pbind eq.
    apply (@f_equal _ _ (@proj1_sig _ _)) in eq.
    simpl in eq.
    apply Preturn.
    assumption.
  }
  clear a a0 eq.
  extensionality t.
  apply CProp_Ext.
  - intros.
    apply unwrap.
    classical_auto.
    subst.
    apply Preturn.
    assumption.
  - intros.
    apply unwrap.
    classical_auto.
    apply Preturn.
    subst.
    assumption.
Qed.

(* This version remembers the knowledge of what the predicate was *)
Ltac classical_induction_full H :=
  let H2 := fresh "H2" in
  let eq := fresh "eq" in
  let new := fresh "x" in
  let Px := fresh "Px" in
  let defining_pred := fresh "defining_pred" in
  pose (H2 := all_classical_return _ H);
  pbind H2;
  specialize H2 as [new [eq defining_pred]];
  revert defining_pred;
  try rewrite <- eq in * |-;
  try intro defining_pred;
  rewrite <- eq;
  clear eq.

(* This is a more general version of Pif that gets access to P (or not P) in the branches *)
Definition Pif' {T : Type} (P : Prop) (b1 : P -> T) (b2 : ~P -> T) : Classical T.
  refine (exist _ (fun b => toCProp ({p : P | b = b1 p} \/ {np : ~P | b = b2 np})) _).
  split.
  - apply (Pbind (Plem P)); intros pornotp.
    apply Preturn.
    destruct pornotp.
    + exists (b1 H).
      simpl.
      apply Preturn.
      apply or_introl.
      Print sig.
      refine (exist _ H eq_refl).
    + exists (b2 H).
      simpl.
      apply Preturn.
      apply or_intror.
      refine (exist _ H eq_refl).
  - intros.
    destruct H.
    simpl in *.
    pbind H.
    pbind H0.
    apply Preturn.
    destruct H; destruct H0;
      destruct H; destruct H0;
      subst; auto;
      try contradiction; apply f_equal; apply proof_irrelevance.
Defined.

Theorem Pif'Def1 {T : Type} (P : Prop) (b1 : P -> T) (b2 : ~P -> T) (p : P)
  : Pif' P b1 b2 = Creturn (b1 p).
Proof.
  intros.
  apply sigEq2.
  simpl.
  extensionality b.
  apply CProp_Ext.
  - intros.
    classical_auto.
    destruct H.
    + destruct H.
      subst.
      apply Preturn.
      apply f_equal.
      apply proof_irrelevance.
    + destruct H.
      contradiction.
  - intros.
    classical_auto.
    subst.
    apply Preturn.
    apply or_introl.
    refine (exist _ p eq_refl).
Qed.

Theorem Pif'Def2 {T : Type} (P : Prop) (b1 : P -> T) (b2 : ~P -> T) (p : ~ P)
  : Pif' P b1 b2 = Creturn (b2 p).
Proof.
  intros.
  apply sigEq2.
  simpl.
  extensionality b.
  apply CProp_Ext.
  - intros.
    simpl in *.
    pbind H.
    destruct H.
    + destruct H.
      contradiction.
    + destruct H.
      apply Preturn.
      subst.
      apply f_equal.
      apply proof_irrelevance.
  - intros.
    simpl in *.
    pbind H.
    apply Preturn.
    apply or_intror.
    refine (exist _ p _).
    assumption.
Qed.
