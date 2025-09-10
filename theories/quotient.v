Require Import base.

Require Import Stdlib.Classes.RelationClasses.
Require Import Stdlib.Relations.Relation_Definitions.
Require Import PropExtensionality. (*this line also imports proof irrelevance*)
Require Import FunctionalExtensionality.
Require Import util.

Module Type EqRel.
  Parameter A : Type.
  Parameter R : relation A.
  Parameter Rsym : forall a b, R a b -> R b a.
  Parameter Rtrans : forall a b c, R a b -> R b c -> R a c.
  Parameter Rrefl : forall a, R a a.
End EqRel.

Module Quotient (EqRel : EqRel).

  Import EqRel.

  (* The quotient type *)

  Definition t : Type :=
    {S : A -> CProp |
      (forall x y, isTrue (S x) -> ([R x y] <-> isTrue (S y))) /\ [exists a, isTrue (S a)]}.

  (*TODO: can't I just delete these and use sigEq? *)
  Lemma quotientEq :
    forall S1 S2 p1 p2,
      S1 = S2 -> @eq t (exist _ S1 p1) (exist _ S2 p2).
  Proof.
    intros.
    subst S1.
    assert (p1 = p2).
    apply proof_irrelevance.
    subst p1.
    reflexivity.
  Qed.

  Lemma quotientEq2:
    forall (x y : t), proj1_sig x = proj1_sig y -> x = y.
  Proof.
    intros.
    destruct x.
    destruct y.
    simpl in H.
    apply quotientEq.
    assumption.
  Qed.
  
  Definition mk (a : A) : t.
    refine (exist _ (fun a' => toCProp (R a' a)) _).
    subst.
    split.
    - intros.
      split.
      + intros.
        classical_auto.
        apply Preturn.
        apply Rsym in H0.
        eapply Rtrans.
        apply H0.
        apply H.
      + intros.
        classical_auto.
        apply Preturn.
        eapply Rtrans.
        apply H.
        apply Rsym in H0.
        apply H0.
    - apply Preturn.
      exists a.
      classical_auto.
      apply Preturn.
      apply Rrefl.
  Defined.

  Theorem ind : forall (P : t -> Prop), (forall (a : A), [P (mk a)]) -> forall (q : t), [P q].
  Proof.
    intros.
    remember q as q'.
    destruct q as [S [property aaInS]].
    apply (Pbind aaInS); intros [a aInS].
    assert (q' = (mk a)). {
      subst.
      apply quotientEq.
      extensionality a'.
      apply CProp_Ext.
      - intros.
        classical_auto.
        apply property; assumption.
      - intros.
        specialize (property a a' aInS).
        classical_auto.
        apply property.
        classical_auto.
        apply Preturn.
        apply Rsym.
        apply H0.
    }
    rewrite H0.
    apply H.
  Qed.

  Theorem isMk : forall (x : t), [exists a, x = mk a].
  Proof.
    intros.
    apply (ind (fun t => exists a, t = mk a)).
    intros.
    apply Preturn.
    exists a.
    auto.
  Qed.

  Theorem isMk_extended : forall (q : t), [exists a, q = mk a /\ proj1_sig (proj1_sig q a)].
  Proof.
    intros.
    remember q as q'.
    destruct q as [S [property aaInS]].
    apply (Pbind aaInS); intros [a aInS].
    assert (q' = (mk a)). {
      subst.
      apply quotientEq.
      extensionality a'.
      apply CProp_Ext.
      - intros.
        classical_auto.
        apply property; assumption.
      - intros.
        specialize (property a a' aInS).
        classical_auto.
        apply property.
        classical_auto.
        apply Preturn.
        apply Rsym.
        assumption.
    }
    apply Preturn.
    exists a.
    split.
    - assumption.
    - subst q'.
      simpl.
      assumption.
  Qed.

  Theorem sound : forall a b, R a b -> mk a = mk b.
  Proof.
    intros.
    apply quotientEq2.
    simpl.
    extensionality a'.
    apply CProp_Ext.
    - intros.
      classical_auto.
      apply Preturn.
      eapply Rtrans.
      apply H0.
      apply H.
    - intros.
      classical_auto.
      apply Preturn.
      eapply Rtrans.
      apply H0.
      apply Rsym.
      apply H.
  Qed.

  (* You could maybe get rid of the [] here, if R outputted a CProp? I'm not sure whats ideal. *)
  Theorem complete : forall a b, mk a = mk b -> [R a b].
  Proof.
    intros.
    apply (@f_equal _ _ (@proj1_sig _ _)) in H.
    simpl in H.
    apply (@f_equal _ _ (fun f => f a)) in H.
    apply (@f_equal _ _ (isTrue)) in H.
    simpl in H.
    rewrite <- H.
    apply Preturn.
    apply Rrefl.
  Qed.

  Definition lift {T : Type} (f : A -> Classical T)
             (respects : forall a b, R a b -> f a = f b)
             (x : t) : Classical T.
    refine (exist _ (fun t0 =>
                       toCProp (exists a, isTrue (proj1_sig x a) /\ isTrue (proj1_sig (f a) t0))) _).
    destruct x as [S [SR aSa]].
    simpl.
    split.
    -
      classical_auto.
      specialize aSa as [a Sa].
      remember (f a) as fa.
      destruct fa as [St [tnonempty tunique]].
      simpl in *.
      apply (Pbind tnonempty).
      intros [t Stt].
      apply Preturn.
      exists t.
      intros.
      classical_auto.
      apply Preturn.
      exists a.
      split; auto.
      rewrite <- Heqfa.
      simpl.
      assumption.
    - intros x y [ aSafax a'Sa'fay ].
      classical_auto.
      specialize aSafax as [a [Sa fax]].
      specialize a'Sa'fay as [a' [Sa' fay]].
      (* this is line 162 *)
      destruct (proj2_sig (f a)) as [_ unique].
      specialize (SR a a' Sa).
      apply SR in Sa'.
      classical_auto.
      specialize (respects a a' Sa').
      rewrite <- respects in fay.
      specialize (unique _ _ (conj fax fay)).
      assumption.
  Defined.
  
  Theorem lift_eq : forall {T : Type} (f : A -> Classical T)
                           (respects : forall a b, R a b -> f a = f b)
                           (a : A), lift f respects (mk a) = f a.
  Proof.
    intros.
    apply sigEq2.
    simpl.
    extensionality t0.
    apply CProp_Ext.
    - intros.
      apply unwrap.
      classical_auto.
      destruct H as [a' [Ra'a fa't0]].
      classical_auto.
      specialize (respects a' a Ra'a).
      rewrite respects in fa't0.
      apply Preturn.
      assumption.
    - intros.
      classical_auto.
      apply Preturn.
      exists a.
      split.
      + apply Preturn. apply Rrefl.
      + assumption.
  Qed.
  
  Definition unwrap_quot (x : [[| t |]]) : t.
    specialize x as [S [existence uniqueness]].
    refine (exist _ (fun a => S (mk a)) _).
    split.
    - intros.
      split.
      + intros.
        apply unwrap.
        classical_auto.
        rewrite (sound _ _ H0) in H.
        apply Preturn.
        assumption.
      + intros.
        specialize (uniqueness _ _ (conj H H0)).
        classical_auto.        
        apply complete.
        assumption.
    - classical_auto.
      specialize existence as [x Sx].
      assert (xismk := isMk x).
      classical_auto.
      destruct xismk as [a p].
      subst.
      apply Preturn.
      exists a.
      assumption.
  Defined.

  Theorem unwrapDef (x : t) : unwrap_quot (Creturn x) = x.
  Proof.
    apply sigEq2.
    simpl.
    extensionality a.
    apply CProp_Ext.
    - intros.
      apply unwrap.
      classical_auto.
      subst.
      simpl.
      repeat apply Preturn.
      apply Rrefl.
    - intros.
      classical_auto.
      apply Preturn.
      apply sigEq2.
      simpl.
      extensionality a'.
      apply CProp_Ext.
      + intros.
        classical_auto.
        apply (proj1 (proj2_sig x) _ _ H).
        classical_auto.
        apply Preturn.
        apply Rsym.
        assumption.
      + intros.
        apply (proj1 (proj2_sig x) _ _ H0).
        assumption.
  Qed. (* Surely this proof can be simplified or written in terms of something else? *)

  Check lift.
  Definition lift2 {T : Type} (f : A -> A -> Classical T)
             (respects : forall x y x' y', R x x' -> R y y' -> f x y = f x' y')
             (x y : t) : Classical T.
    refine (lift (fun a => lift (fun b => f a b) _ y) _ x).
    shelve.
    all:revgoals.
    Unshelve.
    - intros.
      apply respects; auto.
      apply Rrefl.
    - intros.
      assert (lift (fun x => f a x) (fun a' b' H' => respects a a' a b' (Rrefl a) H') =
                lift (fun x => f b x) (fun a' b' H' => respects b a' b b' (Rrefl b) H')). {
        apply f_equal_dep_prop.
        extensionality c.
        apply respects; auto.
        apply Rrefl.
      }
      rewrite H0.
      reflexivity.
  Defined.

  Theorem lift2_eq {T : Type} (f : A -> A -> Classical T)
          (respects : forall x y x' y', R x x' -> R y y' -> f x y = f x' y')
          (a b : A) : lift2 f respects (mk a) (mk b) = f a b.
  Proof.
    unfold lift2.
    rewrite lift_eq.
    rewrite lift_eq.
    reflexivity.
  Qed.

  Definition map (f : A -> A)
             (respects : forall x x', R x x' -> R (f x) (f x'))
             (t1 : t): t.
    apply unwrap_quot.
    refine (lift (fun a => Creturn (mk (f a))) _ t1).
    intros.
    apply f_equal.
    apply sound.
    apply respects.
    apply H.
  Defined.

  Theorem map_eq (f : A -> A)
          (respects : forall x x', R x x' -> R (f x) (f x'))
          (a : A) : map f respects (mk a) = mk (f a).
  Proof.
    unfold map.
    rewrite lift_eq.
    rewrite unwrapDef.
    reflexivity.
  Qed.

  Definition map2 (f : A -> A -> A)
             (respects : forall x y x' y', R x x' -> R y y' -> R (f x y) (f x' y'))
             (t1 t2 : t): t.
    apply unwrap_quot.
    refine (lift2 (fun a b => Creturn (mk (f a b))) _ t1 t2).
    intros.
    apply f_equal.
    apply sound.
    apply respects.
    apply H. apply H0.
  Defined.

  Theorem map2_eq (f : A -> A -> A)
          (respects : forall x y x' y', R x x' -> R y y' -> R (f x y) (f x' y'))
          (a b : A) : map2 f respects (mk a) (mk b) = mk (f a b).
  Proof.
    unfold map2.
    rewrite lift2_eq.
    rewrite unwrapDef.
    reflexivity.
  Qed.
  
  Theorem unwrap_eq_quot (x y : t) : [x = y] -> x = y.
  Proof.
    intros eq.
    apply sigEq2.
    destruct x, y.
    simpl.
    assert [x = x0]. {
      classical_auto.
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

  Ltac quot_induction H :=
  let H2 := fresh "H2" in
  let eq := fresh "eq" in
  let new := fresh "x" in
  let Px := fresh "Px" in
  pose (H2 := isMk H);
  pbind H2;
  specialize H2 as [new eq];
  rewrite eq in *;
  clear eq.
End Quotient.
