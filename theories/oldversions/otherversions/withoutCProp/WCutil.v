Require Import PropExtensionality. (*this line also imports proof irrelevance*)



Search (_ _ = _ _) -nat.

Theorem f_equal_dep_prop (A B : Type) (P : A -> Prop)
        (f : forall (a : A), P a -> B)
        (a1 a2 : A)
        (p1 : P a1)
        (p2 : P a2)
        (eqa : a1 = a2)
  : f a1 p1 = f a2 p2.
Proof.
  subst.
  apply f_equal.
  apply proof_irrelevance.
Qed.

Print Assumptions f_equal_dep_prop.

(*
Require Import Stdlib.Logic.JMeq.

(* This would require using another axiom! *)
Print Assumptions JMeq_congr.

(* need dep version if possible*)
Theorem JMeq_app (A B : Type) (f1 f2 : A -> B) (a1 a2 : A)
        (eqf : JMeq f1 f2) (eqa : JMeq a1 a2) : JMeq (f1 a1) (f2 a2).
Proof.
  Print JMeq.
  
*)
