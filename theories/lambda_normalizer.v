Require Import recursion.
Require Import base.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Nat.

(*
in this file, i demonstrate that you can write a lambda calculus normalizer using
the nonconstructivity monad.
 *)

Inductive Term : Type :=
| lam : Term -> Term
| app : Term -> Term -> Term
| var : nat -> Term.

Fixpoint lift : nat -> Term -> Term :=
  fun k t =>
    match t with
    | lam t' => lam (lift (S k) t')
    | app t1 t2 => app (lift k t1) (lift k t2)
    | var i => if (Nat.ltb i k)
               then var i
               else var (S i)
    end.

Fixpoint subst : nat -> Term -> Term -> Term :=
  fun k toSub t =>
    match t with
    | lam t' => lam (subst (S k) (lift 0 toSub) t')
    | app t1 t2 => app (subst k toSub t1) (subst k toSub t2)
    | var i => if Nat.ltb k i
               then var (pred i)
               else if Nat.eqb i k
                    then toSub
                    else var i
    end.

(*this is the general recursive function that normalizes lambda calculus terms.*)
Definition normalize_prog (t : Term) : Prog Term Term :=
  match t with
  | lam t1 => Rec _ _ t1 (fun t1' => Ret _ _ (lam t1'))
  | app t1 t2 => Rec _ _ t1 (fun t1' =>
                 Rec _ _ t2 (fun t2' =>
                 match t1' with
                 | lam body => Rec _ _ (subst 0 t2' body) (Ret _ _)
                 | _ => Ret _ _ (app t1' t2')
                 end))
  | var i => Ret _ _ (var i)
  end.
Definition normalize : Term -> [[|option Term|]] := runProg normalize_prog.

(*we can run the normalize function, but only up to propositional equality.*)

(* (\x. x) (\x. x) = \x. x *)
Goal normalize (app (lam (var 0)) (lam (var 0))) = Creturn (Some (lam (var 0))).
Proof.
  unfold normalize, runProg, normalize_prog.
  repeat (simpl; rewrite ?runProgDefinitionRec, ?runProgDefinitionRet, ?monadlaw1).
  reflexivity.
Qed.

Definition zero := lam (lam (var 0)).
Definition succ := lam (lam (lam (app (var 1) (app (app (var 2) (var 1)) (var 0))))).
Definition plus := lam (lam (app (app (var 1) succ) (app (app (var 1) succ) zero))).


(* 2 + 2 = 4 *)
Goal normalize (app (app plus (app succ (app succ zero))) (app succ (app succ zero)))
     = normalize (app succ (app succ (app succ (app succ zero)))).
Proof.
  unfold normalize, runProg, normalize_prog, succ, zero, plus.
  (* takes ~10 seconds to run *)
  repeat (simpl; rewrite ?runProgDefinitionRec, ?runProgDefinitionRet, ?monadlaw1).
  reflexivity.
Qed.
