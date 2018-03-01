
Require Import ZArith.
Require Import Ensembles. 
Require Import Recdef.
Open    Scope  Z_scope.

Section commondivisors.

Definition divide a b := exists k, b = k*a.

Notation "( a | b )" := (divide a b).

Inductive Divisors( a : Z ) : Ensemble Z := 
   DivisorConstructor : forall d : Z, (d | a) -> (In Z (Divisors a) d).

Inductive CD (a b : Z) : Ensemble Z :=
   CDconstructor: forall d : Z,  (((d | a) /\ (d | b)) -> (In Z (CD a b) d)).

Theorem CD0 : forall a : Z, (CD a 0) = Divisors a.
Proof.
   intro.
   apply Extensionality_Ensembles.  
   split.

   
   split.
   destruct H.
   apply H.
   
   split.
   split.
   destruct H.
  
   assumption.
   exists 0.
   reflexivity.
   
   
   
   (* complete the proof using tactics
      intro, split, destruct, assumption, exists, reflexivity *)

Qed.

Theorem CDsymmetric : forall a b : Z, (CD a b) = (CD b a).
Proof.
   intros.
   apply Extensionality_Ensembles.
  
   split. 
   split. 
   destruct H.
   split.
   destruct H.
   assumption.
   destruct H.
   assumption.
   
   split. 
   destruct H.
   split. 
   destruct H.
   assumption.

   destruct H.
   assumption.
   (* complete the proof using tactics
      intro, split, destruct, assumption *)

Qed.
   
Theorem CDsubtract : forall a b : Z, (CD a b) = (CD (a-b) b).   
Proof.

   intros.
   apply Extensionality_Ensembles.
   split. 
   intro.
   split. 
   constructor.
   destruct H.
   destruct H.
   destruct H.
   destruct H0.

   exists (x-x0).
   ring_simplify.
   rewrite H.
   rewrite H0.
   reflexivity.
   destruct H.
   destruct H.
   assumption. 
   intro.
   intro.
   constructor.
   split.
   destruct H.
   destruct H.
   destruct H.
   destruct H0.
   exists (x + x0).
   ring_simplify.
   rewrite  <- H.
   rewrite <- H0.
   ring_simplify.
   ring_simplify.
   reflexivity.
   destruct H.
   destruct H.
   assumption.
   
   (* complete the proof using tactics
      intro, split, destruct, assumption, exists, 
      constructor, ring_simplify, rewrite, reflexivity *)

Qed.
