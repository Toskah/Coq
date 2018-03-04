Require Import Ensembles. 
Require Import Coq.Setoids.Setoid.

Variable U : Type.

Theorem distri_and_over_or : forall p q r : Prop, (p /\ (q \/ r)) <-> ((p /\ q) \/ (p /\ r)).

Proof.
intros.
split.
intro.
destruct H as (H0,H1).
destruct H1 as [H3|H3].
left.
split.
assumption.
assumption.
right.
split.
assumption.
assumption.

intro.
destruct H as [H4|H4].
split.
destruct H4 as (H5,H6).
assumption.
left.
destruct H4 as (H5,H6).
assumption.

split.
destruct H4 as (H5,H6).
assumption.
right.
destruct H4 as (H5,H6).
assumption.
Qed.

Theorem IntersectionToAnd : forall A B : Ensemble U, forall x : U,
   In U (Intersection U A B) x <-> (In U A x) /\ (In U B x).
Proof.
intros.
split.
intro.
destruct H.
split.
assumption.
assumption.
intro.
destruct H.
split.
assumption.
assumption.
Qed.

Theorem UnionToOr : forall A B : Ensemble U, forall x : U,
   In U (Union U A B) x <-> (In U A x) \/ (In U B x).

Proof.
intros.
split.
intro.
destruct H.
left.
assumption.
right.
assumption.
intro.
destruct H.
left.
assumption.
right.
assumption.
Qed.


Theorem SetDistri : forall A B C : Ensemble U,
             Intersection U A (Union U B C) =
             Union U (Intersection U A B) (Intersection U A C). 
Proof.
intros.
apply Extensionality_Ensembles.

split.

intro. intro.
destruct H.
right.
apply IntersectionToAnd.
split.
assumption.
apply UnionToOr in H0.
destruct H0 as [H1|H2].
assumption.


(* to be completed *)

Qed.

Variable A : Ensemble U.
Variable B : nat -> (Ensemble U).

Fixpoint unionB (n : nat) : Ensemble U :=
  match n with
  | 0   => B 0
  | S m => Union U (unionB m) (B (S m))
  end.

Fixpoint intersectionAB (n : nat) : Ensemble U :=
  match n with
  | 0   => Intersection U A (B 0) 
  | S m => Union U (intersectionAB m) (Intersection U A (B (S m)))
  end.

Theorem generalizedSetDistri :
        forall n : nat, intersectionAB n = Intersection U A (unionB n).
Proof.
(* to be completed *)
Qed.
Require Import Ensembles. 
Require Import Coq.Setoids.Setoid.

Variable U : Type.

Theorem distri_and_over_or : forall p q r : Prop, (p /\ (q \/ r)) <-> ((p /\ q) \/ (p /\ r)).

Proof.
intros.
split.
intro.
destruct H as (H0,H1).
destruct H1 as [H3|H3].
left.
split.
assumption.
assumption.
right.
split.
assumption.
assumption.

intro.
destruct H as [H4|H4].
split.
destruct H4 as (H5,H6).
assumption.
left.
destruct H4 as (H5,H6).
assumption.

split.
destruct H4 as (H5,H6).
assumption.
right.
destruct H4 as (H5,H6).
assumption.
Qed.

Theorem IntersectionToAnd : forall A B : Ensemble U, forall x : U,
   In U (Intersection U A B) x <-> (In U A x) /\ (In U B x).
Proof.
intros.
split.
intro.
destruct H.
split.
assumption.
assumption.
intro.
destruct H.
split.
assumption.
assumption.
Qed.

Theorem UnionToOr : forall A B : Ensemble U, forall x : U,
   In U (Union U A B) x <-> (In U A x) \/ (In U B x).

Proof.
intros.
split.
intro.
destruct H.
left.
assumption.
right.
assumption.
intro.
destruct H.
left.
assumption.
right.
assumption.
Qed.


Theorem SetDistri : forall A B C : Ensemble U,
             Intersection U A (Union U B C) =
             Union U (Intersection U A B) (Intersection U A C). 
Proof.
intros.
apply Extensionality_Ensembles.

split.

intro. intro.
destruct H.
right.
apply IntersectionToAnd.
split.
<<<<<<< HEAD
destruct H.
assumption.
destruct H.


=======
assumption.
apply UnionToOr in H0.
destruct H0 as [H1|H2].
assumption.
>>>>>>> d90c2ec79cb4b5ffc81a6904dafb9aa7294a6c79


(* to be completed *)

Qed.

Variable A : Ensemble U.
Variable B : nat -> (Ensemble U).

Fixpoint unionB (n : nat) : Ensemble U :=
  match n with
  | 0   => B 0
  | S m => Union U (unionB m) (B (S m))
  end.

Fixpoint intersectionAB (n : nat) : Ensemble U :=
  match n with
  | 0   => Intersection U A (B 0) 
  | S m => Union U (intersectionAB m) (Intersection U A (B (S m)))
  end.

Theorem generalizedSetDistri :
        forall n : nat, intersectionAB n = Intersection U A (unionB n).
Proof.
(* to be completed *)
Qed.

