
Require Import Ensembles.

Variable U : Type.

Variable C : Ensemble U.
  
Theorem IntersectSetmius : forall B1 B2 : Ensemble U,
             Intersection U (Setminus U B1 C) (Setminus U B2 C) =
             Setminus U (Intersection U B1 B2) C. 
Proof.
intros.
apply Extensionality_Ensembles.

(* to be completed *)
split.
split.
split.
destruct H.
destruct H.
assumption.
destruct H.
destruct H0.
assumption.
destruct H.
destruct H.
assumption.
split.
split.
destruct H.
destruct H.
assumption.
destruct H.
destruct H.
assumption.
split.
destruct H.
destruct H.
assumption.
destruct H.
assumption.

Qed.

Variable B : nat -> (Ensemble U).

Fixpoint intersectionB (n : nat) : Ensemble U :=
  match n with
  | 0   => B 0
  | S m => Intersection U (intersectionB m) (B (S m))
  end.

Fixpoint intersectionBC (n : nat) : Ensemble U :=
  match n with
  | 0   => Setminus U (B 0) C 
  | S m => Intersection U (intersectionBC m) (Setminus U (B (S m)) C)
  end.

Theorem generalizedIntersectionSetminus :
        forall n : nat, intersectionBC n = Setminus U (intersectionB n) C.
Proof.
induction n.
apply Extensionality_Ensembles.
split.
split.
destruct H.
assumption.
destruct H.
assumption.

split.
destruct H.
assumption.
destruct H.
assumption.
change (intersectionBC (S n)) with ( Intersection U (intersectionBC n) (Setminus U (B (S n)) C)).
rewrite IHn.
apply IntersectSetmius.

(* to be completed *)

Qed.

Require Import Ensembles.




  
Theorem IntersectSetminusAlt : forall B1 B2 : Ensemble U,
             Intersection U (Setminus U C B1) (Setminus U C B2) =
             Setminus U C (Union U B1 B2). 
Proof.
intros.
apply Extensionality_Ensembles.
split.
split.
destruct H.
destruct H.
assumption.
destruct H.

(* to be completed *)

Qed.

Variable B : nat -> (Ensemble U).

Fixpoint unionB (n : nat) : Ensemble U :=
  match n with
  | 0   => B 0
  | S m => Union U (unionB m) (B (S m))
  end.

Fixpoint intersectionCB (n : nat) : Ensemble U :=
  match n with
  | 0   => Setminus U C (B 0) 
  | S m => Intersection U (intersectionCB m) (Setminus U C (B (S m)))
  end.

Theorem generalizedIntersectionSetminusAlt :
        forall n : nat, intersectionCB n = Setminus U C (unionB n).
Proof.
induction n.
apply Extensionality_Ensembles.

(* to be completed *)

Qed.




        