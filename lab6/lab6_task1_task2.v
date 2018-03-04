
Require Import Ensembles.

Variable U : Type.

Variable C : Ensemble U.

(* ------ TASK 1 ------ *)
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


(* ------ TASK 2 ------ *)

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

