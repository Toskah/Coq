Require Import Ensembles.

Variable U : Type.

Variable C : Ensemble U.
(*-------- TASK 3 ------*)
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
destruct H.
unfold not.
intro.
destruct H2.
contradiction.
destruct H0.
contradiction.

split.
split.
destruct H.
assumption.
destruct H.
intro.
apply H0.
left.
assumption.

destruct H.
split. 
assumption.
intro.
apply H0.
right.
assumption.


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

(* ------- TASK 4 ------ *)
Theorem generalizedIntersectionSetminusAlt :
        forall n : nat, intersectionCB n = Setminus U C (unionB n).
Proof.
induction n.
apply Extensionality_Ensembles.

split.
split.
destruct H.
assumption.

destruct H.
unfold not.
apply H0.

split.
destruct H.
assumption.

destruct H.
apply H0.

change (intersectionCB (S n)) with (Intersection U (intersectionCB n) (Setminus U C (B (S n)))).
rewrite IHn.
apply IntersectSetminusAlt.


Qed.




        