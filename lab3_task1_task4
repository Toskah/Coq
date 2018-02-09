Section Lab3Task1.
Variable D : Set.
Theorem Lab3Task1a : forall A B : D -> Prop,
(forall x, A x -> B x) -> ((forall x, A x) -> (forall x, B x)).
Proof.
(* to be completed *)
intros.
apply H.
apply H0.
Qed.


Theorem Lab3Task1b : forall A B : D -> Prop,
(forall x, A x -> B x) -> ((exists x, A x) -> (exists x, B x)).
Proof.
(* to be completed *)
intros.
destruct H0.
apply H in H0.
exists x.
assumption.
Qed.


Variable d:D. (* D is not empty *)
Theorem Lab3Task1c : forall A B : D -> Prop,
(forall x, A x -> B x) -> ((forall x, A x) -> (exists x, B x)).
Proof.
intros.
exists d.
apply H.
apply H0.
Qed.

Section Lab3Task2.
Require Import Arith.

Fixpoint sumOdd (n : nat) : nat :=
match n with
| 0 => 0
| S n => (sumOdd n) + (2*n + 1)
end.
Theorem sumOdds : forall n : nat, sumOdd n = n*n.

Proof.
induction n.
reflexivity. 
change (sumOdd(S n)) with (sumOdd(n) + (2*n +1)).
ring_simplify.
rewrite IHn.
reflexivity.
Qed.


Require Import Arith.
Section Task3.
Fixpoint sum2 (n : nat) : nat :=
match n with
| 0 => 0
| S n => (sum2 n) + (n+1)*(n+2)
end.
Theorem sum2formula : forall n : nat, 3 * (sum2 n) = n*(n+1)*(n+2).

Proof.

induction n.
ring_simplify.
reflexivity.
change (sum2 (S n)) with ((sum2 n) + ( n+1)*(n+2)).
ring_simplify.
rewrite IHn.
ring_simplify.
reflexivity.
Qed.

Section Task4.
Fixpoint sum3 (n : nat) : nat :=
match n with
| 0 => n
| S n => (sum3 n) + ((n+1)*(n+1))
end.
Theorem squareSumFormula : forall n : nat, 6 * (sum3 n) = n*(n+1)*(2*n+1).

induction n.
ring_simplify.
reflexivity.

change (sum3(S n)) with ((sum3 n) + ((n+1)*(n+1))).
ring_simplify.
rewrite IHn.
ring_simplify.
reflexivity.
Qed.






