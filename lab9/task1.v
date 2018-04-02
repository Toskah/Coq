
Load lab9strongInduction.

Section makingChange.

Theorem change : forall n:nat, exists p q : nat, n+18 = 4*p + 7*q.

Proof.


(*Base Case*)

induction n using strong_induction.
destruct n.
exists 1.
exists 2.
simpl.
reflexivity.


destruct n.
exists 3.
exists 1.
simpl.
reflexivity.

destruct n.
exists 5.
exists 0.
simpl.
reflexivity.

destruct n.
exists 0.
exists 3.
simpl. 
reflexivity.

assert(n < S(S( (S (S n))))).
auto.
apply H in H0.

destruct H0 as (x, H0).
destruct H0 as (y, H0).

exists (1 + x).
exists y.

ring_simplify.
rewrite <- H0.
ring_simplify.
reflexivity.
Qed.