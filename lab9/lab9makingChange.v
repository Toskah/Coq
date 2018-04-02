
Load lab9strongInduction.

Section makingChange.

Theorem change : forall n:nat, exists p q : nat, n+8 = 3*p + 5*q.

Proof.

induction n using strong_induction.

(* Base Case: P 0 *)
destruct n.
exists 1.
exists 1.
simpl.
reflexivity.

(* Base Case: P 1 *)
destruct n.
exists 3.
exists 0.
simpl.
reflexivity.

(* Base Case: P 2 *)
destruct n.
exists 0.
exists 2.
simpl.
reflexivity.

(* generate a specific hypothesis when k is set to n *)
assert( n < S (S (S n)) ).
auto.            (* tactic automation; try a collection of tactics *)
apply H in H0.             

(* Induction Step *)
destruct H0 as (x,H0).
destruct H0 as (y,H0).
exists (1+x).
exists y.

ring_simplify.
rewrite <- H0.
ring_simplify.
reflexivity.

Qed.
