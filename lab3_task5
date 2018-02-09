Require Import Arith.
Section task5.

Fixpoint sum3 (n : nat) : nat :=
  match n with
  | 0   => 0
  | S n => (sum3 n) + (n+1)*(n+2)*(n+3)
  end.

Theorem sum3Formula : forall n : nat, 4 * (sum3 n) = n*(n+1)*(n+2)*(n+3).

Proof.
induction n.
ring_simplify.
reflexivity.

change (sum3 (S n)) with ((sum3 n) + (n+1)*(n+2)*(n+3)).
ring_simplify.
rewrite IHn.
ring_simplify.
reflexivity.
Qed.