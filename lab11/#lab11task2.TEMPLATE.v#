Load lab9strongInduction.
Require Import Coq.omega.Omega.

Fixpoint redeemBars (n : nat) : nat :=
 match n with
 | 0 => 0
 | 1 => 0
 | 2 => 0
 | 3 => 0
 | 4 => 0
 | 5 => 0
 | 6 => 0
 | 7 => 0
 | 8 => 0
 | 9 => 0
 | S(S(S(S(S(S(S(S(S(S n as n'))))))))) => 1 + redeemBars n'
 end.

Eval compute in (redeemBars 9).
Eval compute in (redeemBars 10).
Eval compute in (redeemBars 17).
Eval compute in (redeemBars 18).
Eval compute in (redeemBars 19).
Eval compute in (redeemBars 27).
Eval compute in (redeemBars 28).

Fixpoint div9 (n : nat) : nat :=
 match n with
 | 0 => 0
 | 1 => 0
 | 2 => 0
 | 3 => 0
 | 4 => 0
 | 5 => 0
 | 6 => 0
 | 7 => 0
 | 8 => 0
 | S(S(S(S(S(S(S(S(S n)))))))) => 1 + div9 n
 end.

Theorem result: forall n : nat, redeemBars(S n) = div9 n.
Proof.
induction n using strong_induction.

destruct n.
reflexivity.

destruct n.
reflexivity.

destruct n.
reflexivity.

destruct n.
reflexivity.

destruct n.
reflexivity.

destruct n.
reflexivity.

destruct n.
reflexivity.

destruct n.
reflexivity.

destruct n.
reflexivity.

assert (n < S (S (S (S (S (S (S (S (S n))))))))).
omega.
apply H in H0.

change (redeemBars (S (S (S (S (S (S (S (S (S (S n))))))))))) with (1 + redeemBars (S n)).
change (div9 (S (S (S (S (S (S (S (S (S n)))))))))) with (1 + div9 n).

rewrite H0.
reflexivity.
Qed.
