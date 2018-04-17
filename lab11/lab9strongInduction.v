
Require Import Arith.
Section strong_induction.

Theorem induction1:
 forall P : nat -> Prop,
 (forall n : nat, 
    (forall k : nat, (k < n -> P k)) -> (forall k : nat, (k <= n -> P k)))
 -> (forall n : nat, (forall k : nat, (k <= n -> P k))).

Proof.

induction n.
intro.
apply H.
intro.
intro.

unfold lt in H0.
inversion H0.

apply H.
intro.
intro.
apply IHn.

unfold lt in H0.
apply le_S_n in H0.
assumption.

Qed.


Theorem strong_induction:
 forall P : nat -> Prop,
 (forall n : nat, 
   (forall k : nat, (k < n -> P k)) -> P n)
 -> (forall n : nat, P n).

Proof.

intro.
intro.

assert ( forall n:nat, (forall k:nat, k < n -> P k) -> 
                       (forall k:nat, k <= n -> P k) ).
intro.
intro.
intro.
intro.

inversion H1.
apply H.
assumption.

apply H0.
rewrite <- H3.
unfold lt.
apply le_n_S.
assumption.


assert( forall n : nat, (forall k : nat, (k <= n -> P k)) ).

apply induction1.
assumption.

intro.

assert (forall k:nat, k <= n -> P k).
apply H1.

apply H2.

constructor.


Qed.




