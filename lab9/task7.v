Load lab9strongInduction.

Require Import ZArith.

Section equalRecurrences.

Fixpoint pow2( n : nat ) : Z :=
match n with 
  | 0   => 1%Z
  | S m => (2 * (pow2 m))%Z
end.

Fixpoint f (n : nat) : Z :=
match n with
  | 0 => 0%Z
  | 1 => 0%Z
  | 2 => 1%Z
  | 3 => 3%Z
  | S (S (S (S m)) as p) => (2 * (f p) + (pow2 (S m)) - (f m))%Z
end.

Fixpoint g (n : nat) : Z :=
match n with
  | 0 => 0%Z
  | 1 => 0%Z
  | 2 => 1%Z
  | S (S (S m as p) as q) => ((g q) + (g p) + (g m) + (pow2 p))%Z 
end.

Theorem equal_f_g : forall n : nat, f(n) = g(n).
Proof.
  induction n using strong_induction.

  (* Base Case P(0) *)
   destruct n.
   simpl.
   reflexivity.
  
  (* Base Case P(1) *)
   destruct n.
   simpl.
   reflexivity.

  (* Base Case P(2) *)
   destruct n.
   simpl.
   reflexivity.

   (* Base Case P(3) *)
   destruct n.
   simpl.
   reflexivity.

   assert ( n < S (S (S (S n))) ).
   auto.
   apply H in H0.

   (* Inductive Step *)
   change (f (S (S (S (S n))))) with (((2 * f (S (S (S n)))) + (pow2 (S n)) - (f n))%Z).
   change (g (S (S (S (S n))))) with (((g (S (S (S n)))) + (g (S (S n))) + (g (S n)) + (pow2 (S (S n))))%Z).
   change (pow2 (S (S n))) with ((2*pow2((S n)))%Z).

   rewrite H0.
   assert ( S (S (S n)) < S (S (S (S n))) ).
   auto.
   apply H in H1.

   rewrite H1.
   change (g (S (S (S n)))) with (((g (S (S n))) + (g (S n)) + (g n) + (pow2 (S n)))%Z).
   ring_simplify.
   reflexivity.
  
Qed.
















