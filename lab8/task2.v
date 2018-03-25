Require Import Coq.omega.Omega.
Inductive seq : Type :=
| empty : seq
| pair  : nat -> seq -> seq.
(* lexicographical ordering less than or equal <= *)
Fixpoint lessOrEq (s t: seq) : Prop :=
match s with
| empty     => True
| pair a s1 => match t  with
| empty     => False
| pair b t1 =>  (a < b) \/
((a = b) /\ (lessOrEq s1 t1))
end
end.
Lemma test1 : not (lessOrEq (pair 4 (pair 3 empty))
(pair 3 empty)).
Proof.

intro.
destruct H.
omega.
destruct H.
contradiction.

Qed.
Lemma test2 : lessOrEq (pair 4 (pair 3 empty))
(pair 4 (pair 3 (pair 2 empty))).
Proof.

simpl.
intuition.

Qed.