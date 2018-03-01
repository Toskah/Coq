Load lab5_task1.

Require Import Coq.omega.Omega. 

Fixpoint size (pair : nat*nat) := 
   match pair with
    | (a,b) => plus a b
   end.

Function computeCD (pair : nat*nat) {measure size pair} :=  
  match pair with
  | (a,b) => if      beq_nat b 0 then Divisors  ( Z.of_nat a)
             else if beq_nat a 0 then Divisors  ( Z.of_nat b)
             else if leb     b a then computeCD ((a-b)%nat,b)
             else                     computeCD ((b-a)%nat,a)
  end.
intros.
unfold size.
apply leb_complete in teq2.
apply beq_nat_false in teq0.
omega.
intros.
unfold size.
apply beq_nat_false in teq1.
apply leb_iff_conv in teq2.
omega.
Defined.


Eval compute in computeCD (24,16)%nat.
Eval compute in computeCD (144,48)%nat.
Eval compute in computeCD (144,688)%nat.
Eval compute in computeCD (1147,899)%nat.


Theorem CDcomputeCorrect : forall p : nat*nat, computeCD p = CD (Z.of_nat (fst p)) (Z.of_nat (snd p)).

Proof.

  intros.
  functional induction (computeCD p) using computeCD_ind.

- apply beq_nat_true in e0.
  rewrite e0.
  simpl.
  rewrite CD0.
  reflexivity.

- simpl.
  apply beq_nat_true in e1.
  rewrite e1.
  rewrite CDsymmetric.
  rewrite CD0.
  reflexivity.

- simpl.
  rewrite IHe.
  simpl.
  apply leb_complete in e2.  
  assert (Z.of_nat (a-b) = (Z.of_nat a) - (Z.of_nat b)).
  apply Nat2Z.inj_sub.
  assumption.
  rewrite H.
  rewrite <- CDsubtract.
  reflexivity.

- simpl.
  apply leb_complete_conv in e2.
  rewrite CDsymmetric.
  rewrite CDsubtract.
  rewrite IHe.
  simpl.
  assert (Z.of_nat (b-a) = (Z.of_nat b) - (Z.of_nat a)).
  apply Nat2Z.inj_sub.
  omega.
  rewrite H.
  reflexivity.

Qed.
