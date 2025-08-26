
Theorem and_assoc2 : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
    intros P Q R [HP [HQ HR]].
Admitted.
