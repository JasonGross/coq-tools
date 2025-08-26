
Section __.
  Context {A : Type}.
Theorem and_assoc2 : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof using.
Admitted.
End __.
Check and_assoc2 : forall P Q R, _ /\ _ -> _ /\ _.