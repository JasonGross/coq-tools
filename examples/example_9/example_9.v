Require Import D.

Definition foo' : True.
Proof.
  idtac. (*Fail Timeout 1 repeat pose 1.*)
  exact I.
Qed.

Definition foo
  := D.foo.

Fail Check foo : True.
