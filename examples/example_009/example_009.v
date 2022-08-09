Require Import D.

Definition e_foo' : True.
Proof.
  idtac. (*Fail Timeout 1 repeat pose 1.*)
  exact I.
Qed.

Definition e_foo
  := D.d_foo.

Fail Check e_foo : True.
