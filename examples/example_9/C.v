Require Import A.

Definition foo
  := A.foo.

Definition foo' : True.
Proof.
  idtac. (*Fail Timeout 1 repeat pose 1.*)
  exact I.
Qed.
