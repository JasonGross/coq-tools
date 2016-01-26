Require Import A.

Definition b_foo
  := A.a_foo.

Definition b_foo' : True.
Proof.
  idtac. (*Fail Timeout 1 repeat pose 1.*)
  exact I.
Qed.
