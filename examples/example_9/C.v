Require Import A.

Definition c_foo
  := A.a_foo.

Definition c_foo' : True.
Proof.
  idtac. (*Fail Timeout 1 repeat pose 1.*)
  exact I.
Qed.
