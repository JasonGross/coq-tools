Require Import C B.
Require Export A.


Definition d_foo := C.c_foo.

Definition d_foo' : True.
Proof.
  idtac. (*Fail Timeout 1 repeat pose 1.*)
  exact I.
Qed.
