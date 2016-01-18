Require Import C B.
Require Export A.


Definition foo := C.foo.

Definition foo' : True.
Proof.
  idtac. (*Fail Timeout 1 repeat pose 1.*)
  exact I.
Qed.
