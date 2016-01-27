Require Import Omega.



Definition a_foo : True.
Proof.
  idtac. (* Fail Timeout 1 repeat pose 1.*)
  exact I.
Qed.
