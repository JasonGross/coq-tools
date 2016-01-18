Require Import Omega.



Definition foo : True.
Proof.
  idtac. (* Fail Timeout 1 repeat pose 1.*)
  exact I.
Qed.
