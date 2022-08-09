Require Import Top.A.

Goal True.
  Fail Check A.b.
  pose A.a; fail 0 "A.a exists".
