Definition foo : 1 = 2 -> forall P, ~~P -> P.
Proof.
  intros.
  try tauto. (* no-op, unless Classical_Prop has been Required *)
  congruence.
Defined.

Require Import Foo.A.
Require Import Foo.C.
