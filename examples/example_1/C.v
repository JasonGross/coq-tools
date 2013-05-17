Require Import A B.
Require Import Bool.

Axiom bar : True.

Definition baz : A = B.
  apply proof_irrelevance.
