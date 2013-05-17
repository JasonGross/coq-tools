Require Import Ensembles.

Lemma foo : forall T, Ensemble T = Ensemble T.
  reflexivity.
Qed.

Definition B : Type.
  refine (_ * _); refine (_ * _); abstract exact True.
Defined.
