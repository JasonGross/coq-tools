Require Import Ensembles.


Lemma foo : forall T, Ensemble T = Ensemble T.
  reflexivity.
Qed.







Definition B : Type.
  refine (_ * _)%type; refine (_ * _)%type; abstract exact True.
Defined.
