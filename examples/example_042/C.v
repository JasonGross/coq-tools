From Coq Require Import Classical_Prop.

Lemma npp : forall P, ~~P -> P.
Proof. tauto. Qed.
