Require Import Coq.Logic.Classical_Prop.

Lemma npp : forall P, ~~P -> P.
Proof. tauto. Qed.
