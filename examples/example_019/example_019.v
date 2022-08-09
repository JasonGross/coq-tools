Lemma foo : forall _ : Type, Type.
Proof (fun x => x).

Inductive x := .

Goal x.
  lazymatch goal with |- x => fail end.
