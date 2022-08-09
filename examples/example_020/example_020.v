Lemma foo : forall _ : Type, Type.
Proof (fun x => x).

Inductive x := .

Goal x.
  fail.
