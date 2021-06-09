Lemma foo : True.
Proof.
  Open Scope nat_scope.
  exact I.
  Close Scope nat_scope.
Qed.
Fail Check Set.
