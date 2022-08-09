Inductive eq {A} (x : A) : forall _ : A, Set := eq_refl : eq x x.
Definition v := ((forall x : Set, eq x x) : Set).
