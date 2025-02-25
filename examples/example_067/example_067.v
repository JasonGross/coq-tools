Section foo.
    Context (x y : nat) (p q : x = y).
    Lemma silly : True -> x = y.
    Proof. intro; exact p. Qed.
End foo.
Definition bar := @silly 0 0 eq_refl I.
Fail Check bar.