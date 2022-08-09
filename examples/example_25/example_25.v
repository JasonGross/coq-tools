Definition bar : nat. exact 2. Defined.
Definition baz := Eval unfold bar in bar.
Fail Definition foo := 1 + baz.
