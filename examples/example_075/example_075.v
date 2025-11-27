Require Import Coq.Lists.List.
Fixpoint seq (start len : nat) : list nat :=
  match len with
  | 0 => nil
  | S len0 => cons start (seq (S start) len0)
  end.
Notation hide := _.
Check I.
Goal True. idtac "File ""./example_075.v"", line 999, characters 0-0:". idtac "Error:". Abort.
Eval cbv in seq 0 (10 * 1000).
