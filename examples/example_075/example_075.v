From Ltac2 Require Import Ltac2.
Fixpoint seq (start len : nat) : list nat :=
  match len with
  | 0 => nil
  | S len0 => cons start (seq (S start) len0)
  end.
Check I.
Ltac2 big n := Array.length (Array.make n 'I).

Time Ltac2 Eval big 1000000000.
