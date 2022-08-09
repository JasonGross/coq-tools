Notation "x ^*" := (S x) (at level 10, only parsing).
Definition foo := (4^*).
(* testing removal of comments now, "comment" "*)" "(*" "(*" "(*" *)
Check (5^*) : Set.
