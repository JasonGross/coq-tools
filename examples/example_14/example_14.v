(* -*- coq-prog-args: ("-emacs" "-nois" "-impredicative-set") -*- *)
Require Import A.
Check eq_refl : eq v (forall x : Prop, x).
