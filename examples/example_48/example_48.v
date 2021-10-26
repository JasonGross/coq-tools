(* -*- coq-prog-args: ("-emacs" "-noinit" "-R" "." "Top") -*- *)
Require Import Top.Foo.
Require Import Coq.Init.Ltac.
Monomorphic Inductive True := I.
Monomorphic Inductive eq {A} (x : A) : forall _ : A, Prop := eq_refl : eq x x.
Arguments eq_refl {A x} , [A] x.
Definition foo@{} : Set. Proof. refine True. Defined.
Check let f := (fun _ : foo => (eq_refl Set : eq Foo.foo@{Set} Set)) in f : forall _ : Set, _.
