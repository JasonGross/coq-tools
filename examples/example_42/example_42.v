Require Import Foo.B Foo.C.
(* N.B. Consider replacing this with the example of
https://github.com/JasonGross/coq-tools/issues/16, since the issue
with [congruence] may go away, and all we really want to test here is
that the python code for un-inlinable modules runs fine *)

Definition bar := Eval unfold foo in foo.

Check (bar, npp, Foo.A.a) : Set.
