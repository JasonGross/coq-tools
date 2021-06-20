Require Import Foo.B Foo.C.

Definition bar := Eval unfold foo in foo.

Check (bar, npp, Foo.A.a) : Set.
