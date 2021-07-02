Require Foo.A.
Definition SET : nat := O.
Definition SET2 := SET.
Import Foo.A.
Definition b : SET := let test := SET2 : nat in Foo.A.a.
