Require Foo.A.
Definition SET := O.
Definition SET2 := SET.
Import Foo.A.
Definition b := let test := SET2 : nat in Foo.A.a : SET.
