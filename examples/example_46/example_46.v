Require Foo.Foo.

Module Export Top_DOT_Foo_DOT_Foo_DOT_Baz.
  Module Export Foo.
    Module Export Foo.
      Module Baz.
        Axiom B : Set.
      End Baz.
    End Foo.
  End Foo.
End Top_DOT_Foo_DOT_Foo_DOT_Baz.

Import Foo.Foo.

Fail Check A -> Foo.Foo.Baz.B.
